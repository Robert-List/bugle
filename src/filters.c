/*  BuGLe: an OpenGL debugging tool
 *  Copyright (C) 2004-2007, 2009-2010  Bruce Merry
 *
 *  This program is free software; you can redistribute it and/or modify
 *  it under the terms of the GNU General Public License as published by
 *  the Free Software Foundation; version 2.
 *
 *  This program is distributed in the hope that it will be useful,
 *  but WITHOUT ANY WARRANTY; without even the implied warranty of
 *  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 *  GNU General Public License for more details.
 *
 *  You should have received a copy of the GNU General Public License
 *  along with this program; if not, write to the Free Software
 *  Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
 */

#if HAVE_CONFIG_H
# include <config.h>
#endif
#include <stdio.h>
#include <stddef.h>
#include <string.h>
#include <assert.h>
#include <stdlib.h>
#include <math.h>
#include <errno.h>
#include <dlfcn.h>
#include <bugle/memory.h>
#include <bugle/string.h>
#include <bugle/math.h>
#include <bugle/input.h>
#include <bugle/filters.h>
#include <bugle/log.h>
#include <bugle/linkedlist.h>
#include <bugle/hashtable.h>
#include <budgie/types.h>
#include <budgie/reflect.h>
#include <budgie/addresses.h>
#include "budgielib/defines.h"
#include "platform/threads.h"
#include "platform/dl.h"

struct filter_set_s
{
    const char *name;
    const char *help;
    linked_list filters;
    filter_set_loader load;
    filter_set_unloader unload;
    filter_set_activator activate;
    filter_set_deactivator deactivate;
    const filter_set_variable_info *variables;
    bugle_dl_module dl_handle;

    bugle_bool added;         /* Is listed in the config file or is depended upon */
    bugle_bool loaded;        /* Initialisation has been called */
    bugle_bool active;        /* Is actively intercepting events */
};

typedef struct
{
    filter *parent;
    budgie_function function;
    bugle_bool inactive;    /* True if callback should be called even when filterset is inactive */
    filter_callback callback;
} filter_catcher;

typedef struct
{
    filter_set *set;
    bugle_bool active;        /* BUGLE_TRUE for an activation, BUGLE_FALSE for a deactivation */
} filter_set_activation;

static linked_list filter_sets;
static linked_list added_filter_sets; /* Those specified in the config, plus dependents */

/* As the filter-sets are loaded, loaded_filters is populated with
 * the loaded filters in arbitrary order. Once all filter-sets are
 * loaded, the initialisation code calls filter_compute_order
 * to do a topological sort on the filters in loaded_filters. No
 * locking is required because this all happens in the initialisation
 * code.
 *
 * The active_callbacks list contains the list of callback in
 * active filters. Each active_callback list entry points to a
 * filter_catcher in the original filter structure. It is updated by calling
 * compute_active_callbacks, which takes a write lock on
 * active_callbacks_rwlock. The same lock also protects the ->active flag
 * on filter-sets, and the activations_deferred list (see below).
 *
 * If a filter wishes to activate or deactivate a filter-set (its own
 * or another), it should call bugle_filter_set_activate_deferred
 * or bugle_filter_set_deactivate_deferred. This causes the change to
 * happen only after the current call has completed processing (which
 * removes the need to recompute the active filters while processing
 * them), and also prevents a self-deadlock.
 */
static linked_list loaded_filters;

/* FIXME: remove the dependence on defines.h */
static linked_list active_callbacks[FUNCTION_COUNT];
static linked_list activations_deferred;
static bugle_thread_rwlock_t active_callbacks_rwlock;

/* hash tables of linked lists of strings; A is the key, B is the linked list element */
static hash_table filter_orders;           /* A is called after B */
static hash_table filter_set_dependencies; /* A requires B */
static hash_table filter_set_orders;       /* A is initialised after B */

static bugle_dl_module current_dl_handle = NULL;

static object_class *bugle_call_class;

/* Forward declarations */
static void filter_set_deactivate_nolock(filter_set *handle);
static void compute_active_callbacks(void);

/*** Order management helper code ***/

typedef struct
{
    void *f;
    int valence;
} order_data;

static void register_order(hash_table *orders, const char *before, const char *after)
{
    linked_list *deps;
    deps = (linked_list *) bugle_hash_get(orders, after);
    if (!deps)
    {
        deps = BUGLE_MALLOC(linked_list);
        bugle_list_init(deps, bugle_free);
        bugle_hash_set(orders, after, deps);
    }
    bugle_list_append(deps, bugle_strdup(before));
}

/* Returns BUGLE_TRUE on success, BUGLE_FALSE if there was a cycle.
 * - present: linked list of the binary items (not names); it is rewritten
 *   in place on success.
 * - order: name-name ordering dependencies, as a hash table of linked
 *   lists. If B is in A's linked list, then A must come before B.
 * - get_name: maps an item pointer to the name of the item
 */
static bugle_bool compute_order(linked_list *present,
                                hash_table *order,
                                const char *(*get_name)(void *))
{
    linked_list ordered;
    linked_list queue;
    linked_list *deps;
    hash_table byname;  /* maps names to order_data structs */
    const char *name;
    int count = 0;            /* count of outstanding items, to detect cycles */
    linked_list_node *i, *j;
    void *cur;
    order_data *info;

    bugle_list_init(&ordered, NULL);
    bugle_hash_init(&byname, bugle_free);
    for (i = bugle_list_head(present); i; i = bugle_list_next(i))
    {
        count++;
        info = BUGLE_MALLOC(order_data);
        info->f = bugle_list_data(i);
        info->valence = 0;
        bugle_hash_set(&byname, get_name(info->f), info);
    }

    /* fill in valences */
    for (i = bugle_list_head(present); i; i = bugle_list_next(i))
    {
        cur = bugle_list_data(i);
        deps = (linked_list *) bugle_hash_get(order, get_name(cur));
        if (deps)
        {
            for (j = bugle_list_head(deps); j; j = bugle_list_next(j))
            {
                name = (const char *) bugle_list_data(j);
                info = (order_data *) bugle_hash_get(&byname, name);
                if (info) /* otherwise a non-existant object */
                    info->valence++;
            }
        }
    }

    /* prime the queue */
    bugle_list_init(&queue, NULL);
    for (i = bugle_list_head(present); i; i = bugle_list_next(i))
    {
        cur = (filter *) bugle_list_data(i);
        info = (order_data *) bugle_hash_get(&byname, get_name(cur));
        if (info->valence == 0)
            bugle_list_append(&queue, cur);
    }

    /* do a topological walk, starting at the back */
    while (bugle_list_head(&queue))
    {
        count--;
        cur = bugle_list_data(bugle_list_head(&queue));
        bugle_list_erase(&queue, bugle_list_head(&queue));
        deps = (linked_list *) bugle_hash_get(order, get_name(cur));
        if (deps)
        {
            for (j = bugle_list_head(deps); j; j = bugle_list_next(j))
            {
                name = (const char *) bugle_list_data(j);
                info = (order_data *) bugle_hash_get(&byname, name);
                if (info) /* otherwise a non-existent object */
                {
                    info->valence--;
                    if (info->valence == 0)
                        bugle_list_append(&queue, info->f);
                }
            }
        }
        bugle_list_prepend(&ordered, cur);
    }

    /* clean up */
    bugle_list_clear(&queue);
    bugle_hash_clear(&byname);
    if (count > 0)
    {
        bugle_list_clear(&ordered);
        return BUGLE_FALSE;
    }
    else
    {
        void (*destructor)(void *);

        /* Some fiddling to prevent anything from being destroyed while we
         * shuffle the list structures around
         */
        destructor = present->destructor;
        present->destructor = NULL;
        bugle_list_clear(present);
        *present = ordered;
        present->destructor = destructor;
        return BUGLE_TRUE;
    }
}

/*** End of order management helper code ***/

static void filter_free(filter *f)
{
    bugle_list_clear(&f->callbacks);
    bugle_free(f);
}

static void filter_set_free(filter_set *handle)
{
    if (handle->loaded)
    {
        handle->loaded = BUGLE_FALSE;
        filter_set_deactivate_nolock(handle);
        if (handle->unload) (*handle->unload)(handle);

        bugle_list_clear(&handle->filters);
    }
}

static void filters_shutdown(void)
{
    linked_list_node *i;
    filter_set *s;
    budgie_function k;

    bugle_list_clear(&loaded_filters);
    for (k = 0; k < budgie_function_count(); k++)
        bugle_list_clear(&active_callbacks[k]);

    /* NB: this list runs backwards to obtain the correct shutdown order.
     * Don't try to turn it into a list destructor or the shutdown order
     * will be wrong.
     */
    for (i = bugle_list_tail(&added_filter_sets); i; i = bugle_list_prev(i))
    {
        s = (filter_set *) bugle_list_data(i);
        filter_set_free(s);
    }

    bugle_hash_clear(&filter_orders);
    bugle_hash_clear(&filter_set_dependencies);
    bugle_hash_clear(&filter_set_orders);
    bugle_list_clear(&added_filter_sets);
    bugle_list_clear(&filter_sets);
    bugle_object_class_free(bugle_call_class);
}

static void filter_library_init(const char *filename, void *data)
{
    bugle_dl_module handle;
    void (*init)(void);

    handle = bugle_dl_open(filename, 0);
    if (handle == NULL)
    {
        bugle_log_printf("filters", "initialise", BUGLE_LOG_ERROR,
                         "failed to load %s: %s", filename, dlerror());
        return;
    }
    init = (void (*)(void)) bugle_dl_sym_function(handle, "bugle_initialise_filter_library");
    if (init == NULL)
    {
        bugle_log_printf("filters", "initialise", BUGLE_LOG_WARNING,
                         "library %s did not export initialisation symbol",
                         filename);
        return;
    }
    current_dl_handle = handle;
    (*init)();
    current_dl_handle = NULL;
}

static void list_free(void *l)
{
    linked_list *list;

    list = (linked_list *) l;
    if (!list) return;
    bugle_list_clear(list);
    bugle_free(list);
}

void filters_initialise(void)
{
    const char *libdir;
    budgie_function f;

    bugle_thread_rwlock_init(&active_callbacks_rwlock);
    bugle_list_init(&filter_sets, bugle_free);
    bugle_list_init(&added_filter_sets, NULL);
    bugle_list_init(&loaded_filters, NULL);
    for (f = 0; f < budgie_function_count(); f++)
        bugle_list_init(&active_callbacks[f], NULL);
    bugle_list_init(&activations_deferred, bugle_free);
    bugle_hash_init(&filter_orders, list_free);
    bugle_hash_init(&filter_set_dependencies, list_free);
    bugle_hash_init(&filter_set_orders, list_free);
    bugle_call_class = bugle_object_class_new(NULL);

    libdir = getenv("BUGLE_FILTER_DIR");
    if (!libdir) libdir = PKGLIBDIR;

    bugle_dl_foreach(libdir, filter_library_init, NULL);

    atexit(filters_shutdown);
}

bugle_bool filter_set_variable(filter_set *handle, const char *name, const char *value)
{
    const filter_set_variable_info *v;
    bugle_bool bool_value;
    long int_value;
    float float_value;
    char *string_value;
    char *end;
    bugle_input_key key_value;
    void *value_ptr = NULL;

    for (v = handle->variables; v && v->name; v++)
    {
        if (strcmp(name, v->name) == 0)
        {
            switch (v->type)
            {
            case FILTER_SET_VARIABLE_BOOL:
                if (strcmp(value, "1") == 0
                    || strcmp(value, "yes") == 0
                    || strcmp(value, "true") == 0)
                    bool_value = BUGLE_TRUE;
                else if (strcmp(value, "0") == 0
                         || strcmp(value, "no") == 0
                         || strcmp(value, "false") == 0)
                    bool_value = BUGLE_FALSE;
                else
                {
                    bugle_log_printf(handle->name, "initialise", BUGLE_LOG_ERROR,
                                     "Expected 1|0|yes|no|true|false for %s in filter-set %s",
                                     name, handle->name);
                    return BUGLE_FALSE;
                }
                value_ptr = &bool_value;
                break;
            case FILTER_SET_VARIABLE_INT:
            case FILTER_SET_VARIABLE_UINT:
            case FILTER_SET_VARIABLE_POSITIVE_INT:
                errno = 0;
                int_value = strtol(value, &end, 0);
                if (errno || !*value || *end)
                {
                    bugle_log_printf(handle->name, "initialise", BUGLE_LOG_ERROR,
                                     "Expected an integer for %s in filter-set %s",
                                     name, handle->name);
                    return BUGLE_FALSE;
                }
                if (v->type == FILTER_SET_VARIABLE_UINT && int_value < 0)
                {
                    bugle_log_printf(handle->name, "initialise", BUGLE_LOG_ERROR,
                                     "Expected a non-negative integer for %s in filter-set %s",
                                     name, handle->name);
                    return BUGLE_FALSE;
                }
                else if (v->type == FILTER_SET_VARIABLE_POSITIVE_INT && int_value <= 0)
                {
                    bugle_log_printf(handle->name, "initialise", BUGLE_LOG_ERROR,
                                     "Expected a positive integer for %s in filter-set %s",
                                     name, handle->name);
                    return BUGLE_FALSE;
                }
                value_ptr = &int_value;
                break;
            case FILTER_SET_VARIABLE_FLOAT:
                errno = 0;
                float_value = (float) strtod(value, &end);
                if (errno || !*value || *end)
                {
                    bugle_log_printf(handle->name, "initialise", BUGLE_LOG_ERROR,
                                     "Expected a real number for %s in filter-set %s",
                                     name, handle->name);
                    return BUGLE_FALSE;
                }

                if (!bugle_isfinite(float_value))
                {
                    bugle_log_printf(handle->name, "initialise", BUGLE_LOG_ERROR,
                                     "Expected a finite real number for %s in filter-set %s",
                                     name, handle->name);
                    return BUGLE_FALSE;
                }
                value_ptr = &float_value;
                break;
            case FILTER_SET_VARIABLE_STRING:
                string_value = bugle_strdup(value);
                value_ptr = &string_value;
                break;
            case FILTER_SET_VARIABLE_KEY:
                if (!bugle_input_key_lookup(value, &key_value))
                {
                    bugle_log_printf(handle->name, "initialise", BUGLE_LOG_ERROR,
                                     "Unknown key %s for %s in filter-set %s", value, name, handle->name);
                    return BUGLE_FALSE;
                }
                value_ptr = &key_value;
                break;
            case FILTER_SET_VARIABLE_CUSTOM:
                value_ptr = v->value;
                break;
            }
            if (v->callback && !(*v->callback)(v, value, value_ptr))
            {
                if (v->type == FILTER_SET_VARIABLE_STRING)
                    bugle_free(string_value);
                return BUGLE_FALSE;
            }
            else
            {
                if (v->value)
                {
                    switch (v->type)
                    {
                    case FILTER_SET_VARIABLE_BOOL:
                        *(bugle_bool *) v->value = bool_value;
                        break;
                    case FILTER_SET_VARIABLE_INT:
                    case FILTER_SET_VARIABLE_UINT:
                    case FILTER_SET_VARIABLE_POSITIVE_INT:
                        *(long *) v->value = int_value;
                        break;
                    case FILTER_SET_VARIABLE_FLOAT:
                        *(float *) v->value = float_value;
                        break;
                    case FILTER_SET_VARIABLE_STRING:
                        if (*(char **) v->value)
                            bugle_free(*(char **) v->value);
                        *(char **) v->value = string_value;
                        break;
                    case FILTER_SET_VARIABLE_KEY:
                        *(bugle_input_key *) v->value = key_value;
                        break;
                    case FILTER_SET_VARIABLE_CUSTOM:
                        break;
                    }
                }
                return BUGLE_TRUE;
            }
        }
    }
    bugle_log_printf(handle->name, "initialise", BUGLE_LOG_ERROR,
                     "Unknown variable %s in filter-set %s",
                     name, handle->name);
    return BUGLE_FALSE;
}

/* Every function that calls this one must hold active_callbacks_rwlock
 * (or be single-threaded startup code), and must arrange for
 * compute_active_callbacks to be run afterwards.
 */
/* FIXME: deps should also be activated */
static void filter_set_activate_nolock(filter_set *handle)
{
    assert(handle);
    if (!handle->active)
    {
        if (handle->activate) (*handle->activate)(handle);
        handle->active = BUGLE_TRUE;
    }
}

/* FIXME: reverse deps should also be deactivated */
static void filter_set_deactivate_nolock(filter_set *handle)
{
    assert(handle);
    if (handle->active)
    {
        if (handle->deactivate) (*handle->deactivate)(handle);
        handle->active = BUGLE_FALSE;
    }
}

void filter_set_add(filter_set *handle, bugle_bool activate)
{
    linked_list *deps;
    linked_list_node *i;
    filter_set *s;

    if (!handle->added)
    {
        handle->added = BUGLE_TRUE;
        deps = (linked_list *) bugle_hash_get(&filter_set_dependencies, handle->name);
        if (deps)
        {
            for (i = bugle_list_head(deps); i; i = bugle_list_next(i))
            {
                s = bugle_filter_set_get_handle((const char *) bugle_list_data(i));
                if (!s)
                {
                    bugle_log_printf("filters", "load", BUGLE_LOG_ERROR,
                                     "filter-set %s depends on unknown filter-set %s",
                                     handle->name,
                                     ((const char *) bugle_list_data(i)));
                }
                filter_set_add(s, activate);
            }
        }
        bugle_list_append(&added_filter_sets, handle);
        handle->active = activate;
    }
}

static const char *get_name_filter_set(void *f)
{
    return ((filter_set *) f)->name;
}

/* Puts filter-sets into the proper order and initialises them */
static void load_filter_sets(void)
{
    linked_list_node *i, *j;
    filter_set *handle;
    filter *f;

    compute_order(&added_filter_sets, &filter_set_orders, get_name_filter_set);
    for (i = bugle_list_head(&added_filter_sets); i; i = bugle_list_next(i))
    {
        handle = (filter_set *) bugle_list_data(i);
        if (handle->load && !(*handle->load)(handle))
        {
            bugle_log_printf(handle->name, "load", BUGLE_LOG_ERROR,
                             "failed to initialise filter-set %s", handle->name);
            exit(1);
        }
        handle->loaded = BUGLE_TRUE;

        for (j = bugle_list_head(&handle->filters); j; j = bugle_list_next(j))
        {
            f = (filter *) bugle_list_data(j);
            bugle_list_append(&loaded_filters, f);
        }

        if (handle->active)
        {
            filter_set_activate_nolock(handle);
        }
    }
}

void filter_set_activate(filter_set *handle)
{
    bugle_thread_rwlock_wrlock(&active_callbacks_rwlock);
    filter_set_activate_nolock(handle);
    compute_active_callbacks();
    bugle_thread_rwlock_unlock(&active_callbacks_rwlock);
}

void filter_set_deactivate(filter_set *handle)
{
    bugle_thread_rwlock_wrlock(&active_callbacks_rwlock);
    filter_set_deactivate_nolock(handle);
    compute_active_callbacks();
    bugle_thread_rwlock_unlock(&active_callbacks_rwlock);
}

/* Note: these should be called only from within a callback, in which
 * case the lock is already held.
 */
void bugle_filter_set_activate_deferred(filter_set *handle)
{
    filter_set_activation *activation = BUGLE_MALLOC(filter_set_activation);

    activation->set = handle;
    activation->active = BUGLE_TRUE;

    bugle_thread_rwlock_wrlock(&active_callbacks_rwlock);
    bugle_list_append(&activations_deferred, activation);
    bugle_thread_rwlock_unlock(&active_callbacks_rwlock);
}

void bugle_filter_set_deactivate_deferred(filter_set *handle)
{
    filter_set_activation *activation = BUGLE_MALLOC(filter_set_activation);

    activation->set = handle;
    activation->active = BUGLE_FALSE;

    bugle_thread_rwlock_wrlock(&active_callbacks_rwlock);
    bugle_list_append(&activations_deferred, activation);
    bugle_thread_rwlock_unlock(&active_callbacks_rwlock);
}

static const char *filter_get_name(void *f)
{
    return ((filter *) f)->name;
}

static void filter_compute_order(void)
{
    bugle_bool success;

    success = compute_order(&loaded_filters, &filter_orders, filter_get_name);
    if (!success)
    {
        bugle_log("filters", "load", BUGLE_LOG_ERROR,
                  "cyclic dependency between filters");
        exit(1);
    }
}

static void set_bypass(void)
{
    linked_list_node *i, *j;
    int k;
    bugle_bool *bypass;
    filter *cur;
    filter_catcher *catcher;

    bypass = BUGLE_NMALLOC(budgie_function_count(), bugle_bool);
    /* We use this temporary instead of modifying values directly, because
     * we don't want other threads to see intermediate values.
     */
    memset(bypass, 1, budgie_function_count() * sizeof(bugle_bool));
    for (i = bugle_list_head(&loaded_filters); i; i = bugle_list_next(i))
    {
        cur = (filter *) bugle_list_data(i);
        for (j = bugle_list_tail(&cur->callbacks); j; j = bugle_list_prev(j))
        {
            catcher = (filter_catcher *) bugle_list_data(j);
            if (strcmp(catcher->parent->name, "invoke") != 0)
                bypass[catcher->function] = BUGLE_FALSE;
        }
    }
    for (k = 0; k < budgie_function_count(); k++)
        budgie_function_set_bypass(k, bypass[k]);
    bugle_free(bypass);
}

/* Note: caller must take mutexes */
static void compute_active_callbacks(void)
{
    linked_list_node *i, *j;
    filter *cur;
    budgie_function func;
    filter_catcher *catcher;

    /* Clear the old active_callback lists */
    for (func = 0; func < budgie_function_count(); func++)
        bugle_list_clear(&active_callbacks[func]);

    for (i = bugle_list_head(&loaded_filters); i; i = bugle_list_next(i))
    {
        cur = (filter *) bugle_list_data(i);
        for (j = bugle_list_tail(&cur->callbacks); j; j = bugle_list_prev(j))
        {
            catcher = (filter_catcher *) bugle_list_data(j);
            if (cur->parent->active || catcher->inactive)
                bugle_list_append(&active_callbacks[catcher->function], catcher);
        }
    }
}

void filters_finalise(void)
{
    load_filter_sets();
    filter_compute_order();
    set_bypass();
    compute_active_callbacks();
}

void filters_run(function_call *call)
{
    linked_list_node *i;
    filter_catcher *cur;
    callback_data data;

    bugle_thread_rwlock_rdlock(&active_callbacks_rwlock);

    data.call_object = bugle_object_new(bugle_call_class, NULL, BUGLE_TRUE);
    for (i = bugle_list_head(&active_callbacks[call->generic.id]); i; i = bugle_list_next(i))
    {
        cur = (filter_catcher *) bugle_list_data(i);
        data.filter_set_handle = cur->parent->parent;
        if (!(*cur->callback)(call, &data)) break;
    }
    bugle_object_free(data.call_object);

    /* Process any pending activations */
    if (bugle_list_head(&activations_deferred))
    {
        /* Upgrade to a write lock. Somebody else make get in between the
         * unlock and the wrlock, but at worst they will do our work for us.
         */
        bugle_thread_rwlock_unlock(&active_callbacks_rwlock);
        bugle_thread_rwlock_wrlock(&active_callbacks_rwlock);
        while (bugle_list_head(&activations_deferred))
        {
            i = bugle_list_head(&activations_deferred);
            filter_set_activate_nolock((filter_set *) bugle_list_data(i));
            bugle_list_erase(&activations_deferred, i);
        }
        compute_active_callbacks();
    }
    bugle_thread_rwlock_unlock(&active_callbacks_rwlock);
}

filter_set *bugle_filter_set_new(const filter_set_info *info)
{
    filter_set *s;

    s = BUGLE_MALLOC(filter_set);
    s->name = info->name;
    s->help = info->help;
    bugle_list_init(&s->filters, (void (*)(void *)) filter_free);
    s->load = info->load;
    s->unload = info->unload;
    s->activate = info->activate;
    s->deactivate = info->deactivate;
    s->variables = info->variables;
    s->loaded = BUGLE_FALSE;
    s->active = BUGLE_FALSE;
    s->added = BUGLE_FALSE;
    s->dl_handle = current_dl_handle;

    bugle_list_append(&filter_sets, s);
    /* FIXME: dirty hack. To make sure that 'log' is loaded and loaded
     * first, make sure every filter-set depends on it
     */
    if (strcmp(s->name, "log") != 0)
    {
        bugle_filter_set_depends(s->name, "log");
        bugle_filter_set_order("log", s->name);
    }
    return s;
}

filter *bugle_filter_new(filter_set *handle, const char *name)
{
    filter *f;

    f = BUGLE_MALLOC(filter);
    f->name = name;
    f->parent = handle;
    bugle_list_init(&f->callbacks, bugle_free);
    bugle_list_append(&handle->filters, f);
    return f;
}

void bugle_filter_catches_function_id(filter *handle, budgie_function id,
                                      bugle_bool inactive,
                                      filter_callback callback)
{
    filter_catcher *cb;

    cb = BUGLE_MALLOC(filter_catcher);
    cb->parent = handle;
    cb->function = id;
    cb->inactive = inactive;
    cb->callback = callback;
    bugle_list_append(&handle->callbacks, cb);
}

void bugle_filter_catches_function(filter *handle, const char *f,
                                   bugle_bool inactive,
                                   filter_callback callback)
{
    budgie_function id;

    id = budgie_function_id(f);
    if (id != NULL_FUNCTION)
        bugle_filter_catches_function_id(handle, id, inactive, callback);
    else
        bugle_log_printf(handle->parent->name, handle->name, BUGLE_LOG_WARNING,
                         "Attempt to catch unknown function %s", f);
}

void bugle_filter_catches(filter *handle, const char *group,
                          bugle_bool inactive,
                          filter_callback callback)
{
    budgie_function i;
    budgie_group g;

    i = budgie_function_id(group);
    if (i == NULL_FUNCTION)
    {
        bugle_log_printf(handle->parent->name, handle->name, BUGLE_LOG_WARNING,
                         "Attempt to catch unknown function %s", group);
        return;
    }
    g = budgie_function_group(i);
    /* FIXME: there should be a way to speed this up */
    for (i = 0; i < budgie_function_count(); i++)
        if (budgie_function_group(i) == g)
            bugle_filter_catches_function_id(handle, i, inactive, callback);
}

void bugle_filter_catches_all(filter *handle, bugle_bool inactive,
                              filter_callback callback)
{
    budgie_function i;
    filter_catcher *cb;

    for (i = 0; i < budgie_function_count(); i++)
    {
        cb = BUGLE_MALLOC(filter_catcher);
        cb->parent = handle;
        cb->function = i;
        cb->inactive = inactive;
        cb->callback = callback;
        bugle_list_append(&handle->callbacks, cb);
    }
}

void bugle_filter_order(const char *before, const char *after)
{
    register_order(&filter_orders, before, after);
}

void bugle_filter_set_depends(const char *base, const char *dep)
{
    register_order(&filter_set_dependencies, dep, base);
    register_order(&filter_set_orders, dep, base);
}

void bugle_filter_set_order(const char *before, const char *after)
{
    register_order(&filter_set_orders, before, after);
}

bugle_bool bugle_filter_set_is_loaded(const filter_set *handle)
{
    assert(handle);
    return handle->loaded;
}

bugle_bool bugle_filter_set_is_active(const filter_set *handle)
{
    assert(handle);
    return handle->active;
}

filter_set *bugle_filter_set_get_handle(const char *name)
{
    linked_list_node *i;
    filter_set *cur;

    for (i = bugle_list_head(&filter_sets); i; i = bugle_list_next(i))
    {
        cur = (filter_set *) bugle_list_data(i);
        if (strcmp(name, cur->name) == 0)
            return cur;
    }
    return NULL;
}

void *bugle_filter_set_get_symbol(filter_set *handle, const char *name)
{
    assert(handle != NULL);
    return bugle_dl_sym_data(handle->dl_handle, name);
}

object_class *bugle_get_call_class(void)
{
    assert(bugle_call_class != NULL);
    return bugle_call_class;
}

void filters_help(void)
{
    linked_list_node *i;
    const filter_set_variable_info *j;
    filter_set *cur;

    bugle_flockfile(stderr);
#if BUGLE_BINFMT_LDPRELOAD
    fprintf(stderr, "Usage: BUGLE_CHAIN=<chain> LD_PRELOAD=libbugle.so <program> <args>\n");
#else
    fprintf(stderr, "Usage: BUGLE_CHAIN=<chain> <program> <args>\n");
#endif
    fprintf(stderr, "The following filter-sets are available:\n");
    for (i = bugle_list_head(&filter_sets); i; i = bugle_list_next(i))
    {
        cur = (filter_set *) bugle_list_data(i);
        if (cur->help)
            fprintf(stderr, "  %s: %s\n", cur->name, cur->help);
        j = cur->variables;
        for (j = cur->variables; j && j->name; j++)
            if (j->help)
            {
                const char *type_str = NULL;
                switch (j->type)
                {
                case FILTER_SET_VARIABLE_INT:
                case FILTER_SET_VARIABLE_UINT:
                case FILTER_SET_VARIABLE_POSITIVE_INT:
                    type_str = " (int)";
                    break;
                case FILTER_SET_VARIABLE_FLOAT:
                    type_str = " (float)";
                    break;
                case FILTER_SET_VARIABLE_BOOL:
                    type_str = " (bugle_bool)";
                    break;
                case FILTER_SET_VARIABLE_STRING:
                    type_str = " (string)";
                    break;
                case FILTER_SET_VARIABLE_KEY:
                    type_str = " (key)";
                case FILTER_SET_VARIABLE_CUSTOM:
                    type_str = "";
                    break;
                }
                fprintf(stderr, "    %s%s: %s\n",
                        j->name, type_str, j->help);
            }
    }
    bugle_funlockfile(stderr);
}
