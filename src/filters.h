#ifndef BUGLE_SRC_FILTERS_H
#define BUGLE_SRC_FILTERS_H

#if HAVE_CONFIG_H
# include <config.h>
#endif
#include <stddef.h>
#include "src/types.h"
#include "src/linkedlist.h"
#include "common/bool.h"

struct filter_set_s;

typedef bool (*filter_set_initialiser)(struct filter_set_s *);
typedef void (*filter_set_destructor)(struct filter_set_s *);
typedef bool (*filter_callback)(function_call *call, void *data);

typedef struct
{
    char *name;
    filter_callback callback;
    struct filter_set_s *parent;
} filter;

typedef struct filter_set_s
{
    char *name;
    linked_list filters;
    filter_set_initialiser init;
    filter_set_destructor done;
    ptrdiff_t offset;
    void *dl_handle;

    bool initialised;
    bool enabled;
} filter_set;

/* Functions to be used by the interceptor */

void initialise_filters(void);
void enable_filter_set(filter_set *handle);
void run_filters(function_call *call);

/* Functions to be used by the filter libraries */

filter_set *register_filter_set(const char *name,
                                filter_set_initialiser init,
                                filter_set_destructor done);
void register_filter(filter_set *handle, const char *name,
                     filter_callback callback);
void register_filter_set_depends(const char *base, const char *dep);
void register_filter_depends(const char *after, const char *before);
void register_filter_set_call_state(filter_set *handle, size_t bytes);
filter_set *get_filter_set_handle(const char *name);
void *get_filter_set_symbol(filter_set *handle, const char *name);

#endif /* BUGLE_SRC_FILTERS_H */
