/*  BuGLe: an OpenGL debugging tool
 *  Copyright (C) 2004  Bruce Merry
 *
 *  This program is free software; you can redistribute it and/or modify
 *  it under the terms of the GNU General Public License as published by
 *  the Free Software Foundation; either version 2 of the License, or
 *  (at your option) any later version.
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
#include <stddef.h>
#include <pthread.h>
#include <string.h>
#include "common/linkedlist.h"
#include "common/safemem.h"
#include "common/bool.h"
#include "src/objects.h"

typedef struct
{
    void (*constructor)(const void *key, void *data);
    void (*destructor)(void *data);
    size_t size;
} object_class_info;

void bugle_object_class_init(object_class *klass, object_class *parent)
{
    bugle_list_init(&klass->info);
    klass->total_size = 0;
    klass->parent = parent;
    if (parent)
        klass->parent_offset = bugle_object_class_register(parent, NULL, NULL, sizeof(void *));
    else
        pthread_key_create(&klass->current, NULL);
}

void bugle_object_class_clear(object_class *klass)
{
    bugle_list_clear(&klass->info, true);
    if (!klass->parent)
        pthread_key_delete(klass->current);
}

size_t bugle_object_class_register(object_class *klass,
                                   void (*constructor)(const void *key, void *data),
                                   void (*destructor)(void *data),
                                   size_t size)
{
    object_class_info *info;
    size_t ans;

    info = bugle_malloc(sizeof(object_class_info));
    info->constructor = constructor;
    info->destructor = destructor;
    info->size = size;
    bugle_list_append(&klass->info, info);
    ans = klass->total_size;
    klass->total_size += size;
    return ans;
}

static inline void *offset_ptr(void *base, size_t offset)
{
    return (void *) (((char *) base) + offset);
}

void *bugle_object_new(const object_class *klass, const void *key, bool make_current)
{
    void *ans;
    size_t offset = 0;
    bugle_list_node *i;
    const object_class_info *info;

    if (klass->total_size)
        ans = bugle_malloc(klass->total_size);
    else
        ans = bugle_malloc(1);
    if (make_current) bugle_object_set_current(klass, ans);

    for (i = bugle_list_head(&klass->info); i; i = bugle_list_next(i))
    {
        info = (const object_class_info *) bugle_list_data(i);
        if (info->constructor)
            (*info->constructor)(key, offset_ptr(ans, offset));
        else
            memset(offset_ptr(ans, offset), 0, info->size);
        offset += info->size;
    }
    return ans;
}

void bugle_object_delete(const object_class *klass, void *obj)
{
    bugle_list_node *i;
    const object_class_info *info;
    size_t offset = 0;

    for (i = bugle_list_head(&klass->info); i; i = bugle_list_next(i))
    {
        info = (const object_class_info *) bugle_list_data(i);
        if (info->destructor)
            (*info->destructor)(offset_ptr(obj, offset));
        offset += info->size;
    }
}

void *bugle_object_get_current(const object_class *klass)
{
    void *ans;

    if (klass->parent)
    {
        ans = bugle_object_get_current_data(klass->parent, klass->parent_offset);
        if (!ans) return NULL;
        else return *(void **) ans;
    }
    else
        return pthread_getspecific(klass->current);
}

void *bugle_object_get_current_data(const object_class *klass, size_t offset)
{
    return bugle_object_get_data(klass, bugle_object_get_current(klass), offset);
}

void bugle_object_set_current(const object_class *klass, void *obj)
{
    void *tmp;

    if (klass->parent)
    {
        tmp = bugle_object_get_current_data(klass->parent, klass->parent_offset);
        if (tmp) *(void **) tmp = obj;
    }
    else
        pthread_setspecific(klass->current, obj);
}

void *bugle_object_get_data(const object_class *klass, void *obj, size_t offset)
{
    if (!obj) return NULL;
    else return offset_ptr(obj, offset);
}
