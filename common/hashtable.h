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

#ifndef BUGLE_COMMON_HASHTABLE_H
#define BUGLE_COMMON_HASHTABLE_H

#if HAVE_CONFIG_H
# include <config.h>
#endif
#include "common/bool.h"

typedef struct
{
    char *key;
    void *value;
} hash_entry;

typedef struct
{
    hash_entry *entries;
    size_t size;
    size_t count;
    int size_index;
} hash_table;


void initialise_hashing(void);

void hash_init(hash_table *table);
void hash_set(hash_table *table, const char *key, void *value);
void *hash_get(const hash_table *table, const char *key);
void hash_clear(hash_table *table, bool free_data);

/* Walk the hash table. A walker loop looks like this:
 * for (h = hash_begin(&table); h; h = hash_next(&table, h))
 */
const hash_entry *hash_begin(hash_table *table);
const hash_entry *hash_next(hash_table *table, const hash_entry *e);

#endif /* !BUGLE_COMMON_HASHTABLE_H */
