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

/* The function names and functionality are modelled on libiberty,
 * but are independently implemented. They are light wrappers around
 * the similarly named standard functions, but they display an error
 * and exit if memory could not be allocated. In some cases they also
 * reimplement non-portable functionality.
 */

#ifndef BUGLE_COMMON_SAFEMEM_H
#define BUGLE_COMMON_SAFEMEM_H

#if HAVE_CONFIG_H
# include <stddef.h>
#endif
#include <stdio.h>

void *xmalloc(size_t size);
void *xcalloc(size_t nmemb, size_t size);
void *xrealloc(void *ptr, size_t size);
char *xstrdup(const char *s);

/* Appends src to dest, possibly xrealloc()ing, and returns the pointer.
 * It assumes that dest was malloc()ed with a size that is the smallest
 * power of 2 large enough to hold it, and this will also hold as a
 * post-condition.
 */
char *xstrcat(char *dest, const char *src);

int xasprintf(char **strp, const char *format, ...);

/* Like fgets, but creates the memory. The return value has the same
 * meaning as for fgets, but must be free()ed if non-NULL
 */
char *xafgets(FILE *stream);

#endif /* !BUGLE_COMMON_SAFEMEM_H */
