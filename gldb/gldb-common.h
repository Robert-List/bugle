/*  BuGLe: an OpenGL debugging tool
 *  Copyright (C) 2004, 2005  Bruce Merry
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

#ifndef BUGLE_GLDB_GLDB_COMMON_H
#define BUGLE_GLDB_GLDB_COMMON_H

#if HAVE_CONFIG_H
# include <config.h>
#endif
#include <sys/types.h>
#include <inttypes.h>
#include <signal.h>
#include <unistd.h>
#include "common/bool.h"
#include "common/linkedlist.h"

#if HAVE_READLINE && !HAVE_RL_COMPLETION_MATCHES
# define rl_completion_matches completion_matches
#endif

#define RESTART(expr) \
    do \
    { \
        while ((expr) == -1) \
        { \
            if (errno != EINTR) \
            { \
                perror(#expr " failed"); \
                exit(1); \
            } \
        } \
    } while (0)

/* There are four possible statuses:
 * - dead: the program has not been started or has exited
 * - started: the program is busy initialising and accepting our
 *   breakpoints
 * - running: we have received RESP_RUNNING
 * - stopped: the program is stopped on a breakpoint/error/interrupt
 */
typedef enum
{
    GLDB_STATUS_DEAD,
    GLDB_STATUS_STARTED,
    GLDB_STATUS_RUNNING,
    GLDB_STATUS_STOPPED
} gldb_status;

typedef struct
{
    char *name;
    char *value;
    bugle_linked_list children;
} gldb_state;

typedef struct
{
    uint32_t code;
    uint32_t id;
    uint32_t value;
} gldb_response_ans;

typedef struct
{
    uint32_t code;
    uint32_t id;
    char *call;
} gldb_response_break;

typedef struct
{
    uint32_t code;
    uint32_t id;
    char *call;
    char *error;
} gldb_response_break_error;

typedef struct
{
    uint32_t code;
    uint32_t id;
    char *call;
} gldb_response_stop;

typedef struct
{
    uint32_t code;
    uint32_t id;
    char *state;
} gldb_response_state;

typedef struct
{
    uint32_t code;
    uint32_t id;
    uint32_t error_code;
    char *error;
} gldb_response_error;

typedef struct
{
    uint32_t code;
    uint32_t id;
} gldb_response_running;

typedef struct
{
    uint32_t code;
    uint32_t id;
    char *data;
    uint32_t length;
} gldb_response_screenshot;

typedef struct
{
    uint32_t code;
    uint32_t id;
    gldb_state *root;
} gldb_response_state_tree;

/* Generic type for responses. Always instantiated via one of the above. */
typedef struct
{
    uint32_t code;
    uint32_t id;
} gldb_response;

/* Only first n characters of name are considered. This simplifies
 * generate_commands.
 */
gldb_state *gldb_state_find(gldb_state *root, const char *name, size_t n);
/* Updates the internal state tree if necessary, and returns the tree */
gldb_state *gldb_state_update();

/* Checks that the result of a system call is not -1, otherwise throws
 * an error.
 */
void gldb_safe_syscall(int r, const char *str);

void gldb_run(uint32_t id, void (*child_init)(void));
void gldb_send_quit(uint32_t id);
void gldb_send_continue(uint32_t id);
void gldb_send_enable_disable(uint32_t id, const char *filterset, bool enable);
void gldb_send_screenshot(uint32_t id);
void gldb_send_async(uint32_t id);
void gldb_send_state_tree(uint32_t id);
void gldb_set_break_error(uint32_t id, bool brk);
void gldb_set_break(uint32_t id, const char *function, bool brk);

const char *gldb_get_chain(void);
void gldb_set_chain(const char *chain);
void gldb_notify_child_dead(void);

gldb_response *gldb_get_response(void);
void gldb_free_response(gldb_response *response);

bool gldb_get_break_error(void);
gldb_status gldb_get_status(void);
pid_t gldb_get_child_pid(void);
const char *gldb_get_program(void);
/* These should only be used for select() and the like, never read from.
 * All protocol details are abstracted by gldb_send_*, gldb_set_* and
 * gldb_get_response.
 */
int gldb_get_in_pipe(void);
int gldb_get_out_pipe(void);

void gldb_initialise(int argc, char * const *argv);
void gldb_shutdown(void);

#endif /* !BUGLE_GLDB_GLDB_COMMON_H */
