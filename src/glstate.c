#if HAVE_CONFIG_H
# include <config.h>
#endif
#include "src/glstate.h"
#include "src/types.h"
#include "src/utils.h"
#include "budgielib/state.h"
#include <GL/gl.h>
#include <GL/glext.h>
#include <assert.h>

static GLenum state_to_enum(state_generic *state)
{
    /* FIXME: should be made must faster (store in the specs) */
    return gl_token_to_enum(state->spec->name);
}

static inline GLint ptr_to_int(const void *ptr)
{
    return ((const char *) ptr) - ((const char *) NULL);
}

void glstate_get_enable(state_generic *state)
{
    GLenum e;

    e = state_to_enum(state);
    assert(state->spec->data_type == TYPE_9GLboolean);
    *(GLboolean *) state->data = (*glIsEnabled_real)(e);
}

void glstate_get_global(state_generic *state)
{
    GLenum e;
    double data[16]; /* 16 should be enough */

    e = state_to_enum(state);
    switch (state->spec->data_type)
    {
    case TYPE_P6GLvoid:
        (*glGetPointerv_real)(e, (GLvoid **) state->data);
         break;
    case TYPE_8GLdouble:
        (*glGetDoublev_real)(e, (GLdouble *) state->data);
        break;
    case TYPE_7GLfloat:
        (*glGetFloatv_real)(e, (GLfloat *) state->data);
        break;
    case TYPE_5GLint:
    case TYPE_6GLuint:
#if GLENUM_IS_GLUINT
    case TYPE_6GLenum:
#endif
        (*glGetIntegerv_real)(e, (GLint *) state->data);
        break;
    case TYPE_9GLboolean:
        (*glGetBooleanv_real)(e, (GLboolean *) state->data);
        break;
    default:
        assert((size_t) state->spec->data_length <= sizeof(data) / sizeof(data[0]));
        (*glGetDoublev_real)(e, data);
        type_convert(state->data, state->spec->data_type, data, TYPE_8GLdouble, state->spec->data_length);
    }
}

static GLenum target_to_binding(GLenum target)
{
    switch (target)
    {
    case GL_TEXTURE_1D: return GL_TEXTURE_BINDING_1D;
    case GL_TEXTURE_2D: return GL_TEXTURE_BINDING_2D;
    case GL_TEXTURE_CUBE_MAP_ARB: return GL_TEXTURE_BINDING_CUBE_MAP_ARB;
    case GL_TEXTURE_3D: return GL_TEXTURE_BINDING_3D;
    default: abort();
    }
}

static GLenum get_texture_target(state_generic *state)
{
    return ptr_to_int(state->parent->key);
}

static GLenum push_texture_binding(GLenum target, state_generic *state)
{
    GLenum texture, binding;
    GLenum old;

    binding = target_to_binding(target);
    (*glGetIntegerv_real)(binding, (GLint *) &old);
    texture = ptr_to_int(state->key);
    (*glBindTexture_real)(target, texture);
    return old;
}

static void pop_texture_binding(GLenum target, GLenum old)
{
    (*glBindTexture_real)(target, old);
}

static GLenum push_server_texture_unit(state_generic *state)
{
    GLenum old, cur;

    /* FIXME: check if we really have multitex */
    (*glGetIntegerv_real)(GL_ACTIVE_TEXTURE_ARB, (GLint *) &old);
    cur = GL_TEXTURE0_ARB + ptr_to_int(state->key);
    if (cur != old)
    {
        (*glActiveTextureARB_real)(cur);
        return old;
    }
    else
        return 0;
}

static inline void pop_server_texture_unit(GLenum old)
{
    if (old)
        (*glActiveTextureARB_real)(old);
}

void glstate_get_texparameter(state_generic *state)
{
    GLenum old_texture;
    GLenum target;
    GLenum e;
    float data[16]; /* should be enough */

    target = get_texture_target(state->parent);
    old_texture = push_texture_binding(target, state->parent);

    e = state_to_enum(state);
    switch (state->spec->data_type)
    {
    case TYPE_5GLint:
    case TYPE_6GLuint:
#if GLENUM_IS_GLUINT
    case TYPE_6GLenum:
#endif
        (*glGetTexParameteriv)(target, e, state->data);
        break;
    case TYPE_7GLfloat:
        (*glGetTexParameterfv)(target, e, state->data);
        break;
    default:
        assert((size_t) state->spec->data_length <= sizeof(data) / sizeof(data[0]));
        (*glGetTexParameterfv)(target, e, data);
        type_convert(state->data, state->spec->data_type, data, TYPE_7GLfloat, state->spec->data_length);
    }

    pop_texture_binding(target, old_texture);
}

void glstate_get_texlevelparameter(state_generic *state)
{
    state_generic *tex_state;
    GLenum target, old_texture, e;
    GLint level;
    GLfloat data[16];

    tex_state = state->parent->parent->parent;
    target = get_texture_target(tex_state);
    old_texture = push_texture_binding(target, tex_state);

    e = state_to_enum(state);
    level = ptr_to_int(state->parent->key);
    switch (state->spec->data_type)
    {
    case TYPE_5GLint:
    case TYPE_6GLuint:
#if GLENUM_IS_GLUINT
    case TYPE_6GLenum:
#endif
        (*glGetTexLevelParameteriv_real)(target, level, e, state->data);
        break;
    case TYPE_7GLfloat:
        (*glGetTexLevelParameterfv_real)(target, level, e, state->data);
        break;
    default:
        assert((size_t) state->spec->data_length <= sizeof(data) / sizeof(data[0]));
        (*glGetTexLevelParameterfv_real)(target, level, e, data);
        type_convert(state->data, state->spec->data_type, data, TYPE_7GLfloat, state->spec->data_length);
    }

    pop_texture_binding(target, old_texture);
}

void glstate_get_texgen(state_generic *state)
{
    GLenum old_unit;
    GLenum coord;
    GLenum e;
    GLdouble data[16];

    old_unit = push_server_texture_unit(state->parent->parent->parent);
    coord = ptr_to_int(state->parent->key) + GL_S;
    if (state->spec->data_type == TYPE_9GLboolean) /* enable bit */
        *(GLboolean *) state->data = (*glIsEnabled_real)(coord);
    else
    {
        e = state_to_enum(state);
        switch (state->spec->data_type)
        {
        case TYPE_8GLdouble:
            (*glGetTexGendv_real)(coord, e, (GLdouble *) state->data);
            break;
        case TYPE_7GLfloat:
            (*glGetTexGenfv_real)(coord, e, (GLfloat *) state->data);
            break;
        case TYPE_5GLint:
        case TYPE_6GLuint:
#if GLENUM_IS_GLUINT
        case TYPE_6GLenum:
#endif
            (*glGetTexGeniv_real)(coord, e, (GLint *) state->data);
            break;
        default:
            assert((size_t) state->spec->data_length <= sizeof(data) / sizeof(data[0]));
            (*glGetTexGendv_real)(coord, e, data);
            type_convert(state->data, state->spec->data_type, data, TYPE_8GLdouble, state->spec->data_length);
        }
    }

    pop_server_texture_unit(old_unit);
}

void glstate_get_texunit(state_generic *state)
{
    GLenum old_unit;
    GLenum e;
    GLdouble data[16];

    old_unit = push_server_texture_unit(state->parent);
    e = state_to_enum(state);
    if (state->spec->data_type == TYPE_9GLboolean) /* enable bit */
        *(GLboolean *) state->data = (*glIsEnabled_real)(e);
    else
    {
        switch (state->spec->data_type)
        {
        case TYPE_8GLdouble:
            (*glGetDoublev_real)(e, (GLdouble *) state->data);
            break;
        case TYPE_7GLfloat:
            (*glGetFloatv_real)(e, (GLfloat *) state->data);
            break;
        case TYPE_5GLint:
        case TYPE_6GLuint:
#if GLENUM_IS_GLUINT
        case TYPE_6GLenum:
#endif
            (*glGetIntegerv_real)(e, (GLint *) state->data);
            break;
        default:
            assert((size_t) state->spec->data_length <= sizeof(data) / sizeof(data[0]));
            (*glGetDoublev_real)(e, data);
            type_convert(state->data, state->spec->data_type, data, TYPE_8GLdouble, state->spec->data_length);
        }
    }

    pop_server_texture_unit(old_unit);
}

void glstate_get_texenv(state_generic *state)
{
    GLenum old_unit, e;
    GLfloat data[16];

    old_unit = push_server_texture_unit(state->parent->parent);

    e = state_to_enum(state);
    switch (state->spec->data_type)
    {
    case TYPE_7GLfloat:
        (*glGetTexEnvfv_real)(GL_TEXTURE_ENV, e, state->data);
        break;
    case TYPE_5GLint:
    case TYPE_6GLuint:
#if GLENUM_IS_GLUINT
    case TYPE_6GLenum:
#endif
        (*glGetTexEnviv_real)(GL_TEXTURE_ENV, e, state->data);
        break;
    default:
        assert((size_t) state->spec->data_length <= sizeof(data) / sizeof(data[0]));
        (*glGetTexEnvfv_real)(GL_TEXTURE_ENV, e, data);
        type_convert(state->data, state->spec->data_type, data, TYPE_7GLfloat, state->spec->data_length);
    }

    pop_server_texture_unit(old_unit);
}
