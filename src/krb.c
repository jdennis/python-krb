/*
 * Authors: John Dennis <jdennis@redhat.com>
 *
 * Copyright (C) 2012  Red Hat
 * see file 'COPYING' for use and warranty information
 *
 * This program is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program.  If not, see <http://www.gnu.org/licenses/>.
 */

#include "Python.h"
#include "structmember.h"
#include "datetime.h"
#include "timefuncs.h"
#include "common.h"

#include <stdbool.h>
#include <stdarg.h>
#include <sys/socket.h>
#include <netdb.h>

#include "krb5.h"


/* ========================================================================== */

static PyTypeObject AddressType;
typedef struct {
    PyObject_HEAD
    krb5_address address;
} Address;
#define PyAddress_Check(op) PyObject_TypeCheck(op, &AddressType)

static PyTypeObject KeyBlockType;
typedef struct {
    PyObject_HEAD
    krb5_keyblock *keyblock;
} KeyBlock;
#define PyKeyBlock_Check(op) PyObject_TypeCheck(op, &KeyBlockType)

static PyTypeObject ContextType;
typedef struct {
    PyObject_HEAD
    krb5_context context;
} Context;
#define PyContext_Check(op) PyObject_TypeCheck(op, &ContextType)

static PyTypeObject PrincipalType;
typedef struct {
    PyObject_HEAD
    krb5_principal principal;
} Principal;
#define PyPrincipal_Check(op) PyObject_TypeCheck(op, &PrincipalType)

static PyTypeObject TicketTimesType;
typedef struct {
    PyObject_HEAD
    krb5_ticket_times ticket_times;
} TicketTimes;
#define PyTicketTimes_Check(op) PyObject_TypeCheck(op, &TicketTimesType)

static PyTypeObject CredentialType;
typedef struct {
    PyObject_HEAD
    krb5_creds *credential;
} Credential;
#define PyCredential_Check(op) PyObject_TypeCheck(op, &CredentialType)

static PyTypeObject CCacheType;
typedef struct {
    PyObject_HEAD
    krb5_ccache ccache;
} CCache;
#define PyCCache_Check(op) PyObject_TypeCheck(op, &CCacheType)

static PyTypeObject KeytabEntryType;
typedef struct {
    PyObject_HEAD
    krb5_keytab_entry keytab_entry;
} KeytabEntry;
#define PyKeytabEntry_Check(op) PyObject_TypeCheck(op, &KeytabEntry>Type)

/* ========================================================================== */
#define KRB_THREAD_LOCAL_KEY "krb"
#define CURRENT_CONTEXT_NAME "current_context"

#define OCTETS_PER_LINE_DEFAULT 16
#define HEX_SEPARATOR_DEFAULT ":"

/*
 * Get a Principal object given a Python object.
 *
 * py_arg is a PyObject which may be a Principal object
 * or a principal name as string (str or unicode).
 *
 * py_principal will be initialized to a Principal object with a
 * new reference. The ref count must be decremented before exiting.
 * It may be inialized to NULL, if so the error condition will have
 * been set.
 *
 * name is argument name used in the error message.
 */

#define PRINCIPAL_FROM_ARG(py_principal, py_arg, name)                  \
{                                                                       \
    py_principal = NULL;                                                \
                                                                        \
    if (PyPrincipal_Check(py_arg)) {                                    \
        py_principal = (Principal *)py_arg;                             \
        Py_INCREF(py_principal);                                        \
    } else if (PyString_Check(py_arg) || PyUnicode_Check(py_arg)) {     \
        PyObject *py_args = NULL;                                       \
                                                                        \
        if ((py_args = Py_BuildValue("(O)", py_arg)) != NULL) {         \
            py_principal = (Principal *)PyObject_Call((PyObject *)&PrincipalType, py_args, NULL); \
            Py_DECREF(py_args);                                         \
        }                                                               \
    } else {                                                            \
        PyErr_Format(PyExc_TypeError,                                   \
                     name " principal must be a Principal object or string, not %.200s", \
                     Py_TYPE(py_arg)->tp_name);                         \
    }                                                                   \
}

/* ========================================================================== */

static krb5_context
get_current_context();

static krb5_context
get_current_context_no_error();

PyObject *
PyString_UTF8(PyObject *obj, char *name);

static PyObject *
ticket_flags_str(krb5_flags flags);

static PyObject *
CCache_new_from_krb5_ccache(krb5_ccache ccache);

static int
set_thread_local(const char *name, PyObject *obj);

static PyObject *
get_thread_local(const char *name);

static int
Address_init_from_net_addr(Address *self, krb5_addrtype addrtype, const char *net_addr, socklen_t net_addr_len);

/* ========================================================================== */

static PyObject *empty_tuple = NULL;
static PyObject *time_module = NULL;
static PyObject *KRB_Exception = NULL;

PyObject *krb_enctype_name_to_value = NULL;
PyObject *krb_enctype_value_to_name = NULL;


static char hex_chars[] = "0123456789abcdef";

/* ========================================================================== */

typedef PyObject *(*format_lines_func)(PyObject *self, PyObject *args, PyObject *kwds);

static PyObject *
line_fmt_tuple(int level, const char *label, PyObject *py_value);

static PyObject *
make_line_fmt_tuples(int level, PyObject *src);

static PyObject *
py_make_line_fmt_tuples(PyObject *self, PyObject *args, PyObject *kwds);

static PyObject *
fmt_label(int level, char *label);

static PyObject *
format_from_lines(format_lines_func formatter, PyObject *self, PyObject *args, PyObject *kwds);

static PyObject *
py_indented_format(PyObject *self, PyObject *args, PyObject *kwds);

#define FMT_OBJ_AND_APPEND(dst_fmt_tuples, label, src_obj, level, fail) \
{                                                                       \
    PyObject *fmt_tuple = NULL;                                         \
                                                                        \
    if ((fmt_tuple = line_fmt_tuple(level, label, src_obj)) == NULL) {  \
        goto fail;                                                      \
    }                                                                   \
    if (PyList_Append(dst_fmt_tuples, fmt_tuple) != 0) {                \
        Py_DECREF(fmt_tuple);                                           \
        goto fail;                                                      \
    }                                                                   \
}

#define FMT_LABEL_AND_APPEND(dst_fmt_tuples, label, level, fail)        \
{                                                                       \
    PyObject *fmt_tuple = NULL;                                         \
                                                                        \
    if ((fmt_tuple = fmt_label(level, label)) == NULL) {                \
        goto fail;                                                      \
    }                                                                   \
    if (PyList_Append(dst_fmt_tuples, fmt_tuple) != 0) {                \
        Py_DECREF(fmt_tuple);                                           \
        goto fail;                                                      \
    }                                                                   \
}

#define APPEND_LINE_TUPLES_AND_CLEAR(dst_fmt_tuples, src_fmt_tuples, fail) \
{                                                                       \
    PyObject *src_obj;                                                  \
    Py_ssize_t len, i;                                                  \
    if (src_fmt_tuples) {                                               \
        len = PyList_Size(src_fmt_tuples);                              \
        for (i = 0; i < len; i++) {                                     \
            src_obj = PyList_GetItem(src_fmt_tuples, i);                \
            PyList_Append(dst_fmt_tuples, src_obj);                     \
        }                                                               \
        Py_CLEAR(src_fmt_tuples);                                       \
    }                                                                   \
}

#define APPEND_LINES_AND_CLEAR(dst_fmt_tuples, src_lines, level, fail)  \
{                                                                       \
    PyObject *src_obj;                                                  \
    Py_ssize_t len, i;                                                  \
    if (src_lines) {                                                    \
        len = PySequence_Size(src_lines);                               \
        for (i = 0; i < len; i++) {                                     \
            src_obj = PySequence_GetItem(src_lines, i);                 \
            FMT_OBJ_AND_APPEND(dst_fmt_tuples, NULL, src_obj, level, fail); \
            Py_DECREF(src_obj);                                         \
        }                                                               \
        Py_CLEAR(src_lines);                                            \
    }                                                                   \
}

#define CALL_FORMAT_LINES_AND_APPEND(dst_fmt_tuples, obj, level, fail)  \
{                                                                       \
    PyObject *obj_line_fmt_tuples;                                      \
                                                                        \
    if ((obj_line_fmt_tuples =                                          \
         PyObject_CallMethod(obj, "format_lines",                       \
                             "(i)", level)) == NULL) {                  \
        goto fail;                                                      \
    }                                                                   \
                                                                        \
    APPEND_LINE_TUPLES_AND_CLEAR(dst_fmt_tuples, obj_line_fmt_tuples, fail); \
}


#define APPEND_OBJ_TO_HEX_LINES_AND_CLEAR(dst_fmt_tuples, obj, level, fail) \
{                                                                       \
    PyObject *obj_lines;                                                \
                                                                        \
    if ((obj_lines = obj_to_hex(obj, OCTETS_PER_LINE_DEFAULT,           \
                                HEX_SEPARATOR_DEFAULT)) == NULL) {      \
        goto fail;                                                      \
    }                                                                   \
    Py_CLEAR(obj);                                                      \
    APPEND_LINES_AND_CLEAR(dst_fmt_tuples, obj_lines, level, fail);     \
}

PyDoc_STRVAR(generic_format_doc,
"format(level=0, indent='    ') -> string)\n\
\n\
:Parameters:\n\
    level : integer\n\
        Initial indentation level, all subsequent indents are relative\n\
        to this starting level.\n\
    indent : string\n\
        string replicated once for each indent level then prepended to output line\n\
\n\
This is equivalent to:\n\
indented_format(obj.format_lines()) on an object providing a format_lines() method.\n\
");

PyDoc_STRVAR(generic_format_lines_doc,
"format_lines(level=0) -> [(level, string),...]\n\
\n\
:Parameters:\n\
    level : integer\n\
        Initial indentation level, all subsequent indents are relative\n\
        to this starting level.\n\
\n\
Formats the object into a sequence of lines with indent level\n\
information.  The return value is a list where each list item is a\n\
tuple.  The first item in the tuple is an integer\n\
representing the indentation level for that line. Any remaining items\n\
in the tuple are strings to be output on that line.\n\
\n\
The output of this function can be formatted into a single string by\n\
calling `indented_format()`, e.g.:\n\
\n\
    print indented_format(obj.format_lines())\n\
\n\
The reason this function returns a tuple as opposed to an single\n\
indented string is to support other text formatting systems such as\n\
GUI's with indentation controls.  See `indented_format()` for a\n\
complete explanation.\n\
");


/* Steals reference to obj_str */
static PyObject *
line_fmt_tuple(int level, const char *label, PyObject *py_value)
{
    Py_ssize_t tuple_size, i;
    PyObject *fmt_tuple = NULL;
    PyObject *py_label = NULL;
    PyObject *py_value_str = NULL;

    tuple_size = 1;             /* always have level */

    if (label) {
        tuple_size++;
        if ((py_label = PyString_FromFormat("%s:", label)) == NULL) {
            return NULL;
        }
    }

    if (py_value) {
        tuple_size++;
        if (PyString_Check(py_value) || PyUnicode_Check(py_value)) {
            py_value_str = py_value;
            Py_INCREF(py_value_str);
        } else {
            if ((py_value_str = PyObject_Str(py_value)) == NULL) {
                return NULL;
            }
        }
    }

    if ((fmt_tuple = PyTuple_New(tuple_size)) == NULL) {
        return NULL;
    }

    i = 0;
    PyTuple_SetItem(fmt_tuple, i++, PyInt_FromLong(level));

    if (py_label) {
        PyTuple_SetItem(fmt_tuple, i++, py_label);
    }

    if (py_value_str) {
        PyTuple_SetItem(fmt_tuple, i++, py_value_str);
    }

    return fmt_tuple;
}

static PyObject *
make_line_fmt_tuples(int level, PyObject *src)
{
    PyObject *lines = NULL;
    PyObject *obj = NULL;
    PyObject *fmt_tuple = NULL;
    PyObject *seq = NULL;
    Py_ssize_t n_objs, i;

    if (PyList_Check(src) || PyTuple_Check(src)) {
        seq = src;
        n_objs = PySequence_Size(seq);
        Py_INCREF(seq);
    } else {
        obj = src;
        Py_INCREF(obj);
        n_objs = 1;
    }

    if ((lines = PyList_New(n_objs)) == NULL) {
        goto exit;
    }

    if (seq) {
        for (i = 0; i < n_objs; i++) {
            if ((obj = PySequence_GetItem(seq, i)) == NULL) { /* new reference */
                Py_DECREF(lines);
                goto exit;
            }
            if ((fmt_tuple = line_fmt_tuple(level, NULL, obj)) == NULL) {
                Py_DECREF(lines);
                goto exit;
            }
            PyList_SetItem(lines, i, fmt_tuple);
            Py_CLEAR(obj);
        }
    } else {
        if ((fmt_tuple = line_fmt_tuple(level, NULL, obj)) == NULL) {
            Py_DECREF(lines);
            goto exit;
        }
        PyList_SetItem(lines, 0, fmt_tuple);
    }

 exit:
    Py_XDECREF(obj);
    Py_XDECREF(seq);
    return lines;
}

PyDoc_STRVAR(py_make_line_fmt_tuples_doc,
"make_line_fmt_tuples(level, obj) -> [(level, str), ...]\n\
\n\
:Parameters:\n\
    obj : object\n\
        If obj is a tuple or list then each member will be wrapped\n\
        in a 2-tuple of (level, str). If obj is a scalar object\n\
        then obj will be wrapped in a 2-tuple of (level, obj)\n\
    level : integer\n\
        Initial indentation level, all subsequent indents are relative\n\
        to this starting level.\n\
\n\
Return a list of line formatted tuples sutible to passing to\n\
`indented_format()`. Each tuple consists of a integer\n\
level value and a string object. This is equivalent to:\n\
[(level, str(x)) for x in obj].\n\
As a special case convenience if obj is a scalar object (i.e.\n\
not a list or tuple) then [(level, str(obj))] will be returned.\n\
");

static PyObject *
py_make_line_fmt_tuples(PyObject *self, PyObject *args, PyObject *kwds)
{
    static char *kwlist[] = {"level", "obj", NULL};
    int level = 0;
    PyObject *obj;

    TraceMethodEnter(self);

    if (!PyArg_ParseTupleAndKeywords(args, kwds, "iO:make_line_fmt_tuples", kwlist,
                                     &level, &obj))
        return NULL;

    return make_line_fmt_tuples(level, obj);
}

static PyObject *
fmt_label(int level, char *label)
{
    return line_fmt_tuple(level, label, NULL);
}

static PyObject *
format_from_lines(format_lines_func formatter, PyObject *self, PyObject *args, PyObject *kwds)
{
    static char *kwlist[] = {"level", "indent_len",  NULL};
    int level = 0;
    int indent_len = 4;
    PyObject *py_lines = NULL;
    PyObject *py_formatted_result = NULL;
    PyObject *tmp_args = NULL;

    if (!PyArg_ParseTupleAndKeywords(args, kwds, "|ii:format", kwlist, &level, &indent_len))
        return NULL;

    if ((tmp_args = Py_BuildValue("(i)", level)) == NULL) {
        goto fail;
    }
    if ((py_lines = formatter(self, tmp_args, NULL)) == NULL) {
        goto fail;
    }
    Py_CLEAR(tmp_args);

    if ((tmp_args = Py_BuildValue("Oi", py_lines, indent_len)) == NULL) {
        goto fail;
    }
    if ((py_formatted_result = py_indented_format(NULL, tmp_args, NULL)) == NULL) {
        goto fail;
    }

    Py_DECREF(tmp_args);
    Py_DECREF(py_lines);
    return py_formatted_result;

 fail:
    Py_XDECREF(tmp_args);
    Py_XDECREF(py_lines);
    return NULL;
}

PyDoc_STRVAR(py_indented_format_doc,
"indented_format(line_fmt_tuples, indent_len=4) -> string\n\
\n\
The function supports the display of complex objects which may be\n\
composed of other complex objects. There is often a need to output\n\
section headers or single strings and lists of <attribute,value> pairs\n\
(the attribute in this discussion is called a label), or even blank\n\
lines. All of these items should line up in columns at different\n\
indentation levels in order to visually see the structure.\n\
\n\
It would not be flexible enough to have object formatting routines\n\
which simply returned a single string with all the indentation and\n\
formatting pre-applied. The indentation width may not be what is\n\
desired. Or more importantly you might not be outputting to text\n\
display. It might be a GUI which desires to display the\n\
information. Most GUI's want to handle each string seperately and\n\
control indentation and the visibility of each item (e.g. a tree\n\
control).\n\
\n\
At the same time we want to satisfy the need for easy and simple text\n\
output. This routine will do that, e.g.:\n\
\n\
    print indented_format(obj.format_lines())\n\
\n\
To accomodate necessary flexibility the object formatting methods\n\
(format_lines()) return a list of tuples. Each tuple represents a\n\
single line with the first tuple item being the indentation level for\n\
the line. There may be 0,1 or 2 additional strings in the tuple which\n\
are to be output on the line. A single string are usually one of two\n\
things, either a section header or data that has been continuted onto\n\
multiple lines. Two strings usually represent a <attribute,value> pair\n\
with the first string being a label (e.g. attribute name).\n\
\n\
Each tuple may be:\n\
\n\
    (int,)\n\
        1-value tuple, no strings, e.g. blank line.\n\
\n\
    (int, string)\n\
        2-value tuple, output string at indent level.\n\
\n\
    (int, string, string)\n\
        3-value tuple, first string is a label, second string is a\n\
        value.  Starting at the indent level output the label, then\n\
        follow with the value. By keeping the label separate from the\n\
        value the ouput formatter may elect to align the values in\n\
        vertical columns for adjacent lines.\n\
\n\
Example:\n\
\n\
    # This list of tuples,\n\
\n\
    [(0, 'Constraints'),\n\
     (1, 'min:', '0')\n\
     (1, 'max:', '100'),\n\
     (1, 'Filter Data'),\n\
     (2, 'ab bc de f0 12 34 56 78 9a bc de f0')\n\
     (2, '12 34 56 78 9a bc de f0 12 34 56 78')\n\
    ]\n\
\n\
    # would product this output\n\
\n\
    Constraints\n\
        min: 0\n\
        max: 100\n\
        Filter Data:\n\
           ab bc de f0 12 34 56 78 9a bc de f0\n\
           12 34 56 78 9a bc de f0 12 34 56 78\n\
\n\
:Parameters:\n\
    line_fmt_tuples : [(level, ...),...]\n\
        A list of tuples. First tuple value is the indentation level\n\
        followed by optional strings for the line.\n\
    indent_len : int\n\
        Number of space characters repeated for each level and\n\
        prepended to the line string.\n\
\n\
");

static PyObject *
py_indented_format(PyObject *self, PyObject *args, PyObject *kwds)
{
    typedef struct {
        Py_ssize_t indent_len;
        Py_ssize_t label_len;
        Py_ssize_t value_len;
        Py_ssize_t justification_len;
    } LineInfo;


    static char *kwlist[] = {"lines_pairs", "indent_len", NULL};
    PyObject *py_lines = NULL;
    long line_level = 0;
    int indent_len = 4;
    int cur_indent_len = 0;
    char *src=NULL, *dst=NULL;
    Py_ssize_t num_lines, tuple_len;
    char *label = NULL;
    char *value = NULL;
    Py_ssize_t label_len, value_len, justification_len, max_align;
    char *src_end = NULL;
    PyObject *py_line_fmt_tuple = NULL;
    PyObject *py_level = NULL;
    PyObject *py_label = NULL;
    PyObject *py_value = NULL;
    PyObject *py_string_utf8 = NULL;
    Py_ssize_t cur_formatted_line_len;
    PyObject *py_formatted_str = NULL;
    Py_ssize_t formatted_str_len;
    char *formatted_str;
    Py_ssize_t i, j, k;
    LineInfo *line_info = NULL;

    TraceMethodEnter(self);

    if (!PyArg_ParseTupleAndKeywords(args, kwds, "O!|i:indented_format", kwlist,
                                     &PyList_Type, &py_lines, &indent_len))
        return NULL;

    num_lines = PyList_Size(py_lines);

    /*
     * Because we interrogate the length of the various strings
     * multiple times in the various loops we don't want to repeatedly
     * dereference and query the Pyton objects each time. So we
     * allocate an array to cache the information for efficency
     * purposes.
     */

    if ((line_info = PyMem_Malloc(num_lines*sizeof(LineInfo))) == NULL) {
        return PyErr_NoMemory();
    }

    /*
     * Step 1: Scan all the lines and get the string sizes.  Do all
     * error checking in this loop so we don't have to do it again
     * later. Cache the size information for faster access in
     * subseqent loops.
     */

    for (i = 0; i < num_lines; i++) {
        py_label = NULL;
        label = NULL;
        label_len = 0;

        py_value = NULL;
        value = NULL;
        value_len = 0;

        py_line_fmt_tuple = PyList_GetItem(py_lines, i);
        if (!PyTuple_Check(py_line_fmt_tuple)) {
            PyErr_Format(PyExc_TypeError, "line_fmt_tuples[%zd] must be a tuple, not %.200s",
                         i, Py_TYPE(py_line_fmt_tuple)->tp_name);
            goto fail;
        }

        tuple_len = PyTuple_Size(py_line_fmt_tuple);

        if (tuple_len < 1 || tuple_len > 3) {
            PyErr_Format(PyExc_TypeError, "line_fmt_tuples[%zd] tuple must have 1-3 items, not %d items",
                         i, tuple_len);
            goto fail;
        }

        py_level = PyTuple_GetItem(py_line_fmt_tuple, 0);
        if (tuple_len == 2) {
            py_label = PyTuple_GetItem(py_line_fmt_tuple, 1);
        } else if (tuple_len == 3) {
            py_label = PyTuple_GetItem(py_line_fmt_tuple, 1);
            py_value = PyTuple_GetItem(py_line_fmt_tuple, 2);
        }

        if (!PyInt_Check(py_level)) {
            PyErr_Format(PyExc_TypeError, "item[0] in the tuple at line_fmt_tuples[%zd] list must be an integer, not %.200s",
                         i, Py_TYPE(py_level)->tp_name);
            goto fail;
        }
        line_level = PyInt_AsLong(py_level);
        if (line_level < 0) {
            PyErr_Format(PyExc_TypeError, "item[0] in the tuple at line_fmt_tuples[%zd] list must be a non-negative integer, not %ld",
                         i, line_level);
            goto fail;
        }

        label_len = value_len = 0;
        if (py_label) {
            if ((py_string_utf8 = PyString_UTF8(py_label, "label")) == NULL) {
                PyErr_Format(PyExc_TypeError, "item[1] in the tuple at line_fmt_tuples[%zd] list must be a string, not %.200s",
                             i, Py_TYPE(py_label)->tp_name);
                goto fail;
            }
            if (PyString_AsStringAndSize(py_string_utf8, &label, &label_len) == -1) {
                goto fail;
            }
        }
        Py_CLEAR(py_string_utf8);

        if (py_value) {
            if ((py_string_utf8 = PyString_UTF8(py_value, "value")) == NULL) {
                PyErr_Format(PyExc_TypeError, "item[2] in the tuple at line_fmt_tuples[%zd] list must be a string, not %.200s",
                             i, Py_TYPE(py_value)->tp_name);
                goto fail;
            }
            if (PyString_AsStringAndSize(py_string_utf8, &value, &value_len) == -1) {
                goto fail;
            }
        }
        Py_CLEAR(py_string_utf8);

        /* Cache the length information */
        line_info[i].label_len = label_len;
        line_info[i].value_len = value_len;
        line_info[i].justification_len = 0;
        line_info[i].indent_len = line_level * indent_len;
    }

    /*
     * Step 2: Locate labels and values that appear on consecutive
     * lines at the same indentation level. Compute the alignment for
     * values such that values all line up in the same column.
     *
     * We consider only lines that have both a label and a value for
     * the purpose of computing the alignment, if a line has only a
     * label we ignore it when establishing value alignment.
     *
     * A change in the indendation level resets the alignment.
     */
    for (i = 0; i < num_lines;) {
        cur_indent_len = line_info[i].indent_len;
        if (line_info[i].value_len) {
            max_align = line_info[i].label_len;
        } else {
            max_align = 0;
        }

        /*
         * Search forward for consecutive lines that share the same
         * indendation level.  If the line has value then use it's
         * label to compute the maximum width of all labels in this
         * group of lines.
         */
        for (j = i+1; j < num_lines && cur_indent_len == line_info[j].indent_len; j++) {
            if (line_info[j].value_len) {
                if (line_info[j].label_len > max_align) {
                    max_align = line_info[j].label_len;
                }
            }
        }

        /*
         * Now we know the maximum width of all labels in this group
         * of lines.  We always provide 1 space between a label and
         * it's value so we add 1 to the maximum label width, this
         * becomes our column for value alignment.
         *
         * If there were no values in this group of lines max_align
         * will be zero and we won't be doing any value alignment.
         */
        if (max_align) {
            max_align += 1;
        }

        /*
         * Now that we know the alignment column go back and compute
         * how much space to add at the end of each label to hit the
         * alignment column when we append the value.
         */
        for (k = i; k < j; k++) {
            if (line_info[k].value_len) { /* Only justify if there is a value */
                line_info[k].justification_len = max_align - line_info[k].label_len;
            }
        }

        /* This group of lines is processed, advance to the next group. */
        i = j;
    }

    /*
     * Step 3: We now know how many characters every line consumes,
     * compute the total buffer size required and allocate it.
     */
    formatted_str_len = 0;
    for (i = 0; i < num_lines; i++) {
        cur_formatted_line_len = line_info[i].indent_len +
                                 line_info[i].label_len +
                                 line_info[i].justification_len +
                                 line_info[i].value_len + 1; /* +1 for newline */
        formatted_str_len += cur_formatted_line_len;
    }

    if (num_lines > 0) formatted_str_len -= 1; /* last line doesn't get a new line appended */
    if ((py_formatted_str = PyString_FromStringAndSize(NULL, formatted_str_len)) == NULL) {
        goto fail;
    }

    formatted_str = PyString_AsString(py_formatted_str);
    dst = formatted_str;

    /*
     * Step 4: For each line: Insert the indent. If it has a label
     * insert the label. If it has a value insert the justification to
     * align the values, then insert the value. Finally append a
     * newline (except for the last line).
     */
    for (i = 0; i < num_lines; i++) {
        py_label = NULL;
        label = NULL;

        py_value = NULL;
        value = NULL;

        py_line_fmt_tuple = PyList_GetItem(py_lines, i);

        cur_indent_len = line_info[i].indent_len;
        label_len = line_info[i].label_len;
        value_len = line_info[i].value_len;
        justification_len = line_info[i].justification_len;

        /* Insert the indent */
        for (j = 0; j < cur_indent_len; j++) *dst++ = ' ';

        /* Insert the label */
        if (label_len) {
            py_label = PyTuple_GetItem(py_line_fmt_tuple, 1);
            py_string_utf8 = PyString_UTF8(py_label, "label");
            label = PyString_AsString(py_string_utf8);

            for (src = label, src_end = label + label_len; src < src_end; *dst++ = *src++);

            Py_CLEAR(py_string_utf8);
        }

        /* Insert the alignment justification for the value */
        for (j = 0; j < justification_len; j++) *dst++ = ' ';

        /* Insert the value */
        if (value_len) {
            py_value = PyTuple_GetItem(py_line_fmt_tuple, 2);
            py_string_utf8 = PyString_UTF8(py_value, "value");
            value = PyString_AsString(py_string_utf8);

            for (src = value, src_end = value + value_len; src < src_end; *dst++ = *src++);

            Py_CLEAR(py_string_utf8);
        }

        /* Add a new line, except for the last line */
        if (i < num_lines-1)
            *dst++ = '\n';
    }

    /*
     * Done. Sanity check we've written exactly the buffer we allocated.
     */
    assert(formatted_str + PyString_Size(py_formatted_str) == dst);
    return py_formatted_str;

 fail:
    Py_CLEAR(py_string_utf8);
    PyMem_Free(line_info);
    Py_XDECREF(py_formatted_str);
    return NULL;
}



/* ========================================================================== */

static PyObject *
raw_data_to_hex(unsigned char *data, int data_len, int octets_per_line, char *separator)
{
    int separator_len = 0;
    char *separator_end = NULL;
    char *src=NULL, *dst=NULL;
    int line_size = 0;
    unsigned char octet = 0;
    int num_lines = 0;
    PyObject *lines = NULL;
    PyObject *line = NULL;
    int line_number, i, j;
    int num_octets = 0;

    if (octets_per_line < 0)
        octets_per_line = 0;

    if (!separator)
        separator = "";

    separator_len = strlen(separator);
    separator_end = separator + separator_len;

    if (octets_per_line == 0) {
        num_octets = data_len;
        line_size = (num_octets * 2) + ((num_octets-1) * separator_len);
        if (line_size < 0) line_size = 0;

        if ((line = PyString_FromStringAndSize(NULL, line_size)) == NULL) {
            return NULL;
        }
        dst = PyString_AS_STRING(line);
        for (i = 0; i < data_len; i++) {
            octet = data[i];
            *dst++ = hex_chars[(octet & 0xF0) >> 4];
            *dst++ = hex_chars[octet & 0xF];
            if (i < data_len-1)
                for (src = separator; src < separator_end; *dst++ = *src++);
        }
        return line;
    } else {
        num_lines = (data_len + octets_per_line - 1) / octets_per_line;
        if (num_lines < 0) num_lines = 0;

        if ((lines = PyList_New(num_lines)) == NULL) {
            return NULL;
        }

        for (i = line_number = 0; i < data_len;) {
            num_octets = data_len - i;
            if (num_octets > octets_per_line) {
                num_octets = octets_per_line;
                line_size = num_octets*(2+separator_len);
            } else {
                line_size = (num_octets * 2) + ((num_octets-1) * separator_len);
            }

            if (line_size < 0) line_size = 0;
            if ((line = PyString_FromStringAndSize(NULL, line_size)) == NULL) {
                Py_DECREF(lines);
                return NULL;
            }
            dst = PyString_AS_STRING(line);
            for (j = 0; j < num_octets && i < data_len; i++, j++) {
                octet = data[i];
                *dst++ = hex_chars[(octet & 0xF0) >> 4];
                *dst++ = hex_chars[octet & 0xF];
                if (i < data_len-1)
                    for (src = separator; src < separator_end; *dst++ = *src++);
            }
            PyList_SetItem(lines, line_number++, line);
        }
        return lines;
    }
}

/*
 * Given a Kerberos ticket flags bitmask return a sorted list
 * compromised of the names of each flag enabled in the bitmask.
 */
static PyObject *
ticket_flags_str(krb5_flags flags)
{
    PyObject *py_flags = NULL;
    PyObject *py_flag = NULL;

    if ((py_flags = PyList_New(0)) == NULL)
        return NULL;

    if (flags & TKT_FLG_FORWARDABLE) {
        flags &= ~TKT_FLG_FORWARDABLE;
	if ((py_flag = PyString_FromString("FORWARDABLE")) == NULL) {
            Py_DECREF(py_flags);
            return NULL;
        }
        PyList_Append(py_flags, py_flag);
	Py_DECREF(py_flag);
    }
    if (flags & TKT_FLG_FORWARDED) {
        flags &= ~TKT_FLG_FORWARDED;
	if ((py_flag = PyString_FromString("FORWARDED")) == NULL) {
            Py_DECREF(py_flags);
            return NULL;
        }
        PyList_Append(py_flags, py_flag);
	Py_DECREF(py_flag);
    }
    if (flags & TKT_FLG_PROXIABLE) {
        flags &= ~TKT_FLG_PROXIABLE;
	if ((py_flag = PyString_FromString("PROXIABLE")) == NULL) {
            Py_DECREF(py_flags);
            return NULL;
        }
        PyList_Append(py_flags, py_flag);
	Py_DECREF(py_flag);
    }
    if (flags & TKT_FLG_PROXY) {
        flags &= ~TKT_FLG_PROXY;
	if ((py_flag = PyString_FromString("PROXY")) == NULL) {
            Py_DECREF(py_flags);
            return NULL;
        }
        PyList_Append(py_flags, py_flag);
	Py_DECREF(py_flag);
    }
    if (flags & TKT_FLG_MAY_POSTDATE) {
        flags &= ~TKT_FLG_MAY_POSTDATE;
	if ((py_flag = PyString_FromString("MAY_POSTDATE")) == NULL) {
            Py_DECREF(py_flags);
            return NULL;
        }
        PyList_Append(py_flags, py_flag);
	Py_DECREF(py_flag);
    }
    if (flags & TKT_FLG_POSTDATED) {
        flags &= ~TKT_FLG_POSTDATED;
	if ((py_flag = PyString_FromString("POSTDATED")) == NULL) {
            Py_DECREF(py_flags);
            return NULL;
        }
        PyList_Append(py_flags, py_flag);
	Py_DECREF(py_flag);
    }
    if (flags & TKT_FLG_INVALID) {
        flags &= ~TKT_FLG_INVALID;
	if ((py_flag = PyString_FromString("INVALID")) == NULL) {
            Py_DECREF(py_flags);
            return NULL;
        }
        PyList_Append(py_flags, py_flag);
	Py_DECREF(py_flag);
    }
    if (flags & TKT_FLG_RENEWABLE) {
        flags &= ~TKT_FLG_RENEWABLE;
	if ((py_flag = PyString_FromString("RENEWABLE")) == NULL) {
            Py_DECREF(py_flags);
            return NULL;
        }
        PyList_Append(py_flags, py_flag);
	Py_DECREF(py_flag);
    }
    if (flags & TKT_FLG_INITIAL) {
        flags &= ~TKT_FLG_INITIAL;
	if ((py_flag = PyString_FromString("INITIAL")) == NULL) {
            Py_DECREF(py_flags);
            return NULL;
        }
        PyList_Append(py_flags, py_flag);
	Py_DECREF(py_flag);
    }
    if (flags & TKT_FLG_PRE_AUTH) {
        flags &= ~TKT_FLG_PRE_AUTH;
	if ((py_flag = PyString_FromString("PRE_AUTH")) == NULL) {
            Py_DECREF(py_flags);
            return NULL;
        }
        PyList_Append(py_flags, py_flag);
	Py_DECREF(py_flag);
    }
    if (flags & TKT_FLG_HW_AUTH) {
        flags &= ~TKT_FLG_HW_AUTH;
	if ((py_flag = PyString_FromString("HW_AUTH")) == NULL) {
            Py_DECREF(py_flags);
            return NULL;
        }
        PyList_Append(py_flags, py_flag);
	Py_DECREF(py_flag);
    }
    if (flags & TKT_FLG_TRANSIT_POLICY_CHECKED) {
        flags &= ~TKT_FLG_TRANSIT_POLICY_CHECKED;
	if ((py_flag = PyString_FromString("TRANSIT_POLICY_CHECKED")) == NULL) {
            Py_DECREF(py_flags);
            return NULL;
        }
        PyList_Append(py_flags, py_flag);
	Py_DECREF(py_flag);
    }
    if (flags & TKT_FLG_OK_AS_DELEGATE) {
        flags &= ~TKT_FLG_OK_AS_DELEGATE;
	if ((py_flag = PyString_FromString("OK_AS_DELEGATE")) == NULL) {
            Py_DECREF(py_flags);
            return NULL;
        }
        PyList_Append(py_flags, py_flag);
	Py_DECREF(py_flag);
    }
    if (flags & TKT_FLG_ENC_PA_REP) {
        flags &= ~TKT_FLG_ENC_PA_REP;
	if ((py_flag = PyString_FromString("ENC_PA_REP")) == NULL) {
            Py_DECREF(py_flags);
            return NULL;
        }
        PyList_Append(py_flags, py_flag);
	Py_DECREF(py_flag);
    }
    if (flags & TKT_FLG_ANONYMOUS) {
        flags &= ~TKT_FLG_ANONYMOUS;
	if ((py_flag = PyString_FromString("ANONYMOUS")) == NULL) {
            Py_DECREF(py_flags);
            return NULL;
        }
        PyList_Append(py_flags, py_flag);
	Py_DECREF(py_flag);
    }

    if (flags) {
        if ((py_flag = PyString_FromFormat("unknown bit flags %#x", flags)) == NULL) {
            Py_DECREF(py_flags);
            return NULL;
        }
        PyList_Append(py_flags, py_flag);
	Py_DECREF(py_flag);
    }

    if (PyList_Sort(py_flags) == -1) {
            Py_DECREF(py_flags);
            return NULL;
    }

    return py_flags;
}

/* ========================================================================== */

static PyObject *
set_krb_error(krb5_error_code error_code, const char *format, ...)
{
    va_list vargs;
    PyObject *v;
    const char *error_desc = NULL;
    PyObject *detail = NULL;
    krb5_context current_context = NULL;

    /* Failsafe for errors */
    if ((current_context = get_current_context()) == NULL) {
        krb5_init_context(&current_context);
    }

    if (format) {
#ifdef HAVE_STDARG_PROTOTYPES
	va_start(vargs, format);
#else
	va_start(vargs);
#endif
	detail = PyString_FromFormatV(format, vargs);
	va_end(vargs);
    }

    error_desc = krb5_get_error_message(current_context, error_code);

    if (detail) {
        v = Py_BuildValue("(isS)", error_code, error_desc, detail);
	Py_DECREF(detail);
    } else {
        v = Py_BuildValue("(is)", error_code, error_desc);
    }
    if (v != NULL) {
        PyErr_SetObject(KRB_Exception, v);
        Py_DECREF(v);
    }

    if (error_desc) krb5_free_error_message(current_context, error_desc);

    return NULL;
}

static krb5_context
get_current_context()
{
    PyObject *py_context = NULL;

    if ((py_context = get_thread_local(CURRENT_CONTEXT_NAME)) == NULL) {
        PyErr_SetString(PyExc_RuntimeError, "No current context set, need to call set_current_context()");
        return NULL;
    }

    if (!PyContext_Check(py_context)) {
        PyErr_Format(PyExc_RuntimeError, "current context thread local variable must be %s.200s type, not %.200s",
                     Py_TYPE(&ContextType)->tp_name, Py_TYPE(py_context)->tp_name);
        return NULL;
    }

    return ((Context *)py_context)->context;
}

static krb5_context
get_current_context_no_error()
{
    PyObject *py_context = NULL;

    if ((py_context = get_thread_local(CURRENT_CONTEXT_NAME)) == NULL) {
        return NULL;
    }

    if (!PyContext_Check(py_context)) {
        return NULL;
    }

    return ((Context *)py_context)->context;
}

/* returns new reference or NULL on error */
PyObject *
PyString_UTF8(PyObject *obj, char *name)
{
    if (PyString_Check(obj)) {
        Py_INCREF(obj);
        return obj;
    }

    if  (PyUnicode_Check(obj)) {
        return PyUnicode_AsUTF8String(obj);
    }

    PyErr_Format(PyExc_TypeError, "%s must be a string, not %.200s",
                 name, Py_TYPE(obj)->tp_name);
    return NULL;
}

static PyObject *
datetime_from_timestamp(long t)
{
    PyObject *args = NULL;
    PyObject *py_datetime = NULL;

    args = Py_BuildValue("(i)", t);
    py_datetime = PyDateTime_FromTimestamp(args);
    Py_DECREF(args);
    return py_datetime;
}


static time_t
timestamp_from_datetime(PyObject *py_datetime)
{
    PyObject *py_time_tuple = NULL;
    PyObject *py_timestamp = NULL;
    double    timestamp_double;
    time_t    timestamp;

    if (!PyDateTime_Check(py_datetime)) {
        PyErr_SetString(PyExc_TypeError, "Expected datetime.datetime object");
        return (time_t)-1;
    }

    /*
     * To convert DateTime object, dt, to a timestamp in Python
     * time.mktime(dt.timetuple())
     * The following code mimics that process.
     */

    /* Get a timetuple from the DateTime object */
    if ((py_time_tuple = PyObject_CallMethod(py_datetime, "timetuple", "O")) == NULL) {
        return (time_t)-1;
    }

    /* Call time.mktime() on the timetuple, free the timetuple */
    if ((py_timestamp = PyObject_CallMethod(time_module, "mktime", "(O)", py_time_tuple)) == NULL) {
        Py_DECREF(py_time_tuple);
        return (time_t)-1;
    }
    Py_DECREF(py_time_tuple);

    /*
     * time.mktime() returns a Python float (internally a double).
     * Get the timestamp as a double, free the timestamp
     */
    timestamp_double = PyFloat_AsDouble(py_timestamp);
    Py_DECREF(py_timestamp);

    /*
     * Convert the double to a time_t.  We should call
     * _PyTime_DoubleToTimet() to check for underflow/overflow which
     * is defined in timefuncs.h and implemented in timemodule.c but
     * there is no way to link it, it's not exposed as CAPI, so
     * instead just cast.
     */

    timestamp = (time_t)timestamp_double;
    if (timestamp == (time_t)-1 && PyErr_Occurred()) {
        return (time_t) -1;
    }

    return timestamp;
}

static time_t
time_t_from_py_value(PyObject *value, const char *name)
{
    time_t timestamp = -1;

    if (PyInt_Check(value)) {
        timestamp = PyInt_AsLong(value);
    } else if (PyLong_Check(value)) {
        timestamp = PyLong_AsLong(value);
    } else if (PyFloat_Check(value)) {
        double timestamp_double;

        timestamp_double = PyFloat_AsDouble(value);
        timestamp = timestamp_double;
    } else if (PyDateTime_Check(value)) {
        timestamp = timestamp_from_datetime(value);
        if (timestamp == (time_t)-1 && PyErr_Occurred()) {
            return -1;
        }
    } else {
        if (name == NULL) {
            name = "timestamp";
        }
        PyErr_Format(PyExc_TypeError, "%s must be float, int or datetime, not %.200s",
                     name, Py_TYPE(value)->tp_name);
        return -1;
    }
    return timestamp;
}

static time_t
timestamp_now()
{
    PyObject *py_timestamp = NULL;
    double    timestamp_double;
    time_t    timestamp;

    if ((py_timestamp = PyObject_CallMethod(time_module, "time", NULL)) == NULL) {
        return (time_t)-1;
    }
    timestamp_double = PyFloat_AsDouble(py_timestamp);
    Py_DECREF(py_timestamp);
    timestamp = timestamp_double;
    return timestamp;
}

static int
_AddIntConstantWithLookup(PyObject *module, const char *name, long value, const char *prefix,
                          PyObject *name_to_value, PyObject *value_to_name)
{
    PyObject *module_dict;
    PyObject *py_name = NULL;
    PyObject *py_name_sans_prefix = NULL;
    PyObject *py_lower_name = NULL;
    PyObject *py_value = NULL;

    if (!PyModule_Check(module)) {
        PyErr_SetString(PyExc_TypeError, "_AddIntConstantWithLookup() needs module as first arg");
        return -1;
    }

    if ((module_dict = PyModule_GetDict(module)) == NULL) {
        PyErr_Format(PyExc_SystemError, "module '%s' has no __dict__",
                     PyModule_GetName(module));
        return -1;
    }

    if ((py_name = PyString_FromString(name)) == NULL) {
        return -1;
    }

    if ((py_lower_name = PyObject_CallMethod(py_name, "lower", NULL)) == NULL) {
        Py_DECREF(py_name);
        return -1;
    }

    if ((py_value = PyInt_FromLong(value)) == NULL) {
        Py_DECREF(py_name);
        Py_DECREF(py_lower_name);
        return -1;
    }

    if (PyDict_SetItem(module_dict, py_name, py_value) != 0) {
        Py_DECREF(py_name);
        Py_DECREF(py_lower_name);
        Py_DECREF(py_value);
        return -1;
    }

    if (PyDict_SetItem(value_to_name, py_value, py_name) != 0) {
        Py_DECREF(py_name);
        Py_DECREF(py_lower_name);
        Py_DECREF(py_value);
        return -1;
    }

    if (PyDict_SetItem(name_to_value, py_lower_name, py_value) != 0) {
        Py_DECREF(py_name);
        Py_DECREF(py_lower_name);
        Py_DECREF(py_value);
        return -1;
    }

    if (prefix) {
        size_t prefix_len = strlen(prefix);

        if (strlen(name) > prefix_len &&
            strncasecmp(prefix, name, prefix_len) == 0) {

            if ((py_name_sans_prefix = PyString_FromString(PyString_AS_STRING(py_lower_name) + prefix_len)) == NULL) {
                Py_DECREF(py_name);
                Py_DECREF(py_lower_name);
                Py_DECREF(py_value);
                return -1;
            }

            if (PyDict_SetItem(name_to_value, py_name_sans_prefix, py_value) != 0) {
                Py_DECREF(py_name);
                Py_DECREF(py_name_sans_prefix);
                Py_DECREF(py_lower_name);
                Py_DECREF(py_value);
                return -1;
            }
        }
    }

    Py_DECREF(py_name);
    Py_XDECREF(py_name_sans_prefix);
    Py_DECREF(py_lower_name);
    Py_DECREF(py_value);
    return 0;
}

/* Set object in thread local storage under name, return 0 for success, -1 on failure */
static int
set_thread_local(const char *name, PyObject *obj)
{
    PyObject *tdict;
    PyObject *thread_local_dict;

    /* Get this threads thread local dict */
    if ((tdict = PyThreadState_GetDict()) == NULL) {
        PyErr_SetString(PyExc_RuntimeError, "cannot get thread state");
        return -1;
    }

    /* Get our module's thread local dict */
    if ((thread_local_dict = PyDict_GetItemString(tdict, KRB_THREAD_LOCAL_KEY)) == NULL) {
        /*
         * Our thread local dict does not yet exist so create it
         * and set it in the thread's thread local dict.
         */
        if ((thread_local_dict = PyDict_New()) == NULL) {
            PyErr_SetString(PyExc_RuntimeError, "cannot create thread local data dict");
            return -1;
        }
        if (PyDict_SetItemString(tdict, KRB_THREAD_LOCAL_KEY, thread_local_dict) < 0) {
            Py_DECREF(thread_local_dict);
            PyErr_SetString(PyExc_RuntimeError, "cannot store thread local data dict");
            return -1;
        }
    }

    if (PyDict_SetItemString(thread_local_dict, name, obj) < 0) {
        PyErr_SetString(PyExc_RuntimeError, "cannot store object in thread local data dict");
        return -1;
    }

    return 0;
}

/* Same return behavior as PyDict_GetItem() */
static PyObject *
get_thread_local(const char *name)
{
    PyObject *tdict;
    PyObject *thread_local_dict;

    /* Get this threads thread local dict */
    if ((tdict = PyThreadState_GetDict()) == NULL) {
        PyErr_SetString(PyExc_RuntimeError, "cannot get thread state");
        return NULL;
    }

    /* Get our module's thread local dict */
    if ((thread_local_dict = PyDict_GetItemString(tdict, KRB_THREAD_LOCAL_KEY)) == NULL) {
        /*
         * Our thread local dict does not yet exist thus the item can't be
         * in the dict, thus it's not found.
         */
        return NULL;
    }

    return PyDict_GetItemString(thread_local_dict, name);
}


/*
 * If obj is None store NULL value in param.
 *
 * If str object increment ref count, store the PyString object in
 * param.
 *
 * If unicode object, generate new PyString object by encoding to
 * UTF-8 and store it in param.
 *
 * Note: param *MUST* be freed with Py_XDECREF!
 */
static int
string_or_none_convert(PyObject *obj, PyObject **param)
{
    PyObject *result = NULL;

    if (PyNone_Check(obj)) {
        *param = NULL;
        return 1;
    }

    if (PyString_Check(obj)) {
        result = obj;
        Py_INCREF(result);
        *param = result;
        return 1;
    }

    if  (PyUnicode_Check(obj)) {
        if ((result = PyUnicode_AsUTF8String(obj)) == NULL) {
            *param = NULL;
            return 0;
        }
        Py_INCREF(result);
        *param = result;
        return 1;
    }

    PyErr_Format(PyExc_TypeError, "must be basestring or None, not %.50s",
                 Py_TYPE(obj)->tp_name);
    return 0;
}

/*
 * If obj is None, do not store anything, leave param unmodified.
 * If obj is PyInt store integer value in param.
 */
static int
int_or_none_convert(PyObject *obj, int *param)
{
    if (PyNone_Check(obj)) {
        return 1;
    }

    if (PyInt_Check(obj)) {
        *param = PyInt_AsLong(obj);
        return 1;
    }

    PyErr_Format(PyExc_TypeError, "must be int or None, not %.50s",
                 Py_TYPE(obj)->tp_name);
    return 0;
}

/* ========================================================================== */

static PyObject *
addrtype_to_pystr(krb5_addrtype addrtype)
{
    char *name = NULL;
    char *local = NULL;

    switch(addrtype) {
    case ADDRTYPE_INET:     name = "INET";     break;
    case ADDRTYPE_CHAOS:    name = "CHAOS";    break;
    case ADDRTYPE_XNS:      name = "XNS";      break;
    case ADDRTYPE_ISO:      name = "ISO";      break;
    case ADDRTYPE_DDP:      name = "DDP";      break;
    case ADDRTYPE_NETBIOS:  name = "NETBIOS";  break;
    case ADDRTYPE_INET6:    name = "INET6";    break;
    case ADDRTYPE_ADDRPORT: name = "ADDRPORT"; break;
    case ADDRTYPE_IPPORT:   name = "IPPORT";   break;
    default:
        return PyString_FromFormat("unknown (%0x)", addrtype);
        break;
    }

    if (ADDRTYPE_IS_LOCAL(addrtype)) {
        local = "Local ";
    } else {
        local = "";
    }

    return PyString_FromFormat("%s%s", local, name);
}

static PyObject *
krb_enctype_to_pystr(long enctype)
{
    PyObject *py_value;
    PyObject *py_name;

    if ((py_value = PyInt_FromLong(enctype)) == NULL) {
        PyErr_SetString(PyExc_MemoryError, "unable to create object");
        return NULL;
    }

    if ((py_name = PyDict_GetItem(krb_enctype_value_to_name, py_value)) == NULL) {
        Py_DECREF(py_value);
	PyErr_Format(PyExc_KeyError, "enctype name not found: %ld", enctype);
        return NULL;
    }

    Py_DECREF(py_value);
    Py_INCREF(py_name);

    return py_name;
}

PyDoc_STRVAR(krb_enctype_name_doc,
"krb_enctype_name(enctype) -> string\n\
\n\
:Parameters:\n\
    enctype : int\n\
        ENCTYPE_* constant\n\
\n\
Given a ENCTYPE_* constant\n\
return it's name as a string\n\
");
static PyObject *
krb_enctype_name(PyObject *self, PyObject *args)
{
    unsigned long enctype;

    TraceMethodEnter(self);

    if (!PyArg_ParseTuple(args, "k:krb_enctype_name", &enctype))
        return NULL;

    return krb_enctype_to_pystr(enctype);
}

PyDoc_STRVAR(krb_enctype_from_name_doc,
"krb_enctype_from_name(name) -> int\n\
\n\
:Parameters:\n\
    name : string\n\
        name of ENCTYPE_* constant\n\
\n\
Given the name of a ENCTYPE_* constant\n\
return it's integer constant\n\
The string comparison is case insensitive and will match with\n\
or without the ENCTYPE\\_ prefix\n\
");
static PyObject *
krb_enctype_from_name(PyObject *self, PyObject *args)
{
    PyObject *py_name;
    PyObject *py_lower_name;
    PyObject *py_value;

    TraceMethodEnter(self);

    if (!PyArg_ParseTuple(args, "S:krb_enctype_from_name", &py_name))
        return NULL;

    if ((py_lower_name = PyObject_CallMethod(py_name, "lower", NULL)) == NULL) {
        return NULL;
    }

    if ((py_value = PyDict_GetItem(krb_enctype_name_to_value, py_lower_name)) == NULL) {
	PyErr_Format(PyExc_KeyError, "enctype name not found: %s", PyString_AsString(py_name));
        Py_DECREF(py_lower_name);
        return NULL;
    }

    Py_DECREF(py_lower_name);
    Py_INCREF(py_value);

    return py_value;
}

/* ========================================================================== */
/* ============================= Address Class ============================== */
/* ========================================================================== */

static PyObject *
Address_get_nameinfo(Address *self, bool resolve)
{
    struct sockaddr_storage ss;
    socklen_t sock_addr_len;
    socklen_t net_addr_len;
    int sock_error = 0;
    char host[NI_MAXHOST];
    int flags = 0;

    memset (&ss, 0, sizeof (ss));

    switch (self->address.addrtype) {
    case ADDRTYPE_INET:
        {
            struct sockaddr_in *sinp = (struct sockaddr_in *)&ss;
            sock_addr_len = sizeof(struct sockaddr_in);
            net_addr_len = sizeof(struct in_addr);

            if (self->address.length != net_addr_len) {
                PyObject *py_addrtype = addrtype_to_pystr(self->address.addrtype);

                PyErr_Format(PyExc_ValueError, _("corrupt address, addrtype %s has length %d, expected %d)"),
                             PyString_AsString(py_addrtype), self->address.length, net_addr_len);
                Py_XDECREF(py_addrtype);

                return NULL;
            }
            sinp->sin_family = AF_INET;
#ifdef	HAVE_SOCKADDR_SA_LEN
            sinp->sin_len = xxx;
#endif
            memcpy(&sinp->sin_addr, self->address.contents, self->address.length);
        }
        break;
    case ADDRTYPE_INET6:
        {
            struct sockaddr_in6 *sinp = (struct sockaddr_in6 *)&ss;
            sock_addr_len = sizeof(struct sockaddr_in6);
            net_addr_len = sizeof(struct in6_addr);

            if (self->address.length != net_addr_len) {
                PyObject *py_addrtype = addrtype_to_pystr(self->address.addrtype);

                PyErr_Format(PyExc_ValueError, _("corrupt address, addrtype %s has length %d, expected %d)"),
                             PyString_AsString(py_addrtype), self->address.length, net_addr_len);
                Py_XDECREF(py_addrtype);

                return NULL;
            }
            sinp->sin6_family = AF_INET6;
#ifdef	HAVE_SOCKADDR_SA_LEN
            sinp->sin_len = xxx;
#endif
            memcpy(&sinp->sin6_addr, self->address.contents, self->address.length);
        }
        break;
    default:
        PyErr_Format(PyExc_ValueError, _("unknown addrtype %d"), self->address.addrtype);
        return NULL;
    }

    if (resolve) {
        flags |= NI_NAMEREQD;
    } else {
        flags |= NI_NUMERICHOST;
    }

    host[0] = 0;
    if ((sock_error = getnameinfo ((struct sockaddr *)&ss, sock_addr_len, host, sizeof(host), 0, 0, flags))) {
        if (sock_error == EAI_NONAME) {
            /* If we can't resolve the name it's not an error */
            strncpy(host, "<unavilable>", sizeof(host));
        } else {
            PyObject *py_addrtype = addrtype_to_pystr(self->address.addrtype);

            PyErr_Format(PyExc_ValueError, _("unprintable address, addrtype %s, error %s)"),
                         PyString_AsString(py_addrtype), gai_strerror(sock_error));
            Py_XDECREF(py_addrtype);

            return NULL;
        }
    }

    return PyString_FromString(host);
}

/* >>> Address Attribute Access <<< */

static PyObject *
Address_get_addrtype(Address *self, void *closure)
{
    TraceMethodEnter(self);

    return PyInt_FromLong(self->address.addrtype);
}

static int
Address_set_addrtype(Address *self, PyObject *value, void *closure)
{
    krb5_context current_context = NULL;

    TraceMethodEnter(self);

    if ((current_context = get_current_context()) == NULL) {
        return -1;
    }

    if (value == NULL) {
        PyErr_SetString(PyExc_TypeError, "Cannot delete the addrtype attribute");
        return -1;
    }

    if (!PyInt_Check(value)) {
        PyErr_SetString(PyExc_TypeError, "The attribute value must be a int");
        return -1;
    }

    self->address.addrtype = PyInt_AsLong(value);

    return 0;
}

static PyObject *
Address_get_data(Address *self, void *closure)
{
    TraceMethodEnter(self);

    return PyString_FromStringAndSize((const char *)self->address.contents, self->address.length);
}

static int
Address_set_data(Address *self, PyObject *value, void *closure)
{
    char *data = NULL;
    Py_ssize_t data_len = 0;

    TraceMethodEnter(self);

    if (value == NULL) {
        PyErr_SetString(PyExc_TypeError, "Cannot delete the data attribute");
        return -1;
    }

    if (!PyString_Check(value)) {
        PyErr_SetString(PyExc_TypeError, "The attribute value must be a string");
        return -1;
    }

    if (PyString_AsStringAndSize(value, &data, &data_len)) {
        return -1;
    }

    if (Address_init_from_net_addr(self, self->address.addrtype, data, data_len)) {
        return -1;
    }

    return 0;
}

static PyObject *
Address_get_length(Address *self, void *closure)
{
    TraceMethodEnter(self);

    return PyInt_FromLong(self->address.addrtype);
}

static PyObject *
Address_get_numeric(Address *self, void *closure)
{
    TraceMethodEnter(self);

    return Address_get_nameinfo(self, false);
}

static PyObject *
Address_get_name(Address *self, void *closure)
{
    TraceMethodEnter(self);

    return Address_get_nameinfo(self, true);
}

static
PyGetSetDef Address_getseters[] = {
    {"addrtype", (getter)Address_get_addrtype, (setter)Address_set_addrtype, "network address type, i.e. ADDRTYPE_INET, ADDRTYPE_INET6", NULL},
    {"data",     (getter)Address_get_data,   (setter)Address_set_data,       "address data", NULL},
    {"length",   (getter)Address_get_length, (setter)NULL,                   "number of octets in address data", NULL},
    {"numeric",  (getter)Address_get_length, (setter)NULL,                   "numeric ip address as string", NULL},
    {"name",     (getter)Address_get_length, (setter)NULL,                   "DNS name as string", NULL},
    {NULL}  /* Sentinel */
};

static PyMemberDef Address_members[] = {
    {NULL}  /* Sentinel */
};

/* >>> Address Class Methods <<< */

PyDoc_STRVAR(Address_func_name_doc,
"func_name() -> \n\
\n\
:parameters:\n\
    arg1 : object\n\
        xxx\n\
:returns:\n\
    xxx\n\
\n\
xxx\n\
");

static PyObject *
Address_func_name(Address *self, PyObject *args, PyObject *kwds)
{
    static char *kwlist[] = {"arg1", NULL};
    PyObject *arg;
    krb5_context current_context = NULL;

    TraceMethodEnter(self);

    if ((current_context = get_current_context()) == NULL) {
        return NULL;
    }

    if (!PyArg_ParseTupleAndKeywords(args, kwds, "O|i:func_name", kwlist,
                                     &arg))
        return NULL;

    return NULL;
}

static PyObject *
Address_format_lines(Address *self, PyObject *args, PyObject *kwds)
{
    static char *kwlist[] = {"level", NULL};
    int level = 0;
    PyObject *lines = NULL;
    PyObject *obj = NULL;

    TraceMethodEnter(self);

    if (!PyArg_ParseTupleAndKeywords(args, kwds, "|i:format_lines", kwlist, &level))
        return NULL;

    if ((lines = PyList_New(0)) == NULL) {
        return NULL;
    }

    if ((obj = addrtype_to_pystr(self->address.addrtype)) == NULL) goto fail;
    FMT_OBJ_AND_APPEND(lines, _("Addrtype"), obj, level, fail);
    Py_CLEAR(obj);

    if (self->address.addrtype == ADDRTYPE_INET ||
        self->address.addrtype == ADDRTYPE_INET6) {
        if ((obj = Address_get_name(self, NULL)) == NULL) goto fail;
        FMT_OBJ_AND_APPEND(lines, _("Name"), obj, level, fail);
        Py_CLEAR(obj);

        if ((obj = Address_get_numeric(self, NULL)) == NULL) goto fail;
        FMT_OBJ_AND_APPEND(lines, _("Address"), obj, level, fail);
        Py_CLEAR(obj);
    } else {
        FMT_LABEL_AND_APPEND(lines, _("<unable to interpret addrtype>"), level, fail);
    }

    return lines;

 fail:
    Py_XDECREF(obj);
    Py_XDECREF(lines);
    return NULL;
}

static PyObject *
Address_format(Address *self, PyObject *args, PyObject *kwds)
{
    TraceMethodEnter(self);

    return format_from_lines((format_lines_func)Address_format_lines, (PyObject *)self, args, kwds);
}

static PyObject *
Address_str(Address *self)
{
    return Address_format(self, empty_tuple, NULL);
}


/* >>> Address Class Construction <<< */

static PyObject *
Address_new(PyTypeObject *type, PyObject *args, PyObject *kwds)
{
    Address *self;

    TraceObjNewEnter(type);

    if ((self = (Address *)type->tp_alloc(type, 0)) == NULL) {
        return NULL;
    }

    memset(&self->address, 0, sizeof(self->address));

    TraceObjNewLeave(self);
    return (PyObject *)self;
}

static void
Address_dealloc(Address* self)
{
    TraceMethodEnter(self);

    if (self->address.contents) {
        PyMem_Free(self->address.contents);
    }

    self->ob_type->tp_free((PyObject*)self);
}

PyDoc_STRVAR(Address_doc,
"Address(host=None, family=AF_UNSPEC, addrtype=0, data=None)\n\
\n\
:parameters:\n\
    host : string\n\
        Used when resolving a host name or host numeric address,\n\
        will be resolved by getaddrinfo()\n\
    family : int\n\
        Used when resolving a host name, the inet family (e.g. AF_INET).\n\
        It is passed to getaddrinfo() to select only addresses in\n\
        specified family, or any family if AF_UNSPEC.\n\
    addrtype : int\n\
        Used when initializing from data to specify the address type\n\
        the data represents (e.g. ADDRTYPE_INET)\n\
    data : string or buffer\n\
        Initialize the address data from this. The addrtype must be\n\
        specify the type of data being stored in the address.\n\
:returns:\n\
    Address object\n\
\n\
Initialize an Address object. There are 3 ways to initialize: Select\n\
the optional parameters to pass depending on which initialization you\n\
intend to perform.\n\
\n\
    1. Resolve the address given a host name or numeric address and\n\
       store the resulting address data into the Address object.\n\
       Pass host and optionally family.\n\
\n\
    2. Store raw address data into the Address object.\n\
       Pass both addrtype and data.\n\
\n\
    3. Leave the Address object empty.\n\
       Do not pass any parameters.\n\
\n\
Note, this means it's error to pass both host and data.\n\
");

static int
Address_init(Address *self, PyObject *args, PyObject *kwds)
{
    static char *kwlist[] = {"host", "family", "addrtype", "data", NULL};
    int result = 0;
    PyObject *py_host = NULL;
    char *service = NULL;
    int family = AF_UNSPEC;
    int addrtype = 0;
    const void *buffer = NULL;
    Py_ssize_t buffer_len = 0;
    char *net_addr = NULL;
    socklen_t net_addr_len;
    int ai_error = 0;
    struct addrinfo hints, *ai = NULL, *cur_ai = NULL;

    TraceMethodEnter(self);

    if (!PyArg_ParseTupleAndKeywords(args, kwds, "|O&O&O&z#:Address", kwlist,
                                     string_or_none_convert, &py_host,
                                     int_or_none_convert, &family,
                                     int_or_none_convert, &addrtype,
                                     &buffer, &buffer_len))
        return -1;


    if (py_host && buffer) {
        PyErr_SetString(PyExc_ValueError, "Cannot specify both host and data");
        goto fail;
    }

    if (py_host) {
        bzero(&hints, sizeof(struct addrinfo));
        hints.ai_family = family;
        hints.ai_socktype = SOCK_STREAM;

        if ((ai_error = getaddrinfo(PyString_AsString(py_host), service, &hints, &ai)) != 0) {
            PyErr_Format(PyExc_ValueError, _("cannot obtain address for \"%s\", %s"),
                         PyString_AsString(py_host), gai_strerror(ai_error));
            goto fail;
        }

        for (cur_ai = ai; cur_ai; cur_ai = cur_ai->ai_next) {
            switch (cur_ai->ai_family) {
            case AF_INET:
                addrtype = ADDRTYPE_INET;
                net_addr = (char *)&((struct sockaddr_in *)cur_ai->ai_addr)->sin_addr;
                net_addr_len = sizeof(struct in_addr);
                break;
            case AF_INET6:
                addrtype = ADDRTYPE_INET6;
                net_addr = (char *)&((struct sockaddr_in6 *)cur_ai->ai_addr)->sin6_addr;
                net_addr_len = sizeof(struct in6_addr);
                break;
            default:
                continue;
            }

            if (Address_init_from_net_addr(self, addrtype, net_addr, net_addr_len)) {
                goto fail;
            }
            goto exit;
        }
    } else if (buffer) {
        if (addrtype == 0) {
            PyErr_SetString(PyExc_ValueError, "data specified without addrtype defined");
            goto fail;
        }

        if (Address_init_from_net_addr(self, addrtype, buffer, buffer_len)) {
            goto fail;
        }
    }

    result = 0;

 exit:
    Py_XDECREF(py_host);
    if (ai) {
        freeaddrinfo(ai);
    }
    return result;

 fail:
    result = -1;
    goto exit;
}


static PyObject *
Address_new_from_krb5_address(krb5_address *address)
{
    Address *self = NULL;

    TraceObjNewEnter(NULL);

    if ((self = (Address *) AddressType.tp_new(&AddressType, NULL, NULL)) == NULL) {
        return NULL;
    }

    if (Address_init_from_net_addr(self, address->addrtype,
                                   (char *)address->contents,
                                   address->length)) {
        Py_CLEAR(self);
        TraceObjNewLeave(self);
        return NULL;
    }

    TraceObjNewLeave(self);
    return (PyObject *) self;
}

static int
Address_init_from_net_addr(Address *self, krb5_addrtype addrtype, const char *net_addr, socklen_t net_addr_len)
{
    self->address.magic = KV5M_ADDRESS;
    self->address.addrtype = addrtype;
    self->address.length = net_addr_len;

    if ((self->address.contents = PyMem_Malloc(net_addr_len)) == NULL) {
        return -1;
    }
    memmove(self->address.contents, net_addr, net_addr_len);
    return 0;
}

/* >>> Address Class Definition <<< */

static PyMethodDef Address_methods[] = {
    {"func_name", (PyCFunction)Address_func_name, METH_VARARGS|METH_KEYWORDS, Address_func_name_doc},
    {NULL, NULL}  /* Sentinel */
};

static PyTypeObject AddressType = {
    PyObject_HEAD_INIT(NULL)
    0,						/* ob_size */
    "krb.Address",				/* tp_name */
    sizeof(Address),				/* tp_basicsize */
    0,						/* tp_itemsize */
    (destructor)Address_dealloc,		/* tp_dealloc */
    0,						/* tp_print */
    0,						/* tp_getattr */
    0,						/* tp_setattr */
    0,						/* tp_compare */
    0,						/* tp_repr */
    0,						/* tp_as_number */
    0,						/* tp_as_sequence */
    0,						/* tp_as_mapping */
    0,						/* tp_hash */
    0,						/* tp_call */
    (reprfunc)Address_str,			/* tp_str */
    0,						/* tp_getattro */
    0,						/* tp_setattro */
    0,						/* tp_as_buffer */
    Py_TPFLAGS_DEFAULT | Py_TPFLAGS_BASETYPE,	/* tp_flags */
    Address_doc,				/* tp_doc */
    (traverseproc)0,				/* tp_traverse */
    (inquiry)0,					/* tp_clear */
    0,						/* tp_richcompare */
    0,						/* tp_weaklistoffset */
    0,						/* tp_iter */
    0,						/* tp_iternext */
    Address_methods,				/* tp_methods */
    Address_members,				/* tp_members */
    Address_getseters,				/* tp_getset */
    0,						/* tp_base */
    0,						/* tp_dict */
    0,						/* tp_descr_get */
    0,						/* tp_descr_set */
    0,						/* tp_dictoffset */
    (initproc)Address_init,			/* tp_init */
    0,						/* tp_alloc */
    Address_new,				/* tp_new */
};
/* ========================================================================== */
/* ============================= KeyBlock Class ============================== */
/* ========================================================================== */

/* >>> KeyBlock Attribute Access <<< */

static PyObject *
KeyBlock_get_enctype(KeyBlock *self, void *closure)
{
    TraceMethodEnter(self);

    return PyInt_FromLong(self->keyblock->enctype);
}

static int
KeyBlock_set_enctype(KeyBlock *self, PyObject *value, void *closure)
{
    TraceMethodEnter(self);

    if (value == NULL) {
        PyErr_SetString(PyExc_TypeError, "Cannot delete the enctype attribute");
        return -1;
    }

    if (!PyInt_Check(value)) {
        PyErr_SetString(PyExc_TypeError, "The attribute value must be an int");
        return -1;
    }

    self->keyblock->enctype = PyInt_AsLong(value);

    return 0;
}

static
PyGetSetDef KeyBlock_getseters[] = {
    {"enctype", (getter)KeyBlock_get_enctype,    (setter)KeyBlock_set_enctype, "encryption type as ENCTYPE_* enumerated constant", NULL},
    {NULL}  /* Sentinel */
};

static PyMemberDef KeyBlock_members[] = {
    {NULL}  /* Sentinel */
};

/* >>> KeyBlock Class Methods <<< */

PyDoc_STRVAR(KeyBlock_func_name_doc,
"func_name() -> \n\
\n\
:parameters:\n\
    arg1 : object\n\
        xxx\n\
:returns:\n\
    xxx\n\
\n\
xxx\n\
");

static PyObject *
KeyBlock_func_name(KeyBlock *self, PyObject *args, PyObject *kwds)
{
    static char *kwlist[] = {"arg1", NULL};
    PyObject *arg;
    krb5_context current_context = NULL;

    TraceMethodEnter(self);

    if ((current_context = get_current_context()) == NULL) {
        return NULL;
    }

    if (!PyArg_ParseTupleAndKeywords(args, kwds, "O|i:func_name", kwlist,
                                     &arg))
        return NULL;

    return NULL;
}

PyDoc_STRVAR(KeyBlock_to_hex_doc,
"to_hex(octets_per_line=0, separator=':') -> string or list of strings\n\
\n\
:Parameters:\n\
    octets_per_line : integer\n\
        Number of octets formatted on one line, if 0 then\n\
        return a single string instead of an array of lines\n\
    separator : string\n\
        String used to seperate each octet\n\
        If None it will be as if the empty string had been\n\
        passed and no separator will be used.\n\
\n\
Equivalent to calling data_to_hex()\n\
");

static PyObject *
KeyBlock_to_hex(KeyBlock *self, PyObject *args, PyObject *kwds)
{
    static char *kwlist[] = {"octets_per_line", "separator", NULL};
    int octets_per_line = 0;
    char *separator = HEX_SEPARATOR_DEFAULT;

    TraceMethodEnter(self);

    if (!PyArg_ParseTupleAndKeywords(args, kwds, "|iz:to_hex", kwlist,
                                     &octets_per_line, &separator))
        return NULL;

    return raw_data_to_hex(self->keyblock->contents, self->keyblock->length, octets_per_line, separator);
}

static PyObject *
KeyBlock_format_lines(KeyBlock *self, PyObject *args, PyObject *kwds)
{
    static char *kwlist[] = {"level", NULL};
    int level = 0;
    PyObject *lines = NULL;
    PyObject *obj = NULL;

    TraceMethodEnter(self);

    if (!PyArg_ParseTupleAndKeywords(args, kwds, "|i:format_lines", kwlist, &level))
        return NULL;

    if ((lines = PyList_New(0)) == NULL) {
        return NULL;
    }

    obj = krb_enctype_to_pystr(self->keyblock->enctype);
    FMT_OBJ_AND_APPEND(lines, _("Encryption Type"), obj, level, fail);
    Py_CLEAR(obj);

    obj = PyString_FromFormat("%u", self->keyblock->length);
    FMT_OBJ_AND_APPEND(lines, _("Data Length"), obj, level, fail);
    Py_CLEAR(obj);

    FMT_LABEL_AND_APPEND(lines, _("Data"), level, fail);
    if ((obj = raw_data_to_hex(self->keyblock->contents, self->keyblock->length,
                               OCTETS_PER_LINE_DEFAULT, HEX_SEPARATOR_DEFAULT)) == NULL) {
        goto fail;
    }
    APPEND_LINES_AND_CLEAR(lines, obj, level+1, fail);

    return lines;

 fail:
    Py_XDECREF(obj);
    Py_XDECREF(lines);
    return NULL;
}

static PyObject *
KeyBlock_format(KeyBlock *self, PyObject *args, PyObject *kwds)
{
    TraceMethodEnter(self);

    return format_from_lines((format_lines_func)KeyBlock_format_lines, (PyObject *)self, args, kwds);
}

static PyObject *
KeyBlock_str(KeyBlock *self)
{
    return KeyBlock_format(self, empty_tuple, NULL);
}

/* >>> KeyBlock Class Construction <<< */

static PyObject *
KeyBlock_new(PyTypeObject *type, PyObject *args, PyObject *kwds)
{
    KeyBlock *self;

    TraceObjNewEnter(type);

    if ((self = (KeyBlock *)type->tp_alloc(type, 0)) == NULL) {
        return NULL;
    }

    self->keyblock = NULL;

    TraceObjNewLeave(self);
    return (PyObject *)self;
}

static void
KeyBlock_dealloc(KeyBlock* self)
{
    krb5_context current_context = NULL;

    TraceMethodEnter(self);

    if ((current_context = get_current_context()) != NULL) {
        krb5_free_keyblock(current_context, self->keyblock);
    }

    self->ob_type->tp_free((PyObject*)self);
}

PyDoc_STRVAR(KeyBlock_doc,
"KeyBlock(enctype=ENCTYPE_NULL, data=None)\n\
\n\
:Parameters:\n\
    enctype : int\n\
        encryption type enumerated constant (e.g. ENCTYPE_*)\n\
    data : any read buffer compatible object (e.g. buffer or string)\n\
        raw data to initialize from\n\
:returns:\n\
    KeyBlock object\n\
\n\
An object representing KeyBlock.\n\
");

static int
KeyBlock_init(KeyBlock *self, PyObject *args, PyObject *kwds)
{
    static char *kwlist[] = {"enctype", "data", NULL};
    int enctype = ENCTYPE_NULL;
    const void *buffer = NULL;
    Py_ssize_t buffer_len = 0;
    krb5_error_code krb_error;
    krb5_context current_context = NULL;

    TraceMethodEnter(self);

    if ((current_context = get_current_context()) == NULL) {
        return -1;
    }

    if (!PyArg_ParseTupleAndKeywords(args, kwds, "|iz#:KeyBlock", kwlist,
                                     &enctype, &buffer, &buffer_len))
        return -1;

    if ((krb_error = krb5_init_keyblock(current_context, enctype, buffer_len, &self->keyblock))) {
        return -1;
    }
    if (buffer && buffer_len) {
        memmove(self->keyblock->contents, buffer, buffer_len);
    }

    return 0;
}


static PyObject *
KeyBlock_new_from_krb5_keyblock(krb5_keyblock *keyblock)
{
    krb5_error_code krb_error;
    KeyBlock *self = NULL;
    krb5_context current_context = NULL;

    TraceObjNewEnter(NULL);

    if ((current_context = get_current_context()) == NULL) {
        return NULL;
    }

    if ((self = (KeyBlock *) KeyBlockType.tp_new(&KeyBlockType, NULL, NULL)) == NULL) {
        return NULL;
    }

    if ((krb_error = krb5_copy_keyblock(current_context, keyblock, &self->keyblock))) {
        Py_CLEAR(self);
        TraceObjNewLeave(self);
        return set_krb_error(krb_error, NULL);
    }

    TraceObjNewLeave(self);
    return (PyObject *) self;
}

/* >>> KeyBlock Sequence <<< */

static Py_ssize_t
KeyBlock_length(KeyBlock *self)
{
    return self->keyblock->length;
}

static PyObject *
KeyBlock_item(KeyBlock *self, register Py_ssize_t i)
{
    char octet;

    if (i < 0 || i >= self->keyblock->length) {
        PyErr_SetString(PyExc_IndexError, "KeyBlock index out of range");
        return NULL;
    }
    octet = self->keyblock->contents[i];
    return PyString_FromStringAndSize(&octet, 1);
}

static PyObject *
KeyBlock_slice(KeyBlock *self, Py_ssize_t low, Py_ssize_t high)
{
    if (low < 0)
        low = 0;
    if (high < 0)
        high = 0;
    if (high > self->keyblock->length)
        high = self->keyblock->length;
    if (high < low)
        high = low;
    return PyString_FromStringAndSize((const char *)(self->keyblock->contents + low), high-low);
}

static PyObject*
KeyBlock_subscript(KeyBlock *self, PyObject* item)
{
    if (PyIndex_Check(item)) {
        Py_ssize_t i = PyNumber_AsSsize_t(item, PyExc_IndexError);
        if (i == -1 && PyErr_Occurred())
            return NULL;
        if (i < 0)
            i += self->keyblock->length;
        return KeyBlock_item(self, i);
    }
    else if (PySlice_Check(item)) {
        Py_ssize_t start, stop, step, slice_len, cur, i;
        unsigned char* src;
        unsigned char* dst;
        PyObject* result;

        if (PySlice_GetIndicesEx((PySliceObject*)item, self->keyblock->length,
				 &start, &stop, &step, &slice_len) < 0) {
            return NULL;
        }

        if (slice_len <= 0) {
            return PyString_FromStringAndSize("", 0);
        } else if (step == 1) {
            return PyString_FromStringAndSize((char *)self->keyblock->contents + start, slice_len);
        } else {
            src = self->keyblock->contents;
            if ((result = PyString_FromStringAndSize(NULL, slice_len)) == NULL) {
                return NULL;
            }
            dst = (unsigned char *)PyString_AsString(result);
            for (cur = start, i = 0; i < slice_len; cur += step, i++) {
                dst[i] = src[cur];
            }
            return result;
        }
    } else {
        PyErr_Format(PyExc_TypeError, "KeyBlock indices must be integers, not %.200s",
                     Py_TYPE(item)->tp_name);
        return NULL;
    }
}

static PySequenceMethods KeyBlock_as_sequence = {
    (lenfunc)KeyBlock_length,			/* sq_length */
    0,						/* sq_concat */
    0,						/* sq_repeat */
    (ssizeargfunc)KeyBlock_item,		/* sq_item */
    (ssizessizeargfunc)KeyBlock_slice,		/* sq_slice */
    0,						/* sq_ass_item */
    0,						/* sq_ass_slice */
    0,						/* sq_contains */
    0,						/* sq_inplace_concat */
    0,						/* sq_inplace_repeat */
};

static PyMappingMethods KeyBlock_as_mapping = {
    (lenfunc)KeyBlock_length,			/* mp_length */
    (binaryfunc)KeyBlock_subscript,		/* mp_subscript */
    0,						/* mp_ass_subscript */
};

/* >>> KeyBlock Class Definition <<< */

static PyMethodDef KeyBlock_methods[] = {
    {"format_lines", (PyCFunction)KeyBlock_format_lines,   METH_VARARGS|METH_KEYWORDS, generic_format_lines_doc},
    {"format",       (PyCFunction)KeyBlock_format,         METH_VARARGS|METH_KEYWORDS, generic_format_doc},
    {"to_hex",       (PyCFunction)KeyBlock_to_hex,         METH_VARARGS|METH_KEYWORDS, KeyBlock_to_hex_doc},
    {"func_name",    (PyCFunction)KeyBlock_func_name,      METH_VARARGS|METH_KEYWORDS, KeyBlock_func_name_doc},
    {NULL, NULL}  /* Sentinel */
};

static PyTypeObject KeyBlockType = {
    PyObject_HEAD_INIT(NULL)
    0,						/* ob_size */
    "krb.KeyBlock",				/* tp_name */
    sizeof(KeyBlock),				/* tp_basicsize */
    0,						/* tp_itemsize */
    (destructor)KeyBlock_dealloc,		/* tp_dealloc */
    0,						/* tp_print */
    0,						/* tp_getattr */
    0,						/* tp_setattr */
    0,						/* tp_compare */
    0,						/* tp_repr */
    0,						/* tp_as_number */
    &KeyBlock_as_sequence,			/* tp_as_sequence */
    &KeyBlock_as_mapping,			/* tp_as_mapping */
    0,						/* tp_hash */
    0,						/* tp_call */
    (reprfunc)KeyBlock_str,			/* tp_str */
    0,						/* tp_getattro */
    0,						/* tp_setattro */
    0,						/* tp_as_buffer */
    Py_TPFLAGS_DEFAULT | Py_TPFLAGS_BASETYPE,	/* tp_flags */
    KeyBlock_doc,				/* tp_doc */
    (traverseproc)0,				/* tp_traverse */
    (inquiry)0,					/* tp_clear */
    0,						/* tp_richcompare */
    0,						/* tp_weaklistoffset */
    0,						/* tp_iter */
    0,						/* tp_iternext */
    KeyBlock_methods,				/* tp_methods */
    KeyBlock_members,				/* tp_members */
    KeyBlock_getseters,				/* tp_getset */
    0,						/* tp_base */
    0,						/* tp_dict */
    0,						/* tp_descr_get */
    0,						/* tp_descr_set */
    0,						/* tp_dictoffset */
    (initproc)KeyBlock_init,			/* tp_init */
    0,						/* tp_alloc */
    KeyBlock_new,				/* tp_new */
};

/* ========================================================================== */
/* ============================= Context Class ============================== */
/* ========================================================================== */

/* >>> Context Attribute Access <<< */

static
PyGetSetDef Context_getseters[] = {
    {NULL}  /* Sentinel */
};

static PyMemberDef Context_members[] = {
    {NULL}  /* Sentinel */
};

/* >>> Context Class Methods <<< */

/* >>> Context Class Construction <<< */

static PyObject *
Context_new(PyTypeObject *type, PyObject *args, PyObject *kwds)
{
    Context *self;

    TraceObjNewEnter(type);

    if ((self = (Context *)type->tp_alloc(type, 0)) == NULL) {
        return NULL;
    }

    TraceObjNewLeave(self);
    return (PyObject *)self;
}

static void
Context_dealloc(Context* self)
{
    TraceMethodEnter(self);

    krb5_free_context(self->context);

    self->ob_type->tp_free((PyObject*)self);
}

PyDoc_STRVAR(Context_doc,
"Context(type='default')\n\
\n\
:parameters:\n\
    type : string\n\
        Optional, the type of the context, may one of:\n\
        default, secure\n\
\n\
:returns:\n\
    Context object\n\
\n\
An object representing Kerberos context.\n\
\n\
The type may be one of:\n\
\n\
    default\n\
        Creates a default context.\n\
        Equivalent to krb5_init_context()\n\
    secure\n\
        Creates context using only system configuration files. All\n\
        information passed through environment variables are ignored.\n\
        Equivalent to krb5_init_secure_context().\n\
\n\
");

static int
Context_init(Context *self, PyObject *args, PyObject *kwds)
{
    static char *kwlist[] = {"type", NULL};
    char *type = "default";
    krb5_error_code krb_error;
    krb5_context context = NULL;

    TraceMethodEnter(self);

    if (!PyArg_ParseTupleAndKeywords(args, kwds, "|s:Context", kwlist,
                                     &type))
        return -1;

    if (strcmp(type, "default") == 0) {
        if ((krb_error = krb5_init_context(&context))) {
            set_krb_error(krb_error, NULL);
            return -1;
        }
    } else if (strcmp(type, "secure") == 0) {
        if ((krb_error = krb5_init_secure_context(&context))) {
            set_krb_error(krb_error, NULL);
            return -1;
        }
    } else {
        PyErr_Format(PyExc_ValueError, "Context type must be one of: 'default', 'secure'; not %s",
                     type);
        return -1;
    }

    self->context = context;

    return 0;
}


/* >>> Context Class Definition <<< */

static PyMethodDef Context_methods[] = {
    {NULL, NULL}  /* Sentinel */
};

static PyTypeObject ContextType = {
    PyObject_HEAD_INIT(NULL)
    0,						/* ob_size */
    "krb.Context",				/* tp_name */
    sizeof(Context),				/* tp_basicsize */
    0,						/* tp_itemsize */
    (destructor)Context_dealloc,		/* tp_dealloc */
    0,						/* tp_print */
    0,						/* tp_getattr */
    0,						/* tp_setattr */
    0,						/* tp_compare */
    0,						/* tp_repr */
    0,						/* tp_as_number */
    0,						/* tp_as_sequence */
    0,						/* tp_as_mapping */
    0,						/* tp_hash */
    0,						/* tp_call */
    0,						/* tp_str */
    0,						/* tp_getattro */
    0,						/* tp_setattro */
    0,						/* tp_as_buffer */
    Py_TPFLAGS_DEFAULT | Py_TPFLAGS_BASETYPE,	/* tp_flags */
    Context_doc,				/* tp_doc */
    (traverseproc)0,				/* tp_traverse */
    (inquiry)0,					/* tp_clear */
    0,						/* tp_richcompare */
    0,						/* tp_weaklistoffset */
    0,						/* tp_iter */
    0,						/* tp_iternext */
    Context_methods,				/* tp_methods */
    Context_members,				/* tp_members */
    Context_getseters,				/* tp_getset */
    0,						/* tp_base */
    0,						/* tp_dict */
    0,						/* tp_descr_get */
    0,						/* tp_descr_set */
    0,						/* tp_dictoffset */
    (initproc)Context_init,			/* tp_init */
    0,						/* tp_alloc */
    Context_new,				/* tp_new */
};

/* ========================================================================== */
/* ============================ Principal Class ============================= */
/* ========================================================================== */

/* === Attribute Access === */

static PyObject *
Principal_get_realm(Principal *self, void *closure)
{
    krb5_data *realm = NULL;
    krb5_context current_context = NULL;

    TraceMethodEnter(self);

    if ((current_context = get_current_context()) == NULL) {
        return NULL;
    }

    realm = krb5_princ_realm(current_context, self->principal);
    return PyString_FromStringAndSize(realm->data, realm->length);
}

static int
Principal_set_realm(Principal *self, PyObject *value, void *closure)
{
    krb5_error_code krb_error;
    krb5_context current_context = NULL;
    PyObject *py_value_utf8 = NULL;

    TraceMethodEnter(self);

    if ((current_context = get_current_context()) == NULL) {
        return -1;
    }

    if (value == NULL) {
        PyErr_SetString(PyExc_TypeError, "Cannot delete the realm attribute");
        return -1;
    }

    if ((py_value_utf8 = PyString_UTF8(value, "realm")) == NULL) {
        return -1;
    }

    if ((krb_error = krb5_set_principal_realm(current_context, self->principal, PyString_AsString(py_value_utf8)))) {
	Py_DECREF(py_value_utf8);
        set_krb_error(krb_error, NULL);
        return -1;
    }

    Py_DECREF(py_value_utf8);
    return 0;
}

static PyObject *
Principal_get_type(Principal *self, void *closure)
{
    krb5_int32 type = KRB5_NT_UNKNOWN;
    krb5_context current_context = NULL;

    TraceMethodEnter(self);

    if ((current_context = get_current_context()) == NULL) {
        return NULL;
    }

    type = krb5_princ_type(current_context, self->principal);
    return PyInt_FromLong(type);
}

static
PyGetSetDef Principal_getseters[] = {
    {"realm", (getter)Principal_get_realm, (setter)Principal_set_realm, "principal's realm",     NULL},
    {"type",  (getter)Principal_get_type,  (setter)NULL,                "principal's name type", NULL},
    {NULL}  /* Sentinel */
};

static PyMemberDef Principal_members[] = {
    {NULL}  /* Sentinel */
};

/* === Class Methods === */

static PyObject *
Principal_richcompare(Principal *self, Principal *other, int op)
{
    krb5_boolean result;
    krb5_context current_context = NULL;

    if ((current_context = get_current_context()) == NULL) {
        return NULL;
    }

    if (op != Py_EQ && op != Py_NE) {
        PyErr_SetString(PyExc_TypeError, "Only Equal (==) & Not Equal (!=) comparisons supported between Principal objects");
        return NULL;
    }

    if (!PyPrincipal_Check(other)) {
        PyErr_Format(PyExc_TypeError, "must be a Principal object, not %.200s",
                     Py_TYPE(other)->tp_name);
        return NULL;
    }

    result = krb5_principal_compare(current_context, self->principal, other->principal);
    if (op == Py_EQ) {
        if (result) {
            Py_RETURN_TRUE;
        } else {
            Py_RETURN_FALSE;
        }
    }

    if (op == Py_NE) {
        if (result) {
            Py_RETURN_FALSE;
        } else {
            Py_RETURN_TRUE;
        }
    }

    /* Should never reach here */
    return NULL;
}

static PyObject *
Principal_str(Principal *self)
{
    krb5_error_code krb_error;
    krb5_context current_context = NULL;
    char *name = NULL;
    PyObject *result = NULL;

    if ((current_context = get_current_context()) == NULL) {
        return NULL;
    }

    if ((krb_error = krb5_unparse_name(current_context, self->principal, &name))) {
        return set_krb_error(krb_error, NULL);
    }

    result = PyString_FromString(name);
    krb5_free_unparsed_name(current_context, name);
    return result;
}

/* === Class Construction === */

static PyObject *
Principal_new(PyTypeObject *type, PyObject *args, PyObject *kwds)
{
    Principal *self;

    TraceObjNewEnter(type);

    if ((self = (Principal *)type->tp_alloc(type, 0)) == NULL) {
        return NULL;
    }

    self->principal = NULL;

    TraceObjNewLeave(self);
    return (PyObject *)self;
}

static PyObject *
Principal_new_from_krb5_principal(krb5_const_principal principal)
{
    Principal *self = NULL;
    krb5_error_code krb_error;
    krb5_context current_context = NULL;

    TraceObjNewEnter(NULL);

    if ((current_context = get_current_context()) == NULL) {
        return NULL;
    }

    if ((self = (Principal *) PrincipalType.tp_new(&PrincipalType, NULL, NULL)) == NULL) {
        return NULL;
    }

    if ((krb_error = krb5_copy_principal(current_context, principal, &self->principal))) {
        Py_CLEAR(self);
        TraceObjNewLeave(self);
        return set_krb_error(krb_error, NULL);
    }


    TraceObjNewLeave(self);
    return (PyObject *) self;
}

static void
Principal_dealloc(Principal* self)
{
    TraceMethodEnter(self);
    krb5_context current_context = NULL;

    if ((current_context = get_current_context_no_error()) == NULL) {
        PySys_WriteStderr("No current context set (%s)\n", __FUNCTION__);
    }

    if (current_context && self->principal) {
        krb5_free_principal(current_context, self->principal);
        self->principal = NULL;
    }


    self->ob_type->tp_free((PyObject*)self);
}

PyDoc_STRVAR(Principal_doc,
"Principal(name, flags=0)\n\
\n\
:parameters:\n\
    name : string\n\
      principal's name. See `build_principal_name()` \n\
    flags : int\n\
      Any of the following OR'ed together:\n\
\n\
        * KRB5_PRINCIPAL_PARSE_NO_REALM\n\
        * KRB5_PRINCIPAL_PARSE_REQUIRE_REALM\n\
        * KRB5_PRINCIPAL_PARSE_ENTERPRISE\n\
\n\
An object representing a Kerberos Principal.\n\
\n\
See `build_principal_name()` for a utility which can be used to\n\
generate a principal name to be passed to the constructor.\n\
\n\
Principal objects support:\n\
\n\
  * The == and != comparison operator\n\
  * Reading & writing to the realm property\n\
  * Reading the type property (name type enumerated constant)\n\
  * Because principals may be composed of multiple components\n\
    - len() returns the number of components\n\
    - components may be indexed\n\
    - slices may be taken of the components\n\
    - components may be iterated over\n\
\n\
Examples:\n\
\n\
  >>> # Create a service principal\n\
  ... p = Principal('HTTP/webserver.example.com@EXAMPLE.COM')\n\
  >>> # Get the principal's realm\n\
  ... p.realm\n\
  'EXAMPLE.COM'\n\
  >>> # Set the principal's realm\n\
  ... p.realm = 'CLOUD.ORG'\n\
  ... p.realm\n\
  'CLOUD.ORG'\n\
  >>> # Get the name type of the principal as an enumerated constant\n\
  ... p.type\n\
  1\n\
  >>> # Check the type against the constant\n\
  ... p.type == KRB5_NT_PRINCIPAL\n\
  True\n\
  >>> # Get the number of components in the principal\n\
  ... len(p)\n\
  2\n\
  >>> # Get the first component of the principal\n\
  ... p[0]\n\
  'HTTP'\n\
  >>> # Get the second component of the principal\n\
  ... p[1]\n\
  'webserver.example.com'\n\
  >>> # Get a full slice from the sequence\n\
  ... p[:]\n\
  ('HTTP', 'webserver.example.com')\n\
  >>> # Iterate over each component\n\
  ... for c in p:\n\
  ...     print c\n\
  ... \n\
  HTTP\n\
  webserver.example.com\n\
");

static int
Principal_init(Principal *self, PyObject *args, PyObject *kwds)
{
    static char *kwlist[] = {"name", "flags", NULL};
    PyObject *py_name = NULL;
    PyObject *py_name_utf8 = NULL;
    int flags = 0;
    krb5_error_code krb_error;
    krb5_context current_context = NULL;

    TraceMethodEnter(self);

    if ((current_context = get_current_context()) == NULL) {
        return -1;
    }

    if (!PyArg_ParseTupleAndKeywords(args, kwds, "O|i:Principal", kwlist,
                                     &py_name, &flags))
        return -1;

    if ((py_name_utf8 = PyString_UTF8(py_name, "name")) == NULL) {
        return -1;
    }

    if ((krb_error = krb5_parse_name_flags(current_context, PyString_AsString(py_name_utf8), flags, &self->principal))) {
        set_krb_error(krb_error, "name=\"%s\"", PyString_AsString(py_name_utf8));
        return -1;
    }

    return 0;
}

/* >>> Principal Sequence <<< */

static Py_ssize_t
Principal_length(Principal *self)
{
    krb5_int32 length;

    length = krb5_princ_size(current_context, self->principal);
    return length;
}

static PyObject *
Principal_item(Principal *self, register Py_ssize_t i)
{
    Py_ssize_t length = 0;
    krb5_data *component = NULL;

    length = Principal_length(self);

    if (i < 0 || i >= length) {
        PyErr_SetString(PyExc_IndexError, "Principal index out of range");
        return NULL;
    }

    component = krb5_princ_component(current_context, self->principal, i);
    return PyString_FromStringAndSize(component->data, component->length);

}

static PyObject *
Principal_slice(Principal *self, Py_ssize_t low, Py_ssize_t high)
{
    krb5_int32 length = 0;
    Py_ssize_t n_items = 0;
    PyObject *tuple = NULL;
    Py_ssize_t i;
    krb5_data *component = NULL;
    PyObject *py_component = NULL;

    length = krb5_princ_size(current_context, self->principal);

    if (low < 0)
        low = 0;
    if (high < 0)
        high = 0;
    if (high > length)
        high = length;
    if (high < low)
        high = low;

    n_items = high - low;

    if ((tuple = PyTuple_New(n_items)) == NULL) {
        return NULL;
    }

    for (i = 0; i < n_items; i++) {
        component = krb5_princ_component(current_context, self->principal, i+low);
        if ((py_component = PyString_FromStringAndSize(component->data, component->length)) == NULL) {
            Py_DECREF(tuple);
            return NULL;
        }
        PyTuple_SetItem(tuple, i, py_component);
    }

    return tuple;
}

static PySequenceMethods Principal_as_sequence = {
    (lenfunc)Principal_length,			/* sq_length */
    0,						/* sq_concat */
    0,						/* sq_repeat */
    (ssizeargfunc)Principal_item,		/* sq_item */
    (ssizessizeargfunc)Principal_slice,		/* sq_slice */
    0,						/* sq_ass_item */
    0,						/* sq_ass_slice */
    0,						/* sq_contains */
    0,						/* sq_inplace_concat */
    0,						/* sq_inplace_repeat */
};

/* >>> Class Definition <<< */

static PyMethodDef Principal_methods[] = {
    {NULL, NULL}  /* Sentinel */
};

static PyTypeObject PrincipalType = {
    PyObject_HEAD_INIT(NULL)
    0,						/* ob_size */
    "krb.Principal",				/* tp_name */
    sizeof(Principal),				/* tp_basicsize */
    0,						/* tp_itemsize */
    (destructor)Principal_dealloc,		/* tp_dealloc */
    0,						/* tp_print */
    0,						/* tp_getattr */
    0,						/* tp_setattr */
    0,						/* tp_compare */
    0,						/* tp_repr */
    0,						/* tp_as_number */
    &Principal_as_sequence,			/* tp_as_sequence */
    0,						/* tp_as_mapping */
    0,						/* tp_hash */
    0,						/* tp_call */
    (reprfunc)Principal_str,			/* tp_str */
    0,						/* tp_getattro */
    0,						/* tp_setattro */
    0,						/* tp_as_buffer */
    Py_TPFLAGS_DEFAULT | Py_TPFLAGS_BASETYPE,	/* tp_flags */
    Principal_doc,				/* tp_doc */
    (traverseproc)0,				/* tp_traverse */
    (inquiry)0,					/* tp_clear */
    (richcmpfunc)Principal_richcompare,		/* tp_richcompare */
    0,						/* tp_weaklistoffset */
    0,						/* tp_iter */
    0,						/* tp_iternext */
    Principal_methods,				/* tp_methods */
    Principal_members,				/* tp_members */
    Principal_getseters,				/* tp_getset */
    0,						/* tp_base */
    0,						/* tp_dict */
    0,						/* tp_descr_get */
    0,						/* tp_descr_set */
    0,						/* tp_dictoffset */
    (initproc)Principal_init,			/* tp_init */
    0,						/* tp_alloc */
    Principal_new,				/* tp_new */
};

/* ========================================================================== */
/* =========================== TicketTimes Class ============================ */
/* ========================================================================== */

/* >>> TicketTimes Attribute Access <<< */

static PyObject *
TicketTimes_get_auth(TicketTimes *self, void *closure)
{
    TraceMethodEnter(self);

    return datetime_from_timestamp(self->ticket_times.authtime);
}

static int
TicketTimes_set_auth(TicketTimes *self, PyObject *value, void *closure)
{
    time_t timestamp;

    TraceMethodEnter(self);

    if (value == NULL) {
        PyErr_SetString(PyExc_TypeError, "Cannot delete the auth attribute");
        return -1;
    }

    timestamp = time_t_from_py_value(value, "auth");
    if (timestamp == (time_t)-1 && PyErr_Occurred()) {
        return -1;
    }

    self->ticket_times.authtime = timestamp;
    return 0;
}

static PyObject *
TicketTimes_get_start(TicketTimes *self, void *closure)
{
    TraceMethodEnter(self);

    return datetime_from_timestamp(self->ticket_times.starttime);
}

static int
TicketTimes_set_start(TicketTimes *self, PyObject *value, void *closure)
{
    time_t timestamp;

    TraceMethodEnter(self);

    if (value == NULL) {
        PyErr_SetString(PyExc_TypeError, "Cannot delete the start attribute");
        return -1;
    }

    timestamp = time_t_from_py_value(value, "start");
    if (timestamp == (time_t)-1 && PyErr_Occurred()) {
        return -1;
    }

    self->ticket_times.starttime = timestamp;
    return 0;
}

static PyObject *
TicketTimes_get_end(TicketTimes *self, void *closure)
{
    TraceMethodEnter(self);

    return datetime_from_timestamp(self->ticket_times.endtime);
}

static int
TicketTimes_set_end(TicketTimes *self, PyObject *value, void *closure)
{
    time_t timestamp;

    TraceMethodEnter(self);

    if (value == NULL) {
        PyErr_SetString(PyExc_TypeError, "Cannot delete the end attribute");
        return -1;
    }

    timestamp = time_t_from_py_value(value, "end");
    if (timestamp == (time_t)-1 && PyErr_Occurred()) {
        return -1;
    }

    self->ticket_times.endtime = timestamp;
    return 0;
}

static PyObject *
TicketTimes_get_renew_till(TicketTimes *self, void *closure)
{
    TraceMethodEnter(self);

    return datetime_from_timestamp(self->ticket_times.renew_till);
}

static int
TicketTimes_set_renew_till(TicketTimes *self, PyObject *value, void *closure)
{
    time_t timestamp;

    TraceMethodEnter(self);

    if (value == NULL) {
        PyErr_SetString(PyExc_TypeError, "Cannot delete the renew_till attribute");
        return -1;
    }

    timestamp = time_t_from_py_value(value, "renew_till");
    if (timestamp == (time_t)-1 && PyErr_Occurred()) {
        return -1;
    }

    self->ticket_times.renew_till = timestamp;
    return 0;
}

static
PyGetSetDef TicketTimes_getseters[] = {
    {"auth",       (getter)TicketTimes_get_auth,       (setter)TicketTimes_set_auth,       "auth time, returned as datetime object, set from datetime or float, int, timestamp", NULL},
    {"start",      (getter)TicketTimes_get_start,      (setter)TicketTimes_set_start,      "start time, returned as datetime object, set from datetime or float, int, timestamp", NULL},
    {"end",        (getter)TicketTimes_get_end,        (setter)TicketTimes_set_end,        "end time, returned as datetime object, set from datetime or float, int, timestamp", NULL},
    {"renew_till", (getter)TicketTimes_get_renew_till, (setter)TicketTimes_set_renew_till, "renew_till time, returned as datetime object, set from datetime or float, int, timestamp", NULL},
    {NULL}  /* Sentinel */
};

static PyMemberDef TicketTimes_members[] = {
    {NULL}  /* Sentinel */
};

/* >>> TicketTimes Class Methods <<< */

static PyObject *
TicketTimes_format_lines(TicketTimes *self, PyObject *args, PyObject *kwds)
{
    static char *kwlist[] = {"level", NULL};
    int level = 0;
    PyObject *lines = NULL;
    PyObject *obj = NULL;

    TraceMethodEnter(self);

    if (!PyArg_ParseTupleAndKeywords(args, kwds, "|i:format_lines", kwlist, &level))
        return NULL;

    if ((lines = PyList_New(0)) == NULL) {
        return NULL;
    }

    FMT_LABEL_AND_APPEND(lines, _("Ticket Times"), level, fail);

    if ((obj = TicketTimes_get_auth(self, NULL)) == NULL) goto fail;
    FMT_OBJ_AND_APPEND(lines, _("Auth"), obj, level+1, fail);
    Py_CLEAR(obj);

    if ((obj = TicketTimes_get_start(self, NULL)) == NULL) goto fail;
    FMT_OBJ_AND_APPEND(lines, _("Start"), obj, level+1, fail);
    Py_CLEAR(obj);

    if ((obj = TicketTimes_get_end(self, NULL)) == NULL) goto fail;
    FMT_OBJ_AND_APPEND(lines, _("End"), obj, level+1, fail);
    Py_CLEAR(obj);

    if ((obj = TicketTimes_get_renew_till(self, NULL)) == NULL) goto fail;
    FMT_OBJ_AND_APPEND(lines, _("Renew Till"), obj, level+1, fail);
    Py_CLEAR(obj);

    return lines;
 fail:
    Py_XDECREF(obj);
    Py_XDECREF(lines);
    return NULL;
}

static PyObject *
TicketTimes_format(TicketTimes *self, PyObject *args, PyObject *kwds)
{
    TraceMethodEnter(self);

    return format_from_lines((format_lines_func)TicketTimes_format_lines, (PyObject *)self, args, kwds);
}

static PyObject *
TicketTimes_str(TicketTimes *self)
{
    return TicketTimes_format(self, empty_tuple, NULL);
}

/* >>> TicketTimes Class Construction <<< */

static PyObject *
TicketTimes_new(PyTypeObject *type, PyObject *args, PyObject *kwds)
{
    TicketTimes *self;

    TraceObjNewEnter(type);

    if ((self = (TicketTimes *)type->tp_alloc(type, 0)) == NULL) {
        return NULL;
    }

    memset(&self->ticket_times, 0, sizeof(krb5_ticket_times));

    TraceObjNewLeave(self);
    return (PyObject *)self;
}

static void
TicketTimes_dealloc(TicketTimes* self)
{
    TraceMethodEnter(self);

    self->ob_type->tp_free((PyObject*)self);
}

PyDoc_STRVAR(TicketTimes_doc,
"TicketTimes(auth=None, start=None, end=None, renew_till=None)\n\
\n\
:parameters:\n\
    auth : datetime | float | int | None\n\
        The ticket auth time.\n\
        If a datetime object it is set to this value.\n\
        If a float or int it is interpreted as a UNIX timestamp value.\n\
        If None it is initialized to the current time.\n\
:returns:\n\
    New TicketTimes object\n\
\n\
An object representing TicketTimes\n\
With the following datetime properties:\n\
\n\
    auth\n\
        time ticket was authorized.\n\
    start\n\
        starting validity time.\n\
    end\n\
        ending validity time.\n\
    renew_till\n\
        time ticket can be renewed until\n\
");

static int
TicketTimes_init(TicketTimes *self, PyObject *args, PyObject *kwds)
{
    static char *kwlist[] = {"auth", "start", "end", "renew_till", NULL};
    PyObject *py_auth = NULL;
    PyObject *py_start = NULL;
    PyObject *py_end = NULL;
    PyObject *py_renew_till = NULL;
    time_t timestamp;


    TraceMethodEnter(self);

    if (!PyArg_ParseTupleAndKeywords(args, kwds, "|OOOO:TicketTimes", kwlist,
                                     &py_auth, &py_start, &py_end, &py_renew_till))
        return -1;

    /* auth */
    if (py_auth) {
        timestamp = time_t_from_py_value(py_auth, "auth");
    } else {
        timestamp = timestamp_now();
    }
    if (timestamp == (time_t)-1 && PyErr_Occurred()) {
        return -1;
    }
    self->ticket_times.authtime = timestamp;

    /* start */
    if (py_start) {
        timestamp = time_t_from_py_value(py_start, "start");
    } else {
        timestamp = timestamp_now();
    }
    if (timestamp == (time_t)-1 && PyErr_Occurred()) {
        return -1;
    }
    self->ticket_times.starttime = timestamp;

    /* end */
    if (py_end) {
        timestamp = time_t_from_py_value(py_end, "end");
    } else {
        timestamp = timestamp_now();
    }
    if (timestamp == (time_t)-1 && PyErr_Occurred()) {
        return -1;
    }
    self->ticket_times.endtime = timestamp;

    /* renew_till */
    if (py_renew_till) {
        timestamp = time_t_from_py_value(py_renew_till, "renew_till");
    } else {
        timestamp = timestamp_now();
    }
    if (timestamp == (time_t)-1 && PyErr_Occurred()) {
        return -1;
    }
    self->ticket_times.renew_till = timestamp;

    return 0;
}


static PyObject *
TicketTimes_new_from_krb5_ticket_times(krb5_ticket_times *ticket_times)
{
    TicketTimes *self = NULL;

    TraceObjNewEnter(NULL);

    if ((self = (TicketTimes *) TicketTimesType.tp_new(&TicketTimesType, NULL, NULL)) == NULL) {
        return NULL;
    }

    self->ticket_times = *ticket_times;

    TraceObjNewLeave(self);
    return (PyObject *) self;
}

/* >>> TicketTimes Class Definition <<< */

static PyMethodDef TicketTimes_methods[] = {
    {"format_lines", (PyCFunction)TicketTimes_format_lines,   METH_VARARGS|METH_KEYWORDS, generic_format_lines_doc},
    {"format",       (PyCFunction)TicketTimes_format,         METH_VARARGS|METH_KEYWORDS, generic_format_doc},
    {NULL, NULL}  /* Sentinel */
};

static PyTypeObject TicketTimesType = {
    PyObject_HEAD_INIT(NULL)
    0,						/* ob_size */
    "krb.TicketTimes",				/* tp_name */
    sizeof(TicketTimes),				/* tp_basicsize */
    0,						/* tp_itemsize */
    (destructor)TicketTimes_dealloc,		/* tp_dealloc */
    0,						/* tp_print */
    0,						/* tp_getattr */
    0,						/* tp_setattr */
    0,						/* tp_compare */
    0,						/* tp_repr */
    0,						/* tp_as_number */
    0,						/* tp_as_sequence */
    0,						/* tp_as_mapping */
    0,						/* tp_hash */
    0,						/* tp_call */
    (reprfunc)TicketTimes_str,			/* tp_str */
    0,						/* tp_getattro */
    0,						/* tp_setattro */
    0,						/* tp_as_buffer */
    Py_TPFLAGS_DEFAULT | Py_TPFLAGS_BASETYPE,	/* tp_flags */
    TicketTimes_doc,				/* tp_doc */
    (traverseproc)0,				/* tp_traverse */
    (inquiry)0,					/* tp_clear */
    0,						/* tp_richcompare */
    0,						/* tp_weaklistoffset */
    0,						/* tp_iter */
    0,						/* tp_iternext */
    TicketTimes_methods,				/* tp_methods */
    TicketTimes_members,				/* tp_members */
    TicketTimes_getseters,				/* tp_getset */
    0,						/* tp_base */
    0,						/* tp_dict */
    0,						/* tp_descr_get */
    0,						/* tp_descr_set */
    0,						/* tp_dictoffset */
    (initproc)TicketTimes_init,			/* tp_init */
    0,						/* tp_alloc */
    TicketTimes_new,				/* tp_new */
};

/* ========================================================================== */
/* =========================== Credential Class ============================= */
/* ========================================================================== */

/* >>> Credential Attribute Access <<< */

static PyObject *
Credential_get_client(Credential *self, void *closure)
{
    TraceMethodEnter(self);

    return Principal_new_from_krb5_principal(self->credential->client);
}

static PyObject *
Credential_get_server(Credential *self, void *closure)
{
    TraceMethodEnter(self);

    return Principal_new_from_krb5_principal(self->credential->server);
}

static PyObject *
Credential_get_times(Credential *self, void *closure)
{
    TraceMethodEnter(self);

    return TicketTimes_new_from_krb5_ticket_times(&self->credential->times);
}

static PyObject *
Credential_get_is_skey(Credential *self, void *closure)
{
    TraceMethodEnter(self);

    if (self->credential->is_skey) {
        Py_RETURN_TRUE;
    } else {
        Py_RETURN_FALSE;
    }
}

static PyObject *
Credential_get_ticket_flags(Credential *self, void *closure)
{
    TraceMethodEnter(self);

    return PyInt_FromLong(self->credential->ticket_flags);
}

static PyObject *
Credential_get_addresses(Credential *self, void *closure)
{
    krb5_address *address = NULL;
    Py_ssize_t index = 0, len = 0;
    PyObject *py_address = NULL;
    PyObject *py_list = NULL;

    TraceMethodEnter(self);

    for (len = 0, address = *self->credential->addresses; address; len++, address++);

    if ((py_list = PyList_New(len)) == NULL) {
        return NULL;
    }

    for (index = 0, address = *self->credential->addresses; address; index++, address++) {
        if ((py_address = Address_new_from_krb5_address(address)) == NULL) {
            Py_DECREF(py_list);
            return NULL;
        }
        if ((PyList_SetItem(py_list, index, py_address)) == -1) {
            Py_DECREF(py_address);
            Py_DECREF(py_list);
            return NULL;
        }
    }

    return py_list;
}

static
PyGetSetDef Credential_getseters[] = {
    {"client",       (getter)Credential_get_client,       (setter)NULL, "returns client as Principal object", NULL},
    {"server",       (getter)Credential_get_server,       (setter)NULL, "returns server as Principal object", NULL},
    {"times",        (getter)Credential_get_times,        (setter)NULL, "returns ticket times as TicketTimes object", NULL},
    {"is_skey",      (getter)Credential_get_is_skey,      (setter)NULL, "returns is_skey flag as boolean", NULL},
    {"ticket_flags", (getter)Credential_get_ticket_flags, (setter)NULL, "returns ticket_flags as int", NULL},
    {NULL}  /* Sentinel */
};

static PyMemberDef Credential_members[] = {
    {NULL}  /* Sentinel */
};

/* >>> Credential Class Methods <<< */

static PyObject *
Credential_format_lines(Credential *self, PyObject *args, PyObject *kwds)
{
    static char *kwlist[] = {"level", NULL};
    int level = 0;
    PyObject *lines = NULL;
    PyObject *obj = NULL, *objs = NULL;
    Py_ssize_t index = 0, len = 0;
    char label[128];

    TraceMethodEnter(self);

    if (!PyArg_ParseTupleAndKeywords(args, kwds, "|i:format_lines", kwlist, &level))
        return NULL;

    if ((lines = PyList_New(0)) == NULL) {
        return NULL;
    }

    if (self->credential->client) {
        if ((obj = Principal_new_from_krb5_principal(self->credential->client)) == NULL) goto fail;
    } else {
        obj = Py_None;
        Py_INCREF(obj);
    }
    FMT_OBJ_AND_APPEND(lines, _("Client"), obj, level, fail);
    Py_CLEAR(obj);

    if (self->credential->server) {
        if ((obj = Principal_new_from_krb5_principal(self->credential->server)) == NULL) goto fail;
    } else {
        obj = Py_None;
        Py_INCREF(obj);
    }
    FMT_OBJ_AND_APPEND(lines, _("Server"), obj, level, fail);
    Py_CLEAR(obj);

    if ((obj = TicketTimes_new_from_krb5_ticket_times(&self->credential->times)) == NULL) goto fail;
    CALL_FORMAT_LINES_AND_APPEND(lines, obj, level, fail);
    Py_CLEAR(obj);

    if ((obj = Credential_get_is_skey(self, NULL)) == NULL) goto fail;
    FMT_OBJ_AND_APPEND(lines, _("Is SKey"), obj, level, fail);
    Py_CLEAR(obj);

    if ((obj = ticket_flags_str(self->credential->ticket_flags)) == NULL) goto fail;
    FMT_OBJ_AND_APPEND(lines, _("Flags"), obj, level, fail);
    Py_CLEAR(obj);

    if ((objs = Credential_get_addresses(self, NULL)) == NULL) goto fail;
    if ((len = PySequence_Length(objs)) == -1) goto fail;
    if (len) {
        FMT_LABEL_AND_APPEND(lines, _("Addresses"), level, fail);
        for (index = 0; index < len; index++) {
            snprintf(label, sizeof(label), _("Address %d"), index);
            if ((obj = PySequence_GetItem(objs, index)) == NULL) goto fail;
            FMT_OBJ_AND_APPEND(lines, label, obj, level+1, fail);
            Py_CLEAR(obj);
        }
    } else {
        FMT_LABEL_AND_APPEND(lines, _("Addresses (None)"), level, fail);
    }
    Py_CLEAR(objs);

    FMT_LABEL_AND_APPEND(lines, _("Session Encryption Key"), level, fail);
    if ((obj = KeyBlock_new_from_krb5_keyblock(&self->credential->keyblock)) == NULL) goto fail;
    CALL_FORMAT_LINES_AND_APPEND(lines, obj, level+1, fail);
    Py_CLEAR(obj);

    return lines;
 fail:
    Py_XDECREF(obj);
    Py_XDECREF(objs);
    Py_XDECREF(lines);
    return NULL;
}

static PyObject *
Credential_format(Credential *self, PyObject *args, PyObject *kwds)
{
    TraceMethodEnter(self);

    return format_from_lines((format_lines_func)Credential_format_lines, (PyObject *)self, args, kwds);
}

static PyObject *
Credential_str(Credential *self)
{
    return Credential_format(self, empty_tuple, NULL);
}

/* >>> Credential Class Construction <<< */

static PyObject *
Credential_new(PyTypeObject *type, PyObject *args, PyObject *kwds)
{
    Credential *self;

    TraceObjNewEnter(type);

    if ((self = (Credential *)type->tp_alloc(type, 0)) == NULL) {
        return NULL;
    }

    self->credential = NULL;

    TraceObjNewLeave(self);
    return (PyObject *)self;
}

static void
Credential_dealloc(Credential* self)
{
    TraceMethodEnter(self);
    krb5_context current_context = NULL;

    if ((current_context = get_current_context_no_error()) == NULL) {
        PySys_WriteStderr("No current context set (%s)\n", __FUNCTION__);
    }

    if (current_context && self->credential) {
        krb5_free_creds(current_context, self->credential);
    }

    self->ob_type->tp_free((PyObject*)self);
}

// FIXME, need to add params to Credential constructor.

PyDoc_STRVAR(Credential_doc,
"Credential(client_principal, server_principal, ticket_times=None, flags=0)\n\
\n\
:parameters:\n\
    client_principal : Principal object or principal name\n\
        Client principal\n\
    server_principal : Principal object or principal name\n\
        Server principal\n\
    ticket_times : TicketTimes object\n\
        Optional, credential validity timestamps\n\
    flags : int\n\
        Optional, credential flags (e.g. TKT_FLG_* enumerated constant)\n\
\n\
An object representing Credential.\n\
");

static int
Credential_init(Credential *self, PyObject *args, PyObject *kwds)
{
    static char *kwlist[] = {"client_principal", "server_principal", "ticket_times", "flags", NULL};
    Principal *py_client_principal = NULL;
    Principal *py_server_principal = NULL;
    TicketTimes *py_ticket_times = NULL;
    int flags = 0;
    Principal *py_principal = NULL;
    krb5_error_code krb_error;
    krb5_context current_context = NULL;

    TraceMethodEnter(self);

    if ((current_context = get_current_context()) == NULL) {
        return -1;
    }

    if (!PyArg_ParseTupleAndKeywords(args, kwds, "OO|Oi:Credential", kwlist,
                                     &py_client_principal, &py_server_principal,
                                     &py_ticket_times, &flags))
        return -1;

    /* krb5 library uses malloc/free, so we must use malloc here */
    if ((self->credential = malloc(sizeof(krb5_creds))) == NULL) {
        PyErr_NoMemory();
        return -1;
    }
    memset(self->credential, 0, sizeof(krb5_creds));

    /* client principal */
    PRINCIPAL_FROM_ARG(py_principal, py_client_principal, "client");
    if (py_principal == NULL) {
        return -1;
    }
    if ((krb_error = krb5_copy_principal(current_context,
                                         py_principal->principal,
                                         &self->credential->client))) {
        set_krb_error(krb_error, NULL);
        Py_DECREF(py_principal);
        return -1;
    }
    Py_DECREF(py_principal);

    /* server principal */
    PRINCIPAL_FROM_ARG(py_principal, py_server_principal, "server");
    if (py_principal == NULL) {
        return -1;
    }
    if ((krb_error = krb5_copy_principal(current_context,
                                         py_principal->principal,
                                         &self->credential->server))) {
        set_krb_error(krb_error, NULL);
        Py_DECREF(py_principal);
        return -1;
    }
    Py_DECREF(py_principal);

    /* ticket times */
    if (PyTicketTimes_Check(py_ticket_times) && !PyNone_Check((PyObject *)py_ticket_times)) {
        self->credential->times = py_ticket_times->ticket_times;
    }

    self->credential->ticket_flags = flags;

    return 0;
}


static PyObject *
Credential_new_from_krb5_creds(krb5_creds *krb_credential)
{
    krb5_error_code krb_error;
    krb5_context current_context = NULL;
    Credential *self = NULL;

    TraceObjNewEnter(NULL);

    if ((current_context = get_current_context()) == NULL) {
        return NULL;
    }

    if ((self = (Credential *) CredentialType.tp_new(&CredentialType, NULL, NULL)) == NULL) {
        return NULL;
    }

    if ((krb_error = krb5_copy_creds(current_context, krb_credential, &self->credential))) {
        Py_CLEAR(self);
        TraceObjNewLeave(self);
        return set_krb_error(krb_error, NULL);
    }

    TraceObjNewLeave(self);
    return (PyObject *) self;
}

/* >>> Credential Class Definition <<< */

static PyMethodDef Credential_methods[] = {
    {"format_lines", (PyCFunction)Credential_format_lines,   METH_VARARGS|METH_KEYWORDS, generic_format_lines_doc},
    {"format",       (PyCFunction)Credential_format,         METH_VARARGS|METH_KEYWORDS, generic_format_doc},
    {NULL, NULL}  /* Sentinel */
};


static PyTypeObject CredentialType = {
    PyObject_HEAD_INIT(NULL)
    0,						/* ob_size */
    "krb.Credential",				/* tp_name */
    sizeof(Credential),				/* tp_basicsize */
    0,						/* tp_itemsize */
    (destructor)Credential_dealloc,		/* tp_dealloc */
    0,						/* tp_print */
    0,						/* tp_getattr */
    0,						/* tp_setattr */
    0,						/* tp_compare */
    0,						/* tp_repr */
    0,						/* tp_as_number */
    0,						/* tp_as_sequence */
    0,						/* tp_as_mapping */
    0,						/* tp_hash */
    0,						/* tp_call */
    (reprfunc)Credential_str,			/* tp_str */
    0,						/* tp_getattro */
    0,						/* tp_setattro */
    0,						/* tp_as_buffer */
    Py_TPFLAGS_DEFAULT | Py_TPFLAGS_BASETYPE,	/* tp_flags */
    Credential_doc,				/* tp_doc */
    (traverseproc)0,				/* tp_traverse */
    (inquiry)0,					/* tp_clear */
    0,						/* tp_richcompare */
    0,						/* tp_weaklistoffset */
    0,						/* tp_iter */
    0,						/* tp_iternext */
    Credential_methods,				/* tp_methods */
    Credential_members,				/* tp_members */
    Credential_getseters,				/* tp_getset */
    0,						/* tp_base */
    0,						/* tp_dict */
    0,						/* tp_descr_get */
    0,						/* tp_descr_set */
    0,						/* tp_dictoffset */
    (initproc)Credential_init,			/* tp_init */
    0,						/* tp_alloc */
    Credential_new,				/* tp_new */
};


/* ========================================================================== */
/* ============================= CCache Class ============================== */
/* ========================================================================== */

static PyObject *
CCache_lookup_credential(krb5_ccache ccache, PyObject *py_server_principal_arg)
{
    krb5_error_code krb_error;
    krb5_flags flags = KRB5_TC_MATCH_SRV_NAMEONLY | KRB5_TC_SUPPORTED_KTYPES;
    krb5_principal client_principal = NULL;;
    krb5_creds match_creds;
    krb5_creds found_creds;
    Principal *py_server_principal = NULL;
    PyObject *py_credential = NULL;
    krb5_context current_context = NULL;

    if ((current_context = get_current_context()) == NULL) {
        return NULL;
    }

    memset(&match_creds, 0, sizeof(match_creds));
    memset(&found_creds, 0, sizeof(found_creds));

    PRINCIPAL_FROM_ARG(py_server_principal, py_server_principal_arg, "server");
    if (py_server_principal == NULL) {
        goto exit;
    }

    if ((krb_error = krb5_cc_get_principal(current_context, ccache, &client_principal))) {
        return set_krb_error(krb_error, NULL);
    }

    match_creds.client = client_principal;
    match_creds.server = py_server_principal->principal;

    if ((krb_error = krb5_cc_retrieve_cred(current_context, ccache,
                                           flags, &match_creds, &found_creds))) {
        if (krb_error == KRB5_CC_NOTFOUND) {
            PyObject *py_name = PyObject_Str((PyObject *)py_server_principal);

            PyErr_Format(PyExc_KeyError, "principal not found: \"%s\"", PyString_AsString(py_name));
            Py_XDECREF(py_name);
        } else {
            set_krb_error(krb_error, NULL);
        }
        goto exit;
    }

    py_credential = Credential_new_from_krb5_creds(&found_creds);

 exit:
    Py_XDECREF(py_server_principal);
    if (client_principal) {
        krb5_free_principal(current_context, client_principal);
    }
    krb5_free_cred_contents(current_context, &found_creds);
    return py_credential;
}
/* >>> CCache Attribute Access <<< */

static PyObject *
CCache_get_type(CCache *self, void *closure)
{
    krb5_context current_context = NULL;

    TraceMethodEnter(self);

    if ((current_context = get_current_context()) == NULL) {
        return NULL;
    }

    return PyString_FromString(krb5_cc_get_type(current_context, self->ccache));
}

static PyObject *
CCache_get_name(CCache *self, void *closure)
{
    krb5_context current_context = NULL;

    TraceMethodEnter(self);

    if ((current_context = get_current_context()) == NULL) {
        return NULL;
    }

    return PyString_FromString(krb5_cc_get_name(current_context, self->ccache));
}

static PyObject *
CCache_get_principal(CCache *self, void *closure)
{
    krb5_error_code krb_error;
    krb5_context current_context = NULL;
    krb5_principal principal = NULL;;
    PyObject *py_principal = NULL;

    TraceMethodEnter(self);

    if ((current_context = get_current_context()) == NULL) {
        return NULL;
    }

    if ((krb_error = krb5_cc_get_principal(current_context, self->ccache, &principal))) {
        return set_krb_error(krb_error, NULL);
    }

    py_principal = Principal_new_from_krb5_principal(principal);
    krb5_free_principal(current_context, principal);
    return py_principal;

}

static
PyGetSetDef CCache_getseters[] = {
    {"type",             (getter)CCache_get_type,             (setter)NULL, "type (i.e. FILE|MEMORY) as string", NULL},
    {"name",             (getter)CCache_get_name,             (setter)NULL, "name (i.e. file pathname when type=='FILE') as string", NULL},
    {"principal",        (getter)CCache_get_principal,        (setter)NULL, "principal as Principal object", NULL},
    {NULL}  /* Sentinel */
};

static PyMemberDef CCache_members[] = {
    {NULL}  /* Sentinel */
};

/* >>> CCache Class Methods <<< */

PyDoc_STRVAR(CCache_initialize_doc,
"initialize(principal)\n\
\n\
:parameters:\n\
    principal : Principal object or principal name\n\
        Default principal.\n\
:returns:\n\
    None\n\
\n\
Destroy any existing contents of cache and initialize it for the\n\
default principal principal.\n\
");

static PyObject *
CCache_initialize(CCache *self, PyObject *args, PyObject *kwds)
{
    static char *kwlist[] = {"principal", NULL};
    PyObject *py_principal_arg = NULL;
    Principal *py_principal = NULL;
    krb5_error_code krb_error;
    krb5_context current_context = NULL;

    TraceMethodEnter(self);

    if ((current_context = get_current_context()) == NULL) {
        return NULL;
    }

    if (!PyArg_ParseTupleAndKeywords(args, kwds, "O:initialize", kwlist,
                                     &py_principal_arg))
        return NULL;

    PRINCIPAL_FROM_ARG(py_principal, py_principal_arg, "default");
    if (py_principal == NULL) {
        goto fail;
    }

    if ((krb_error = krb5_cc_initialize(current_context, self->ccache, py_principal->principal))) {
        set_krb_error(krb_error, NULL);
        goto fail;
    }

    Py_DECREF(py_principal);
    Py_RETURN_NONE;

fail:
    Py_XDECREF(py_principal);
    return NULL;
}

PyDoc_STRVAR(CCache_store_credential_doc,
"store_credential(credential)\n\
\n\
:parameters:\n\
    credential : Credential object \n\
        Credential to store.\n\
:returns:\n\
    None\n\
\n\
Stores the given credential in the ccache.\n\
");

static PyObject *
CCache_store_credential(CCache *self, PyObject *args)
{
    Credential *py_credential = NULL;
    krb5_error_code krb_error;
    krb5_context current_context = NULL;

    TraceMethodEnter(self);

    if ((current_context = get_current_context()) == NULL) {
        return NULL;
    }

    if (!PyArg_ParseTuple(args, "O!:store_credential",
                          &CredentialType, &py_credential))
        return NULL;

    if ((krb_error = krb5_cc_store_cred(current_context, self->ccache, py_credential->credential))) {
        return set_krb_error(krb_error, NULL);
    }

    Py_RETURN_NONE;
}

PyDoc_STRVAR(CCache_close_doc,
"close() -> None\n\
\n\
:returns:\n\
    None\n\
\n\
Closes the credential cache.\n\
");

static PyObject *
CCache_close(CCache *self, PyObject *args)
{
    krb5_error_code krb_error;
    krb5_context current_context = NULL;

    TraceMethodEnter(self);

    if ((current_context = get_current_context()) == NULL) {
        return NULL;
    }

    if ((krb_error = krb5_cc_close(current_context, self->ccache))) {
        return set_krb_error(krb_error, NULL);
    }

    Py_RETURN_NONE;
}

static PyObject *
CCache_format_lines(CCache *self, PyObject *args, PyObject *kwds)
{
    static char *kwlist[] = {"level", NULL};
    int level = 0;
    PyObject *lines = NULL;
    PyObject *obj = NULL;
    krb5_error_code krb_error;
    krb5_context current_context = NULL;
    krb5_principal client_principal = NULL;;
    krb5_cc_cursor cursor = NULL;
    krb5_creds credential;
    int index = 0;

    TraceMethodEnter(self);

    if ((current_context = get_current_context()) == NULL) {
        return NULL;
    }

    if (!PyArg_ParseTupleAndKeywords(args, kwds, "|i:format_lines", kwlist, &level))
        return NULL;

    if ((lines = PyList_New(0)) == NULL) {
        return NULL;
    }

    if ((obj = PyString_FromFormat("%s:%s",
                                   krb5_cc_get_type(current_context, self->ccache),
                                   krb5_cc_get_name(current_context, self->ccache))) == NULL) goto fail;

    FMT_OBJ_AND_APPEND(lines, _("Ticket cache"), obj, level, fail);
    Py_CLEAR(obj);

    if ((krb_error = krb5_cc_get_principal(current_context, self->ccache, &client_principal))) {
        set_krb_error(krb_error, NULL);
        goto fail;
    }

    if ((obj = Principal_new_from_krb5_principal(client_principal)) == NULL) goto fail;
    FMT_OBJ_AND_APPEND(lines, _("Default principal"), obj, level, fail);
    Py_CLEAR(obj);

    if ((krb_error = krb5_cc_start_seq_get(current_context, self->ccache, &cursor))) {
        set_krb_error(krb_error, NULL);
        goto fail;
    }

    while (!(krb_error = krb5_cc_next_cred(current_context, self->ccache, &cursor, &credential))) {
        if ((obj = PyString_FromFormat("Ticket %d", index)) == NULL) {
            krb5_free_cred_contents(current_context, &credential);
            goto fail;
        }
        FMT_LABEL_AND_APPEND(lines, PyString_AsString(obj), level, fail);
        Py_CLEAR(obj);

        if ((obj = Credential_new_from_krb5_creds(&credential)) == NULL) {
            krb5_free_cred_contents(current_context, &credential);
            goto fail;
        }
        krb5_free_cred_contents(current_context, &credential);

        CALL_FORMAT_LINES_AND_APPEND(lines, obj, level+1, fail);
        Py_CLEAR(obj);

        index++;
    }
    if (krb_error != KRB5_CC_END) {
        set_krb_error(krb_error, NULL);
        goto fail;
    }

    if ((obj = PyInt_FromLong(index)) == NULL) goto fail;
    FMT_OBJ_AND_APPEND(lines, _("Total Tickets"), obj, level, fail);
    Py_CLEAR(obj);

    return lines;

 fail:
    if (cursor) {
        krb5_cc_end_seq_get(current_context, self->ccache, &cursor);
    }

    Py_XDECREF(obj);
    Py_XDECREF(lines);
    return NULL;
}

static PyObject *
CCache_format(CCache *self, PyObject *args, PyObject *kwds)
{
    TraceMethodEnter(self);

    return format_from_lines((format_lines_func)CCache_format_lines, (PyObject *)self, args, kwds);
}

static PyObject *
CCache_str(CCache *self)
{
    return CCache_format(self, empty_tuple, NULL);
}


/* >>> CCache Class Construction <<< */

static PyObject *
CCache_new(PyTypeObject *type, PyObject *args, PyObject *kwds)
{
    CCache *self;

    TraceObjNewEnter(type);

    if ((self = (CCache *)type->tp_alloc(type, 0)) == NULL) {
        return NULL;
    }

    self->ccache = NULL;

    TraceObjNewLeave(self);
    return (PyObject *)self;
}

static void
CCache_dealloc(CCache* self)
{
    TraceMethodEnter(self);
    krb5_context current_context = NULL;

    if ((current_context = get_current_context_no_error()) == NULL) {
        PySys_WriteStderr("No current context set (%s)\n", __FUNCTION__);
    }

    if (current_context && self->ccache) {
        krb5_cc_close(current_context, self->ccache);
    }

    self->ob_type->tp_free((PyObject*)self);
}

PyDoc_STRVAR(CCache_doc,
"CCache(name=string)\n\
\n\
:parameters:\n\
    name : string\n\
        Optional, the name of an existing ccache to open. The name may\n\
        optionally be prefixed with the type (e.g. FILE, MEMORY, DIR,\n\
        KEYRING, etc.) followed by a colon (:). If no type is specified the\n\
        type defaults to FILE. If no name is supplied then the default\n\
        credential cache is opened.\n\
\n\
:returns:\n\
    CCache object \n\
\n\
An object representing a Kerberos credential cache.\n\
\n\
There are several ways to create a CCache. This constructor opens an\n\
existing ccache.  If a name is supplied then that ccache is opened. If\n\
no name is supplied the default ccache is opened.\n\
");

static int
CCache_init(CCache *self, PyObject *args, PyObject *kwds)
{
    static char *kwlist[] = {"name", NULL};
    PyObject *py_name = NULL;
    PyObject *py_name_utf8 = NULL;
    krb5_error_code krb_error;
    krb5_context current_context = NULL;

    TraceMethodEnter(self);

    if ((current_context = get_current_context()) == NULL) {
        return -1;
    }

    if (!PyArg_ParseTupleAndKeywords(args, kwds, "|O:CCache", kwlist,
                                     &py_name))
        return -1;

    if (py_name) {
        if ((py_name_utf8 = PyString_UTF8(py_name, "ccache name")) == NULL) {
            return -1;
        }

        if ((krb_error = krb5_cc_resolve(current_context, PyString_AsString(py_name_utf8), &self->ccache))) {
            set_krb_error(krb_error, "cannot open ccache \"%s\"", PyString_AsString(py_name_utf8));
            return -1;
        }
    } else {
        if ((krb_error = krb5_cc_default(current_context, &self->ccache))) {
            set_krb_error(krb_error, "cannot open default ccache");
            return -1;
        }
    }

    return 0;
}


PyDoc_STRVAR(CCache_new_unique_doc,
"CCache_new_unique(type, hint)\n\
\n\
:parameters:\n\
    type : string\n\
        Optional, The type (e.g. FILE, MEMORY, DIR, KEYRING, etc.) of\n\
        the ccache.  Other types may be available if they have been\n\
        registered.\n\
    hint : string\n\
        Optional, a hint for creating the ccache.\n\
        Currently unsed by Kerberos library.\n\
:returns:\n\
    CCache object \n\
\n\
Creates a new CCache of the specified type which is unique.\n\
");

static PyObject *
CCache_new_unique(CCache *self, PyObject *args, PyObject *kwds)
{
    static char *kwlist[] = {"type", "hint", NULL};
    char *type = NULL;
    char *hint = NULL;
    krb5_error_code krb_error;
    krb5_context current_context = NULL;
    krb5_ccache ccache = NULL;

    TraceMethodEnter(self);

    if ((current_context = get_current_context()) == NULL) {
        return NULL;
    }

    if (!PyArg_ParseTupleAndKeywords(args, kwds, "|ss:new_unique", kwlist,
                                     &type, &hint))
        return NULL;

    if ((krb_error = krb5_cc_new_unique(current_context, type, hint, &ccache))) {
        return set_krb_error(krb_error, NULL);
    }

    return CCache_new_from_krb5_ccache(ccache);
}

static PyObject *
CCache_new_from_krb5_ccache(krb5_ccache ccache)
{
    CCache *self = NULL;

    TraceObjNewEnter(NULL);

    if ((self = (CCache *) CCacheType.tp_new(&CCacheType, NULL, NULL)) == NULL) {
        return NULL;
    }

    self->ccache = ccache;

    TraceObjNewLeave(self);
    return (PyObject *) self;
}

/* >>> CCache Sequence <<< */

static Py_ssize_t
CCache_length(CCache *self)
{
    krb5_error_code krb_error;
    krb5_context current_context = NULL;
    krb5_cc_cursor cursor = NULL;
    krb5_creds credential;
    krb5_int32 length = 0;

    if ((current_context = get_current_context()) == NULL) {
        return -1;
    }

    if ((krb_error = krb5_cc_start_seq_get(current_context, self->ccache, &cursor))) {
        set_krb_error(krb_error, NULL);
        return -1;
    }

    while (!(krb_error = krb5_cc_next_cred(current_context, self->ccache, &cursor, &credential))) {
        krb5_free_cred_contents(current_context, &credential);
        length++;
    }

    krb5_cc_end_seq_get(current_context, self->ccache, &cursor);
    if (krb_error != KRB5_CC_END) {
        set_krb_error(krb_error, NULL);
        return -1;
    }

    return length;
}

static PyObject *
CCache_item(CCache *self, register Py_ssize_t i)
{
    krb5_error_code krb_error;
    krb5_context current_context = NULL;
    krb5_cc_cursor cursor = NULL;
    krb5_creds credential;
    Py_ssize_t index = 0;
    PyObject *py_credential = NULL;

    if ((current_context = get_current_context()) == NULL) {
        return NULL;
    }

    if (i < 0) {
        PyErr_SetString(PyExc_IndexError, "CCache index out of range");
        return NULL;
    }

    if ((krb_error = krb5_cc_start_seq_get(current_context, self->ccache, &cursor))) {
        return set_krb_error(krb_error, NULL);
    }

    while (!(krb_error = krb5_cc_next_cred(current_context, self->ccache, &cursor, &credential))) {
        if (index == i) {
            py_credential = Credential_new_from_krb5_creds(&credential);
            krb5_free_cred_contents(current_context, &credential);
            krb5_cc_end_seq_get(current_context, self->ccache, &cursor);
            return py_credential;
        }
        krb5_free_cred_contents(current_context, &credential);
        index++;
    }
    krb5_cc_end_seq_get(current_context, self->ccache, &cursor);

    if (krb_error != KRB5_CC_END) {
        return set_krb_error(krb_error, NULL);
    }

    PyErr_SetString(PyExc_IndexError, "CCache index out of range");
    return NULL;
}

static PyObject *
CCache_slice(CCache *self, Py_ssize_t low, Py_ssize_t high)
{
    krb5_int32 length = 0;
    Py_ssize_t n_items = 0;
    PyObject *list = NULL;
    Py_ssize_t i;
    PyObject *py_credential = NULL;

    length = CCache_length(self);

    if (low < 0)
        low = 0;
    if (high < 0)
        high = 0;
    if (high > length)
        high = length;
    if (high < low)
        high = low;

    n_items = high - low;

    if ((list = PyList_New(n_items)) == NULL) {
        return NULL;
    }

    for (i = 0; i < n_items; i++) {
        if ((py_credential = CCache_item(self, i)) == NULL) {
            Py_DECREF(list);
            return NULL;
        }
        PyList_SetItem(list, i, py_credential);
    }

    return list;
}

static PyObject*
CCache_subscript(CCache *self, PyObject* item)
{
    PyObject* result;

    if (PyIndex_Check(item)) {
        Py_ssize_t i = PyNumber_AsSsize_t(item, PyExc_IndexError);

        if (i == -1 && PyErr_Occurred())
            return NULL;
        if (i < 0)
            i += CCache_length(self);
        return CCache_item(self, i);
    } else if (PySlice_Check(item)) {
        Py_ssize_t start, stop, step, slicelength, cur, i;
        PyObject* py_ava;

        if (PySlice_GetIndicesEx((PySliceObject*)item, CCache_length(self),
				 &start, &stop, &step, &slicelength) < 0) {
            return NULL;
        }

        if (slicelength <= 0) {
            return PyList_New(0);
        } else {
            result = PyList_New(slicelength);
            if (!result) return NULL;

            for (cur = start, i = 0; i < slicelength; cur += step, i++) {
                /* We don't need to bump the ref count because CCache_item
                 * returns a new object */
                py_ava = CCache_item(self, cur);
                if (PyList_SetItem(result, i, py_ava) == -1) {
                    Py_DECREF(result);
                    return NULL;
                }
            }
            return result;
	}
    } else if (PyString_Check(item) || PyUnicode_Check(item) || PyPrincipal_Check(item)) {
        result = CCache_lookup_credential(self->ccache, item);
        return result;

    } else {
        PyErr_Format(PyExc_TypeError,
                     "indices must be integers, strings or Principal, not %.200s",
                     item->ob_type->tp_name);
        return NULL;
    }
    return NULL;
}

static PySequenceMethods CCache_as_sequence = {
    (lenfunc)CCache_length,			/* sq_length */
    0,						/* sq_concat */
    0,						/* sq_repeat */
    (ssizeargfunc)CCache_item,			/* sq_item */
    (ssizessizeargfunc)CCache_slice,		/* sq_slice */
    0,						/* sq_ass_item */
    0,						/* sq_ass_slice */
    0,						/* sq_contains */
    0,						/* sq_inplace_concat */
    0,						/* sq_inplace_repeat */
};


static PyMappingMethods CCache_as_mapping = {
    (lenfunc)CCache_length,			/* mp_length */
    (binaryfunc)CCache_subscript,		/* mp_subscript */
    0,						/* mp_ass_subscript */
};

/* >>> CCache Class Definition <<< */

static PyMethodDef CCache_methods[] = {
    {"format_lines",        (PyCFunction)CCache_format_lines,        METH_VARARGS|METH_KEYWORDS,            generic_format_lines_doc},
    {"format",              (PyCFunction)CCache_format,              METH_VARARGS|METH_KEYWORDS,            generic_format_doc},
    {"new_unique",          (PyCFunction)CCache_new_unique,          METH_VARARGS|METH_KEYWORDS|METH_CLASS, CCache_new_unique_doc},
    {"initialize",          (PyCFunction)CCache_initialize,          METH_VARARGS|METH_KEYWORDS,            CCache_initialize_doc},
    {"store_credential",    (PyCFunction)CCache_store_credential,    METH_VARARGS,                          CCache_store_credential_doc},
    {"close",               (PyCFunction)CCache_close,               METH_NOARGS,                           CCache_close_doc},
    {NULL, NULL}  /* Sentinel */
};

static PyTypeObject CCacheType = {
    PyObject_HEAD_INIT(NULL)
    0,						/* ob_size */
    "krb.CCache",				/* tp_name */
    sizeof(CCache),				/* tp_basicsize */
    0,						/* tp_itemsize */
    (destructor)CCache_dealloc,			/* tp_dealloc */
    0,						/* tp_print */
    0,						/* tp_getattr */
    0,						/* tp_setattr */
    0,						/* tp_compare */
    0,						/* tp_repr */
    0,						/* tp_as_number */
    &CCache_as_sequence,			/* tp_as_sequence */
    &CCache_as_mapping,				/* tp_as_mapping */
    0,						/* tp_hash */
    0,						/* tp_call */
    (reprfunc)CCache_str,			/* tp_str */
    0,						/* tp_getattro */
    0,						/* tp_setattro */
    0,						/* tp_as_buffer */
    Py_TPFLAGS_DEFAULT | Py_TPFLAGS_BASETYPE,	/* tp_flags */
    CCache_doc,				/* tp_doc */
    (traverseproc)0,				/* tp_traverse */
    (inquiry)0,					/* tp_clear */
    0,						/* tp_richcompare */
    0,						/* tp_weaklistoffset */
    0,						/* tp_iter */
    0,						/* tp_iternext */
    CCache_methods,				/* tp_methods */
    CCache_members,				/* tp_members */
    CCache_getseters,				/* tp_getset */
    0,						/* tp_base */
    0,						/* tp_dict */
    0,						/* tp_descr_get */
    0,						/* tp_descr_set */
    0,						/* tp_dictoffset */
    (initproc)CCache_init,			/* tp_init */
    0,						/* tp_alloc */
    CCache_new,				/* tp_new */
};

/* ========================================================================== */
/* =========================== KeytabEntry Class ============================ */
/* ========================================================================== */

/* >>> KeytabEntry Attribute Access <<< */

static PyObject *
KeytabEntry_get_principal(KeytabEntry *self, void *closure)
{
    TraceMethodEnter(self);

    return Principal_new_from_krb5_principal(self->keytab_entry.principal);
}

static PyObject *
KeytabEntry_get_timestamp(KeytabEntry *self, void *closure)
{
    TraceMethodEnter(self);

    return datetime_from_timestamp(self->keytab_entry.timestamp);
}

static PyObject *
KeytabEntry_get_vno(KeytabEntry *self, void *closure)
{
    TraceMethodEnter(self);

    return PyInt_FromLong(self->keytab_entry.vno);
}

static
PyGetSetDef KeytabEntry_getseters[] = {
    {"principal", (getter)KeytabEntry_get_principal,    (setter)NULL, "principal as Principal object", NULL},
    {"timestamp", (getter)KeytabEntry_get_timestamp,    (setter)NULL, "time entry written to keytable, as datetime object", NULL},
    {"vno",       (getter)KeytabEntry_get_vno,          (setter)NULL, "key version number as an int", NULL},
    {NULL}  /* Sentinel */
};

static PyMemberDef KeytabEntry_members[] = {
    {NULL}  /* Sentinel */
};

/* >>> KeytabEntry Class Methods <<< */

PyDoc_STRVAR(KeytabEntry_func_name_doc,
"func_name() -> \n\
\n\
:parameters:\n\
    arg1 : object\n\
        xxx\n\
:returns:\n\
    xxx\n\
\n\
xxx\n\
");

static PyObject *
KeytabEntry_func_name(KeytabEntry *self, PyObject *args, PyObject *kwds)
{
    static char *kwlist[] = {"arg1", NULL};
    PyObject *arg;
    krb5_context current_context = NULL;

    TraceMethodEnter(self);

    if ((current_context = get_current_context()) == NULL) {
        return NULL;
    }

    if (!PyArg_ParseTupleAndKeywords(args, kwds, "O|i:func_name", kwlist,
                                     &arg))
        return NULL;

    return NULL;
}

static PyObject *
KeytabEntry_format_lines(KeytabEntry *self, PyObject *args, PyObject *kwds)
{
    static char *kwlist[] = {"level", NULL};
    int level = 0;
    PyObject *lines = NULL;
    PyObject *obj = NULL;

    TraceMethodEnter(self);

    if (!PyArg_ParseTupleAndKeywords(args, kwds, "|i:format_lines", kwlist, &level))
        return NULL;

    if ((lines = PyList_New(0)) == NULL) {
        return NULL;
    }

    if ((obj = Principal_new_from_krb5_principal(self->keytab_entry.principal)) == NULL) goto fail;
    FMT_OBJ_AND_APPEND(lines, _("Principal"), obj, level, fail);
    Py_CLEAR(obj);

    if ((obj = KeytabEntry_get_timestamp(self, NULL)) == NULL) goto fail;
    FMT_OBJ_AND_APPEND(lines, _("Timestamp"), obj, level, fail);
    Py_CLEAR(obj);

    if ((obj = PyString_FromFormat("%u (%0x)", self->keytab_entry.vno, self->keytab_entry.vno)) == NULL) goto fail;
    FMT_OBJ_AND_APPEND(lines, _("Vno"), obj, level, fail);
    Py_CLEAR(obj);

    if ((obj = KeyBlock_new_from_krb5_keyblock(&self->keytab_entry.key)) == NULL) goto fail;
    CALL_FORMAT_LINES_AND_APPEND(lines, obj, level+1, fail);
    Py_CLEAR(obj);


    return lines;
 fail:
    Py_XDECREF(obj);
    Py_XDECREF(lines);
    return NULL;
}

static PyObject *
KeytabEntry_format(KeytabEntry *self, PyObject *args, PyObject *kwds)
{
    TraceMethodEnter(self);

    return format_from_lines((format_lines_func)KeytabEntry_format_lines, (PyObject *)self, args, kwds);
}

static PyObject *
KeytabEntry_str(KeytabEntry *self)
{
    return KeytabEntry_format(self, empty_tuple, NULL);
}

/* >>> KeytabEntry Class Construction <<< */

static PyObject *
KeytabEntry_new(PyTypeObject *type, PyObject *args, PyObject *kwds)
{
    KeytabEntry *self;

    TraceObjNewEnter(type);

    if ((self = (KeytabEntry *)type->tp_alloc(type, 0)) == NULL) {
        return NULL;
    }

    memset(&self->keytab_entry, 0, sizeof(krb5_keytab_entry));

    TraceObjNewLeave(self);
    return (PyObject *)self;
}

static void
KeytabEntry_dealloc(KeytabEntry* self)
{
    krb5_context current_context = NULL;

    TraceMethodEnter(self);

    if ((current_context = get_current_context()) != NULL) {
        krb5_free_keytab_entry_contents(current_context, &self->keytab_entry);
    }

    self->ob_type->tp_free((PyObject*)self);
}

PyDoc_STRVAR(KeytabEntry_doc,
"KeytabEntry(obj)\n\
\n\
:parameters:\n\
    obj : xxx\n\
:returns:\n\
    xxx\n\
\n\
An object representing KeytabEntry.\n\
");

static int
KeytabEntry_init(KeytabEntry *self, PyObject *args, PyObject *kwds)
{
    static char *kwlist[] = {"arg", NULL};
    PyObject *arg = NULL;
    krb5_context current_context = NULL;

    TraceMethodEnter(self);

    if ((current_context = get_current_context()) == NULL) {
        return -1;
    }

    if (!PyArg_ParseTupleAndKeywords(args, kwds, "O|i:KeytabEntry", kwlist,
                                     &arg))
        return -1;

    return 0;
}


static PyObject *
KeytabEntry_new_from_krb5_keytab_entry(krb5_keytab_entry *keytab_entry)
{
    krb5_error_code krb_error;
    KeytabEntry *self = NULL;
    krb5_context current_context = NULL;

    TraceObjNewEnter(NULL);

    if ((current_context = get_current_context()) == NULL) {
        return NULL;
    }

    if ((self = (KeytabEntry *) KeytabEntryType.tp_new(&KeytabEntryType, NULL, NULL)) == NULL) {
        return NULL;
    }

    self->keytab_entry.magic = keytab_entry->magic;

    if ((krb_error = krb5_copy_principal(current_context, keytab_entry->principal, &self->keytab_entry.principal))) {
        Py_CLEAR(self);
        TraceObjNewLeave(self);
        return set_krb_error(krb_error, NULL);
    }

    self->keytab_entry.timestamp = keytab_entry->timestamp;
    self->keytab_entry.vno = keytab_entry->vno;

    if ((krb_error = krb5_copy_keyblock_contents(current_context, &keytab_entry->key, &self->keytab_entry.key))) {
        Py_CLEAR(self);
        TraceObjNewLeave(self);
        return set_krb_error(krb_error, NULL);
    }

    TraceObjNewLeave(self);
    return (PyObject *) self;
}


/* >>> KeytabEntry Class Definition <<< */

static PyMethodDef KeytabEntry_methods[] = {
    {"format_lines", (PyCFunction)KeytabEntry_format_lines,   METH_VARARGS|METH_KEYWORDS, generic_format_lines_doc},
    {"format",       (PyCFunction)KeytabEntry_format,         METH_VARARGS|METH_KEYWORDS, generic_format_doc},
    {"func_name", (PyCFunction)KeytabEntry_func_name, METH_VARARGS|METH_KEYWORDS, KeytabEntry_func_name_doc},
    {NULL, NULL}  /* Sentinel */
};

static PyTypeObject KeytabEntryType = {
    PyObject_HEAD_INIT(NULL)
    0,						/* ob_size */
    "krb.KeytabEntry",				/* tp_name */
    sizeof(KeytabEntry),				/* tp_basicsize */
    0,						/* tp_itemsize */
    (destructor)KeytabEntry_dealloc,		/* tp_dealloc */
    0,						/* tp_print */
    0,						/* tp_getattr */
    0,						/* tp_setattr */
    0,						/* tp_compare */
    0,						/* tp_repr */
    0,						/* tp_as_number */
    0,						/* tp_as_sequence */
    0,						/* tp_as_mapping */
    0,						/* tp_hash */
    0,						/* tp_call */
    (reprfunc)KeytabEntry_str,			/* tp_str */
    0,						/* tp_getattro */
    0,						/* tp_setattro */
    0,						/* tp_as_buffer */
    Py_TPFLAGS_DEFAULT | Py_TPFLAGS_BASETYPE,	/* tp_flags */
    KeytabEntry_doc,				/* tp_doc */
    (traverseproc)0,				/* tp_traverse */
    (inquiry)0,					/* tp_clear */
    0,						/* tp_richcompare */
    0,						/* tp_weaklistoffset */
    0,						/* tp_iter */
    0,						/* tp_iternext */
    KeytabEntry_methods,				/* tp_methods */
    KeytabEntry_members,				/* tp_members */
    KeytabEntry_getseters,				/* tp_getset */
    0,						/* tp_base */
    0,						/* tp_dict */
    0,						/* tp_descr_get */
    0,						/* tp_descr_set */
    0,						/* tp_dictoffset */
    (initproc)KeytabEntry_init,			/* tp_init */
    0,						/* tp_alloc */
    KeytabEntry_new,				/* tp_new */
};
/* ========================================================================== */


PyDoc_STRVAR(krb_build_principal_name_doc,
"build_principal_name(components, realm) -> string\n\
\n\
:parameters:\n\
  components : string or sequence of strings\n\
    string or a sequence (list or tuple) of component strings\n\
  realm : string\n\
    the principal's realm\n\
\n\
Examples:\n\
\n\
>>> build_principal_name('admin', 'EXAMPLE.COM')\n\
'admin@EXAMPLE.COM'\n\
\n\
>>> build_principal_name(['HTTP','webserver.example.com'], 'EXAMPLE.COM')\n\
'HTTP/webserver.example.com@EXAMPLE.COM'\n\
\n\
>>> build_principal_name(('kadmin', 'changepw'), 'EXAMPLE.COM')\n\
'kadmin/changepw@EXAMPLE.COM'\n\
");
static PyObject *
krb_build_principal_name(PyObject *self, PyObject *args)
{
    PyObject *py_components = NULL;
    PyObject *py_realm = NULL;
    Py_ssize_t n_components, i;
    PyObject *py_component = NULL;
    PyObject *py_principal = NULL;
    PyObject *py_utf8 = NULL;
    PyObject *py_component_separator = NULL;
    PyObject *py_realm_separator = NULL;
    bool      components_is_sequence;

    TraceMethodEnter(self);

    if (!PyArg_ParseTuple(args, "OO:build_principal_name",
                          &py_components, &py_realm))
        return NULL;

    if (PyString_Check(py_components) || PyUnicode_Check(py_components)) {
        components_is_sequence = false;
    } else if (PyTuple_Check(py_components) || PyList_Check(py_components)) {
        components_is_sequence = true;
    } else {
        PyErr_Format(PyExc_TypeError, "components must be a string or list or tuple, not %.200s",
                     Py_TYPE(py_components)->tp_name);
        return NULL;
    }

    if ((py_realm_separator = PyString_FromString("@")) == NULL) {
        goto fail;
    }

    if ((py_principal = PyString_FromStringAndSize(NULL, 0)) == NULL) {
        return NULL;
    }

    if (components_is_sequence) {
        if ((py_component_separator = PyString_FromString("/")) == NULL) {
            goto fail;
        }

        n_components = PySequence_Length(py_components);

        for (i = 0; i < n_components; i++) {
            py_component = PySequence_ITEM(py_components, i);
            if ((py_utf8 = PyString_UTF8(py_component, "component")) == NULL) {
                goto fail;
            }
            PyString_ConcatAndDel(&py_principal, py_utf8);
            if (py_principal == NULL) {
                goto fail;
            }

            if (i < n_components - 1) {
                PyString_Concat(&py_principal, py_component_separator);
                if (py_principal == NULL) {
                    goto fail;
                }
            }
        }
    } else {
        if ((py_utf8 = PyString_UTF8(py_components, "components")) == NULL) {
            goto fail;
        }
        PyString_ConcatAndDel(&py_principal, py_utf8);
        if (py_principal == NULL) {
            goto fail;
        }
    }

    PyString_Concat(&py_principal, py_realm_separator);
    if (py_principal == NULL) {
        goto fail;
    }

    if ((py_utf8 = PyString_UTF8(py_realm, "realm")) == NULL) {
        goto fail;
    }
    PyString_ConcatAndDel(&py_principal, py_utf8);
    if (py_principal == NULL) {
        goto fail;
    }

    Py_XDECREF(py_component_separator);
    Py_DECREF(py_realm_separator);

    return py_principal;

 fail:
    Py_XDECREF(py_component_separator);
    Py_XDECREF(py_realm_separator);
    Py_XDECREF(py_principal);
    return NULL;
}

PyDoc_STRVAR(krb_error_message_doc,
"error_message(error_code) -> string\n\
\n\
:parameters:\n\
    error_code : int\n\
        Kerberos error code\n\
:returns:\n\
    error description as string\n\
\n\
Given a Kerberos error code return the string description\n\
of the error.\n\
");

static PyObject *
krb_error_message(PyObject *self, PyObject *args, PyObject *kwds)
{
    long error_code = 0;
    const char *error_desc = NULL;
    PyObject *py_message = NULL;
    krb5_context current_context = NULL;

    TraceMethodEnter(self);

    if ((current_context = get_current_context()) == NULL) {
        return NULL;
    }

    if (!PyArg_ParseTuple(args, "l:error_message", &error_code))
        return NULL;

    if ((error_desc = krb5_get_error_message(current_context, error_code))) {
        py_message = PyString_FromString(error_desc);
        krb5_free_error_message(current_context, error_desc);
    } else {
        PyErr_Format(PyExc_ValueError, "Unable to lookup error message for error code (%ld)", error_code);
    }

    return py_message;
}


PyDoc_STRVAR(krb_ticket_flags_str_doc,
"ticket_flags_str(ticket_flags) -> [string]\n\
\n\
:parameters:\n\
    ticket_flags : int\n\
        bitmask of Kerberos ticket flags\n\
:returns:\n\
    sorted list of ticket names, one for each flag enabled.\n\
\n\
Given a Kerberos ticket flags bitmask return a sorted list compromised\n\
of the names of each flag enabled in the bitmask.\n\
");
static PyObject *
krb_ticket_flags_str(PyObject *self, PyObject *args)
{
    int flags = 0;

    TraceMethodEnter(self);

    if (!PyArg_ParseTuple(args, "i:ticket_flags_str", &flags))
        return NULL;

    return ticket_flags_str(flags);

}

PyDoc_STRVAR(krb_set_current_context_doc,
"set_current_context(context) -> None\n\
\n\
:parameters:\n\
    context : Context object\n\
        The Kerberos context to use.\n\
:returns:\n\
    None\n\
\n\
Sets the current Kerberos context for a thread. At any given time each\n\
thread has one current context which is set with this function. If no\n\
context has been set the threads current context will be None and an\n\
exception will be raised by any Python Kerberos function needing\n\
access to the current context.\n\
\n\
Background; all Kerberous C library functions require a Kerberos\n\
context. How should this be accomplished in this Python binding?\n\
\n\
    * Have the module allocate a default and use it internally.\n\
      However, there are different ways contexts can be created,\n\
      this would not accommodate needing a specific context.\n\
\n\
    * If a specific context was needed it could be passed as an\n\
      optional keyword parameter that would override the default\n\
      module context. But then the user would need to pass this extra\n\
      parameter to every function and method they invoke. This is not\n\
      programmer friendly, it can also lead to unexpected problems if\n\
      the extra optional context argument is inadvertantly omitted\n\
      from just one call.\n\
\n\
    * Adding an optional keyword argument is not an option for another\n\
      reason. Some parts of the binding, for example in object\n\
      properties, it is not possible to pass another argument, yet\n\
      internally the CPython code still needs access to a context in\n\
      order to call the C Kerberos library.\n\
\n\
    * Have the user set a current context which is maintained as a\n\
      thread local variable. All elements of the Python binding access\n\
      this thread local variable. There is no need to manage extra\n\
      arguments. The user has the freedom to create whatever type of\n\
      context they need and not be at the mercy of a default picked by\n\
      the binding. It is also simple, most users will create one and\n\
      set one initial context and never touch it again.\n\
\n\
We elect to use the thread local current context model.\n\
");

static PyObject *
krb_set_current_context(PyObject *self, PyObject *args)
{
    int result;
    PyObject *py_context;

    TraceMethodEnter(self);

    if (!PyArg_ParseTuple(args, "O!:set_current_context",
                          &ContextType, &py_context))
        return NULL;

    if ((result = set_thread_local(CURRENT_CONTEXT_NAME, py_context)) != 0) {
        PyErr_SetString(PyExc_RuntimeError, "cannot set current context as thread local variable");
        return NULL;
    }

    Py_RETURN_NONE;
}

PyDoc_STRVAR(krb_get_current_context_doc,
"get_current_context() -> Context | None\n\
\n\
:parameters:\n\
:returns:\n\
    Current Context object or None if the current context had not been\n\
    set.\n\
\n\
Returns the current Context object or None if the current context had\n\
not been set. See `set_current_context()`.\n\
n\
");

static PyObject *
krb_get_current_context(PyObject *self, PyObject *args)
{
    PyObject *py_context = NULL;

    TraceMethodEnter(self);

    if ((py_context = get_thread_local(CURRENT_CONTEXT_NAME)) == NULL) {
        Py_RETURN_NONE;
    }

    if (!PyContext_Check(py_context)) {
        PyErr_Format(PyExc_RuntimeError, "current context thread local variable must be %s.200s type, not %.200s",
                     Py_TYPE(&ContextType)->tp_name, Py_TYPE(py_context)->tp_name);
        return NULL;
    }

    return py_context;
}

/* ========================================================================== */
static PyMethodDef module_methods[] = {
    {"indented_format",      (PyCFunction)py_indented_format,       METH_VARARGS|METH_KEYWORDS, py_indented_format_doc},
    {"make_line_fmt_tuples", (PyCFunction)py_make_line_fmt_tuples,  METH_VARARGS|METH_KEYWORDS, py_make_line_fmt_tuples_doc},
    {"krb_enctype_name",     (PyCFunction)krb_enctype_name,         METH_VARARGS,               krb_enctype_name_doc},
    {"krb_enctype_from_name",(PyCFunction)krb_enctype_from_name,    METH_VARARGS,               krb_enctype_from_name_doc},
    {"build_principal_name", (PyCFunction)krb_build_principal_name, METH_VARARGS,               krb_build_principal_name_doc},
    {"error_message",        (PyCFunction)krb_error_message,        METH_VARARGS,               krb_error_message_doc},
    {"ticket_flags_str",     (PyCFunction)krb_ticket_flags_str,     METH_VARARGS,               krb_ticket_flags_str_doc},
    {"set_current_context",  (PyCFunction)krb_set_current_context,  METH_VARARGS,               krb_set_current_context_doc},
    {"get_current_context",  (PyCFunction)krb_get_current_context,  METH_NOARGS,                krb_get_current_context_doc},
    {NULL}  /* Sentinel */

};

PyDoc_STRVAR(module_doc,
"This module implements the Kerberos functions\n\
\n\
");

PyMODINIT_FUNC
initkrb(void)
{
    PyObject *m;

    if ((m = Py_InitModule3("krb", module_methods, module_doc)) == NULL) {
        return;
    }

    if ((empty_tuple = PyTuple_New(0)) == NULL) {
        return;
    }
    Py_INCREF(empty_tuple);

    time_module = PyImport_ImportModule("time");

    PyDateTime_IMPORT;

    TYPE_READY(AddressType);
    TYPE_READY(KeyBlockType);
    TYPE_READY(ContextType);
    TYPE_READY(TicketTimesType);
    TYPE_READY(CredentialType);
    TYPE_READY(PrincipalType);
    TYPE_READY(CCacheType);
    TYPE_READY(KeytabEntryType);

    /* exceptions */
    if ((KRB_Exception = PyErr_NewException("krb.KerberosError", PyExc_EnvironmentError, NULL)) == NULL)
        return;
    Py_INCREF(KRB_Exception);
    if (PyModule_AddObject(m, "KerberosError", KRB_Exception) < 0)
        return;

    /* parse_name */
    AddIntConstant(KRB5_PRINCIPAL_PARSE_NO_REALM);
    AddIntConstant(KRB5_PRINCIPAL_PARSE_REQUIRE_REALM);
    AddIntConstant(KRB5_PRINCIPAL_PARSE_ENTERPRISE);

    /* principal name type */
    AddIntConstant(KRB5_NT_UNKNOWN);
    AddIntConstant(KRB5_NT_PRINCIPAL);
    AddIntConstant(KRB5_NT_SRV_INST);
    AddIntConstant(KRB5_NT_SRV_HST);
    AddIntConstant(KRB5_NT_SRV_XHST);
    AddIntConstant(KRB5_NT_UID);
    AddIntConstant(KRB5_NT_X500_PRINCIPAL);
    AddIntConstant(KRB5_NT_SMTP_NAME);
    AddIntConstant(KRB5_NT_ENTERPRISE_PRINCIPAL);
    AddIntConstant(KRB5_NT_WELLKNOWN);
    AddIntConstant(KRB5_NT_MS_PRINCIPAL);
    AddIntConstant(KRB5_NT_MS_PRINCIPAL_AND_ID);
    AddIntConstant(KRB5_NT_ENT_PRINCIPAL_AND_ID);

    /* ticket flags */
    AddIntConstant(TKT_FLG_FORWARDABLE);
    AddIntConstant(TKT_FLG_FORWARDED);
    AddIntConstant(TKT_FLG_PROXIABLE);
    AddIntConstant(TKT_FLG_PROXY);
    AddIntConstant(TKT_FLG_MAY_POSTDATE);
    AddIntConstant(TKT_FLG_POSTDATED);
    AddIntConstant(TKT_FLG_INVALID);
    AddIntConstant(TKT_FLG_RENEWABLE);
    AddIntConstant(TKT_FLG_INITIAL);
    AddIntConstant(TKT_FLG_PRE_AUTH);
    AddIntConstant(TKT_FLG_HW_AUTH);
    AddIntConstant(TKT_FLG_TRANSIT_POLICY_CHECKED);
    AddIntConstant(TKT_FLG_OK_AS_DELEGATE);
    AddIntConstant(TKT_FLG_ENC_PA_REP);
    AddIntConstant(TKT_FLG_ANONYMOUS);

    /* for retrieve_cred */
    AddIntConstant(KRB5_TC_MATCH_TIMES);
    AddIntConstant(KRB5_TC_MATCH_IS_SKEY);
    AddIntConstant(KRB5_TC_MATCH_FLAGS);
    AddIntConstant(KRB5_TC_MATCH_TIMES_EXACT);
    AddIntConstant(KRB5_TC_MATCH_FLAGS_EXACT);
    AddIntConstant(KRB5_TC_MATCH_AUTHDATA);
    AddIntConstant(KRB5_TC_MATCH_SRV_NAMEONLY);
    AddIntConstant(KRB5_TC_MATCH_2ND_TKT);
    AddIntConstant(KRB5_TC_MATCH_KTYPE);
    AddIntConstant(KRB5_TC_SUPPORTED_KTYPES);

    /* for set_flags and other functions */
    AddIntConstant(KRB5_TC_OPENCLOSE);
    AddIntConstant(KRB5_TC_NOTICKET);

    /* errors */
    AddIntConstant(KRB5KDC_ERR_NONE);
    AddIntConstant(KRB5KDC_ERR_NAME_EXP);
    AddIntConstant(KRB5KDC_ERR_SERVICE_EXP);
    AddIntConstant(KRB5KDC_ERR_BAD_PVNO);
    AddIntConstant(KRB5KDC_ERR_C_OLD_MAST_KVNO);
    AddIntConstant(KRB5KDC_ERR_S_OLD_MAST_KVNO);
    AddIntConstant(KRB5KDC_ERR_C_PRINCIPAL_UNKNOWN);
    AddIntConstant(KRB5KDC_ERR_S_PRINCIPAL_UNKNOWN);
    AddIntConstant(KRB5KDC_ERR_PRINCIPAL_NOT_UNIQUE);
    AddIntConstant(KRB5KDC_ERR_NULL_KEY);
    AddIntConstant(KRB5KDC_ERR_CANNOT_POSTDATE);
    AddIntConstant(KRB5KDC_ERR_NEVER_VALID);
    AddIntConstant(KRB5KDC_ERR_POLICY);
    AddIntConstant(KRB5KDC_ERR_BADOPTION);
    AddIntConstant(KRB5KDC_ERR_ETYPE_NOSUPP);
    AddIntConstant(KRB5KDC_ERR_SUMTYPE_NOSUPP);
    AddIntConstant(KRB5KDC_ERR_PADATA_TYPE_NOSUPP);
    AddIntConstant(KRB5KDC_ERR_TRTYPE_NOSUPP);
    AddIntConstant(KRB5KDC_ERR_CLIENT_REVOKED);
    AddIntConstant(KRB5KDC_ERR_SERVICE_REVOKED);
    AddIntConstant(KRB5KDC_ERR_TGT_REVOKED);
    AddIntConstant(KRB5KDC_ERR_CLIENT_NOTYET);
    AddIntConstant(KRB5KDC_ERR_SERVICE_NOTYET);
    AddIntConstant(KRB5KDC_ERR_KEY_EXP);
    AddIntConstant(KRB5KDC_ERR_PREAUTH_FAILED);
    AddIntConstant(KRB5KDC_ERR_PREAUTH_REQUIRED);
    AddIntConstant(KRB5KDC_ERR_SERVER_NOMATCH);
    AddIntConstant(KRB5KDC_ERR_MUST_USE_USER2USER);
    AddIntConstant(KRB5KDC_ERR_PATH_NOT_ACCEPTED);
    AddIntConstant(KRB5KDC_ERR_SVC_UNAVAILABLE);
    AddIntConstant(KRB5KRB_AP_ERR_BAD_INTEGRITY);
    AddIntConstant(KRB5KRB_AP_ERR_TKT_EXPIRED);
    AddIntConstant(KRB5KRB_AP_ERR_TKT_NYV);
    AddIntConstant(KRB5KRB_AP_ERR_REPEAT);
    AddIntConstant(KRB5KRB_AP_ERR_NOT_US);
    AddIntConstant(KRB5KRB_AP_ERR_BADMATCH);
    AddIntConstant(KRB5KRB_AP_ERR_SKEW);
    AddIntConstant(KRB5KRB_AP_ERR_BADADDR);
    AddIntConstant(KRB5KRB_AP_ERR_BADVERSION);
    AddIntConstant(KRB5KRB_AP_ERR_MSG_TYPE);
    AddIntConstant(KRB5KRB_AP_ERR_MODIFIED);
    AddIntConstant(KRB5KRB_AP_ERR_BADORDER);
    AddIntConstant(KRB5KRB_AP_ERR_ILL_CR_TKT);
    AddIntConstant(KRB5KRB_AP_ERR_BADKEYVER);
    AddIntConstant(KRB5KRB_AP_ERR_NOKEY);
    AddIntConstant(KRB5KRB_AP_ERR_MUT_FAIL);
    AddIntConstant(KRB5KRB_AP_ERR_BADDIRECTION);
    AddIntConstant(KRB5KRB_AP_ERR_METHOD);
    AddIntConstant(KRB5KRB_AP_ERR_BADSEQ);
    AddIntConstant(KRB5KRB_AP_ERR_INAPP_CKSUM);
    AddIntConstant(KRB5KRB_AP_PATH_NOT_ACCEPTED);
    AddIntConstant(KRB5KRB_ERR_RESPONSE_TOO_BIG);
    AddIntConstant(KRB5KRB_ERR_GENERIC);
    AddIntConstant(KRB5KRB_ERR_FIELD_TOOLONG);
    AddIntConstant(KRB5KDC_ERR_CLIENT_NOT_TRUSTED);
    AddIntConstant(KRB5KDC_ERR_KDC_NOT_TRUSTED);
    AddIntConstant(KRB5KDC_ERR_INVALID_SIG);
    AddIntConstant(KRB5KDC_ERR_DH_KEY_PARAMETERS_NOT_ACCEPTED);
    AddIntConstant(KRB5KDC_ERR_CERTIFICATE_MISMATCH);
    AddIntConstant(KRB5KRB_AP_ERR_NO_TGT);
    AddIntConstant(KRB5KDC_ERR_WRONG_REALM);
    AddIntConstant(KRB5KRB_AP_ERR_USER_TO_USER_REQUIRED);
    AddIntConstant(KRB5KDC_ERR_CANT_VERIFY_CERTIFICATE);
    AddIntConstant(KRB5KDC_ERR_INVALID_CERTIFICATE);
    AddIntConstant(KRB5KDC_ERR_REVOKED_CERTIFICATE);
    AddIntConstant(KRB5KDC_ERR_REVOCATION_STATUS_UNKNOWN);
    AddIntConstant(KRB5KDC_ERR_REVOCATION_STATUS_UNAVAILABLE);
    AddIntConstant(KRB5KDC_ERR_CLIENT_NAME_MISMATCH);
    AddIntConstant(KRB5KDC_ERR_KDC_NAME_MISMATCH);
    AddIntConstant(KRB5KDC_ERR_INCONSISTENT_KEY_PURPOSE);
    AddIntConstant(KRB5KDC_ERR_DIGEST_IN_CERT_NOT_ACCEPTED);
    AddIntConstant(KRB5KDC_ERR_PA_CHECKSUM_MUST_BE_INCLUDED);
    AddIntConstant(KRB5KDC_ERR_DIGEST_IN_SIGNED_DATA_NOT_ACCEPTED);
    AddIntConstant(KRB5KDC_ERR_PUBLIC_KEY_ENCRYPTION_NOT_SUPPORTED);
    AddIntConstant(KRB5KRB_AP_ERR_IAKERB_KDC_NOT_FOUND);
    AddIntConstant(KRB5KRB_AP_ERR_IAKERB_KDC_NO_RESPONSE);
    AddIntConstant(KRB5KDC_ERR_UNKNOWN_CRITICAL_FAST_OPTION);
    AddIntConstant(KRB5_ERR_RCSID);
    AddIntConstant(KRB5_LIBOS_BADLOCKFLAG);
    AddIntConstant(KRB5_LIBOS_CANTREADPWD);
    AddIntConstant(KRB5_LIBOS_BADPWDMATCH);
    AddIntConstant(KRB5_LIBOS_PWDINTR);
    AddIntConstant(KRB5_PARSE_ILLCHAR);
    AddIntConstant(KRB5_PARSE_MALFORMED);
    AddIntConstant(KRB5_CONFIG_CANTOPEN);
    AddIntConstant(KRB5_CONFIG_BADFORMAT);
    AddIntConstant(KRB5_CONFIG_NOTENUFSPACE);
    AddIntConstant(KRB5_BADMSGTYPE);
    AddIntConstant(KRB5_CC_BADNAME);
    AddIntConstant(KRB5_CC_UNKNOWN_TYPE);
    AddIntConstant(KRB5_CC_NOTFOUND);
    AddIntConstant(KRB5_CC_END);
    AddIntConstant(KRB5_NO_TKT_SUPPLIED);
    AddIntConstant(KRB5KRB_AP_WRONG_PRINC);
    AddIntConstant(KRB5KRB_AP_ERR_TKT_INVALID);
    AddIntConstant(KRB5_PRINC_NOMATCH);
    AddIntConstant(KRB5_KDCREP_MODIFIED);
    AddIntConstant(KRB5_KDCREP_SKEW);
    AddIntConstant(KRB5_IN_TKT_REALM_MISMATCH);
    AddIntConstant(KRB5_PROG_ETYPE_NOSUPP);
    AddIntConstant(KRB5_PROG_KEYTYPE_NOSUPP);
    AddIntConstant(KRB5_WRONG_ETYPE);
    AddIntConstant(KRB5_PROG_SUMTYPE_NOSUPP);
    AddIntConstant(KRB5_REALM_UNKNOWN);
    AddIntConstant(KRB5_SERVICE_UNKNOWN);
    AddIntConstant(KRB5_KDC_UNREACH);
    AddIntConstant(KRB5_NO_LOCALNAME);
    AddIntConstant(KRB5_MUTUAL_FAILED);
    AddIntConstant(KRB5_RC_TYPE_EXISTS);
    AddIntConstant(KRB5_RC_MALLOC);
    AddIntConstant(KRB5_RC_TYPE_NOTFOUND);
    AddIntConstant(KRB5_RC_UNKNOWN);
    AddIntConstant(KRB5_RC_REPLAY);
    AddIntConstant(KRB5_RC_IO);
    AddIntConstant(KRB5_RC_NOIO);
    AddIntConstant(KRB5_RC_PARSE);
    AddIntConstant(KRB5_RC_IO_EOF);
    AddIntConstant(KRB5_RC_IO_MALLOC);
    AddIntConstant(KRB5_RC_IO_PERM);
    AddIntConstant(KRB5_RC_IO_IO);
    AddIntConstant(KRB5_RC_IO_UNKNOWN);
    AddIntConstant(KRB5_RC_IO_SPACE);
    AddIntConstant(KRB5_TRANS_CANTOPEN);
    AddIntConstant(KRB5_TRANS_BADFORMAT);
    AddIntConstant(KRB5_LNAME_CANTOPEN);
    AddIntConstant(KRB5_LNAME_NOTRANS);
    AddIntConstant(KRB5_LNAME_BADFORMAT);
    AddIntConstant(KRB5_CRYPTO_INTERNAL);
    AddIntConstant(KRB5_KT_BADNAME);
    AddIntConstant(KRB5_KT_UNKNOWN_TYPE);
    AddIntConstant(KRB5_KT_NOTFOUND);
    AddIntConstant(KRB5_KT_END);
    AddIntConstant(KRB5_KT_NOWRITE);
    AddIntConstant(KRB5_KT_IOERR);
    AddIntConstant(KRB5_NO_TKT_IN_RLM);
    AddIntConstant(KRB5DES_BAD_KEYPAR);
    AddIntConstant(KRB5DES_WEAK_KEY);
    AddIntConstant(KRB5_BAD_ENCTYPE);
    AddIntConstant(KRB5_BAD_KEYSIZE);
    AddIntConstant(KRB5_BAD_MSIZE);
    AddIntConstant(KRB5_CC_TYPE_EXISTS);
    AddIntConstant(KRB5_KT_TYPE_EXISTS);
    AddIntConstant(KRB5_CC_IO);
    AddIntConstant(KRB5_FCC_PERM);
    AddIntConstant(KRB5_FCC_NOFILE);
    AddIntConstant(KRB5_FCC_INTERNAL);
    AddIntConstant(KRB5_CC_WRITE);
    AddIntConstant(KRB5_CC_NOMEM);
    AddIntConstant(KRB5_CC_FORMAT);
    AddIntConstant(KRB5_CC_NOT_KTYPE);
    AddIntConstant(KRB5_INVALID_FLAGS);
    AddIntConstant(KRB5_NO_2ND_TKT);
    AddIntConstant(KRB5_NOCREDS_SUPPLIED);
    AddIntConstant(KRB5_SENDAUTH_BADAUTHVERS);
    AddIntConstant(KRB5_SENDAUTH_BADAPPLVERS);
    AddIntConstant(KRB5_SENDAUTH_BADRESPONSE);
    AddIntConstant(KRB5_SENDAUTH_REJECTED);
    AddIntConstant(KRB5_PREAUTH_BAD_TYPE);
    AddIntConstant(KRB5_PREAUTH_NO_KEY);
    AddIntConstant(KRB5_PREAUTH_FAILED);
    AddIntConstant(KRB5_RCACHE_BADVNO);
    AddIntConstant(KRB5_CCACHE_BADVNO);
    AddIntConstant(KRB5_KEYTAB_BADVNO);
    AddIntConstant(KRB5_PROG_ATYPE_NOSUPP);
    AddIntConstant(KRB5_RC_REQUIRED);
    AddIntConstant(KRB5_ERR_BAD_HOSTNAME);
    AddIntConstant(KRB5_ERR_HOST_REALM_UNKNOWN);
    AddIntConstant(KRB5_SNAME_UNSUPP_NAMETYPE);
    AddIntConstant(KRB5KRB_AP_ERR_V4_REPLY);
    AddIntConstant(KRB5_REALM_CANT_RESOLVE);
    AddIntConstant(KRB5_TKT_NOT_FORWARDABLE);
    AddIntConstant(KRB5_FWD_BAD_PRINCIPAL);
    AddIntConstant(KRB5_GET_IN_TKT_LOOP);
    AddIntConstant(KRB5_CONFIG_NODEFREALM);
    AddIntConstant(KRB5_SAM_UNSUPPORTED);
    AddIntConstant(KRB5_SAM_INVALID_ETYPE);
    AddIntConstant(KRB5_SAM_NO_CHECKSUM);
    AddIntConstant(KRB5_SAM_BAD_CHECKSUM);
    AddIntConstant(KRB5_KT_NAME_TOOLONG);
    AddIntConstant(KRB5_KT_KVNONOTFOUND);
    AddIntConstant(KRB5_APPL_EXPIRED);
    AddIntConstant(KRB5_LIB_EXPIRED);
    AddIntConstant(KRB5_CHPW_PWDNULL);
    AddIntConstant(KRB5_CHPW_FAIL);
    AddIntConstant(KRB5_KT_FORMAT);
    AddIntConstant(KRB5_NOPERM_ETYPE);
    AddIntConstant(KRB5_CONFIG_ETYPE_NOSUPP);
    AddIntConstant(KRB5_OBSOLETE_FN);
    AddIntConstant(KRB5_EAI_FAIL);
    AddIntConstant(KRB5_EAI_NODATA);
    AddIntConstant(KRB5_EAI_NONAME);
    AddIntConstant(KRB5_EAI_SERVICE);
    AddIntConstant(KRB5_ERR_NUMERIC_REALM);
    AddIntConstant(KRB5_ERR_BAD_S2K_PARAMS);
    AddIntConstant(KRB5_ERR_NO_SERVICE);
    AddIntConstant(KRB5_CC_READONLY);
    AddIntConstant(KRB5_CC_NOSUPP);
    AddIntConstant(KRB5_DELTAT_BADFORMAT);
    AddIntConstant(KRB5_PLUGIN_NO_HANDLE);
    AddIntConstant(KRB5_PLUGIN_OP_NOTSUPP);
    AddIntConstant(KRB5_ERR_INVALID_UTF8);
    AddIntConstant(KRB5_ERR_FAST_REQUIRED);
    AddIntConstant(KRB5_LOCAL_ADDR_REQUIRED);
    AddIntConstant(KRB5_REMOTE_ADDR_REQUIRED);
    AddIntConstant(KRB5_TRACE_NOSUPP);

    /* Address Type */
    AddIntConstant(ADDRTYPE_INET);
    AddIntConstant(ADDRTYPE_CHAOS);
    AddIntConstant(ADDRTYPE_XNS);
    AddIntConstant(ADDRTYPE_ISO);
    AddIntConstant(ADDRTYPE_DDP);
    AddIntConstant(ADDRTYPE_NETBIOS);
    AddIntConstant(ADDRTYPE_INET6);
    AddIntConstant(ADDRTYPE_ADDRPORT);
    AddIntConstant(ADDRTYPE_IPPORT);

    /* Encryption Type */

    if ((krb_enctype_name_to_value = PyDict_New()) == NULL) {
        return;
    }
    if ((krb_enctype_value_to_name = PyDict_New()) == NULL) {
        return;
    }

#define ExportConstant(constant)                      \
if (_AddIntConstantWithLookup(m, #constant, constant, \
    "ENCTYPE_", krb_enctype_name_to_value, krb_enctype_value_to_name) < 0) return;

    ExportConstant(ENCTYPE_NULL);
    ExportConstant(ENCTYPE_DES_CBC_CRC);
    ExportConstant(ENCTYPE_DES_CBC_MD4);
    ExportConstant(ENCTYPE_DES_CBC_MD5);
    ExportConstant(ENCTYPE_DES_CBC_RAW);
    ExportConstant(ENCTYPE_DES3_CBC_SHA);
    ExportConstant(ENCTYPE_DES3_CBC_RAW);
    ExportConstant(ENCTYPE_DES_HMAC_SHA1);
    ExportConstant(ENCTYPE_DSA_SHA1_CMS);
    ExportConstant(ENCTYPE_MD5_RSA_CMS);
    ExportConstant(ENCTYPE_SHA1_RSA_CMS);
    ExportConstant(ENCTYPE_RC2_CBC_ENV);
    ExportConstant(ENCTYPE_RSA_ENV);
    ExportConstant(ENCTYPE_RSA_ES_OAEP_ENV);
    ExportConstant(ENCTYPE_DES3_CBC_ENV);
    ExportConstant(ENCTYPE_DES3_CBC_SHA1);
    ExportConstant(ENCTYPE_AES128_CTS_HMAC_SHA1_96);
    ExportConstant(ENCTYPE_AES256_CTS_HMAC_SHA1_96);
    ExportConstant(ENCTYPE_ARCFOUR_HMAC);
    ExportConstant(ENCTYPE_ARCFOUR_HMAC_EXP);
    ExportConstant(ENCTYPE_UNKNOWN);
}
