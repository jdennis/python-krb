//#define DEBUG

// Gettext
#ifndef _
#define _(s) s
#endif

#define PyNone_Check(x) ((x) == Py_None)

#define TYPE_READY(type)                                                \
{                                                                       \
    if (PyType_Ready(&type) < 0)                                        \
        return;                                                         \
    Py_INCREF(&type);                                                   \
    PyModule_AddObject(m, rindex(type.tp_name, '.')+1, (PyObject *)&type); \
}

#define AddIntConstant(c) if (PyModule_AddIntConstant(m, #c, c) < 0) return;

#ifdef DEBUG

#define DumpRefCount(x)                                                 \
{                                                                       \
    PyObject *_obj = (PyObject *) (x);                                  \
    printf("<%s object at %p refcnt=%d>\n", Py_TYPE(_obj)->tp_name, _obj, _obj->ob_refcnt); \
}


#define TraceMessage(_msg)                      \
{                                               \
    printf("%s\n", _msg);                       \
}

#define TraceMethodEnter(x)                                             \
{                                                                       \
    PyObject *_obj = (PyObject *) (x);                                  \
    const char *name = NULL;                                            \
                                                                        \
    if (_obj) {                                                         \
        name = Py_TYPE(_obj)->tp_name;                                  \
    }                                                                   \
    printf("%s (Enter): <%s object at %p refcnt=%d>\n",                 \
           __FUNCTION__, name, _obj, _obj ? _obj->ob_refcnt : -9999);   \
}

#define TraceMethodLeave(x)                                             \
{                                                                       \
    PyObject *_obj = (PyObject *) (x);                                  \
    const char *name = NULL;                                            \
                                                                        \
    if (_obj) {                                                         \
        name = Py_TYPE(_obj)->tp_name;                                  \
    }                                                                   \
    printf("%s (Leave): <%s object at %p refcnt=%d>\n",                 \
           __FUNCTION__, name, _obj, _obj ? _obj->ob_refcnt : -9999);   \
}

#define TraceObjNewEnter(_tp)                                   \
{                                                               \
    PyTypeObject *tp = _tp;                                     \
    if (tp != NULL)                                             \
        printf("%s (Enter) %s\n", __FUNCTION__, tp->tp_name);   \
    else                                                        \
        printf("%s (Enter)\n", __FUNCTION__);                   \
}


#define TraceObjNewLeave(x)                                             \
{                                                                       \
    PyObject *_obj = (PyObject *) (x);                                  \
    const char *name = NULL;                                            \
                                                                        \
    if (_obj) {                                                         \
        name = Py_TYPE(_obj)->tp_name;                                  \
    }                                                                   \
    printf("%s: returns <%s object at %p refcnt=%d>\n",                 \
           __FUNCTION__, name, _obj, _obj ? _obj->ob_refcnt : -9999);   \
}

#else
#define DumpRefCount(_obj)
#define TraceMessage(_msg)
#define TraceMethodEnter(_obj)
#define TraceMethodLeave(_obj)
#define TraceObjNewEnter(_tp)
#define TraceObjNewLeave(_obj)
#endif

