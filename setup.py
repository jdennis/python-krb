#!/usr/bin/python

import sys
from distutils.core import setup, Extension


#-------------------------------------------------------------------------------
version = "0.12"

#-------------------------------------------------------------------------------

def main(argv):

    long_description='''
    Python binding for Kerberos V5.
    '''

    debug_compile_args = ['-O0', '-g']
    extra_compile_args = []

    for arg in argv:
        if arg in ('-d', '--debug'):
            print "compiling with debug"
            extra_compile_args = debug_compile_args
            argv.remove(arg)

    krb_extension = \
        Extension('krb',
                  sources            = ['src/krb.c'],
                  depends            = ['src/common.h'],
                  libraries          = ['krb5'],
                  extra_compile_args = extra_compile_args,
                  )


    setup(name             = 'python-krb',
          version          = version,
          description      = 'Python binding for Kerberos V5',
          long_description = long_description,
          author           = 'John Dennis',
          author_email     = 'jdennis@redhat.com',
          maintainer       = 'John Dennis',
          maintainer_email = 'jdennis@redhat.com',
          license          = 'LGPLv2+',
          platforms        = 'posix',
          url              = '',
          download_url     = '',
          ext_modules      = [krb_extension,
                             ],
          package_dir      = {'krb':'src'},
          packages         = ['krb'],
    )

    return 0


#-------------------------------------------------------------------------------

if __name__ == "__main__":
    sys.exit(main(sys.argv))
