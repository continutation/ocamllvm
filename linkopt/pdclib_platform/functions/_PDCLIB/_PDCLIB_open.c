#if 0
/* _PDCLIB_open( const char * const, int )

   This file is part of the Public Domain C Library (PDCLib).
   Permission is granted to use, modify, and / or redistribute at will.
*/

/* This is an example implementation of _PDCLIB_open() fit for use with POSIX
   kernels.
*/

#include <stdio.h>

#include "pdclib/_PDCLIB_glue.h"

#include "sys/types.h"
#include "sys/stat.h"
#include "fcntl.h"
#include "unistd.h"

#include "/usr/include/errno.h"

int _PDCLIB_open( const char * const filename, unsigned int mode )
{
    /* This is an example implementation of _PDCLIB_open() fit for use with
       POSIX kernels.
    */
    int osmode;
    int rc;
    switch ( mode & ( _PDCLIB_FREAD | _PDCLIB_FWRITE | _PDCLIB_FAPPEND | _PDCLIB_FRW ) )
    {
        case _PDCLIB_FREAD: /* "r" */
            osmode = O_RDONLY;
            break;
        case _PDCLIB_FWRITE: /* "w" */
            osmode = O_WRONLY | O_CREAT | O_TRUNC;
            break;
        case _PDCLIB_FAPPEND: /* "a" */
            osmode = O_WRONLY | O_APPEND | O_CREAT;
            break;
        case _PDCLIB_FREAD | _PDCLIB_FRW: /* "r+" */
            osmode = O_RDWR;
            break;
        case _PDCLIB_FWRITE | _PDCLIB_FRW: /* "w+" */
            osmode = O_RDWR | O_CREAT | O_TRUNC;
            break;
        case _PDCLIB_FAPPEND | _PDCLIB_FRW: /* "a+" */
            osmode = O_RDWR | O_APPEND | O_CREAT;
            break;
        default: /* Invalid mode */
            return -1;
    }
    if ( osmode & O_CREAT )
    {
        rc = open( filename, osmode, S_IRUSR | S_IWUSR | S_IRGRP | S_IWGRP | S_IROTH | S_IWOTH );
    }
    else
    {
        rc = open( filename, osmode );
    }
    if ( rc == -1 )
    {
        /* The 1:1 mapping in _PDCLIB_config.h ensures this works. */
        *_PDCLIB_errno_func() = errno;
    }
    return rc;
}
#endif