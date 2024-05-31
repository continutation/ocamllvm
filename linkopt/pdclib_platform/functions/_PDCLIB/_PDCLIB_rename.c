#if 0
#include "pdclib/_PDCLIB_glue.h"

int _PDCLIB_rename( const char * oldpath, const char * newpath )
{
    /* Note that the behaviour if new file exists is implementation-defined.
       There is nothing wrong with either overwriting it or failing the
       operation, but you might want to document whichever you chose.
       This example fails if new file exists.
    */
    if ( link( oldpath, newpath ) == 0 )
    {
        if ( unlink( oldpath ) )
        {
            /* The 1:1 mapping in _PDCLIB_config.h ensures this works. */
            *_PDCLIB_errno_func() = errno;
            return -1;
        }
        else
        {
            return 0;
        }
    }
    else
    {
        /* The 1:1 mapping in _PDCLIB_config.h ensures this works. */
        *_PDCLIB_errno_func() = errno;
        return EOF;
    }
}
#endif