#include "pdclib/_PDCLIB_glue.h"

extern int errno;
extern int close( int fd );

int _PDCLIB_close( int fd )
{
    int rc = close( fd );
    if ( rc )
    {
      *_PDCLIB_errno_func() = errno;
    }
    return rc;
}
