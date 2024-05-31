#include <stdio.h>
#include <string.h>

extern struct _PDCLIB_file_t * _PDCLIB_filelist;

int remove( const char * pathname )
{
    int rc;
    struct _PDCLIB_file_t * current = _PDCLIB_filelist;
    while ( current != NULL )
    {
        if ( ( current->filename != NULL ) && ( strcmp( current->filename, pathname ) == 0 ) )
        {
            return EOF;
        }
        current = current->next;
    }
    rc = 0; //unlink( pathname );
    if ( rc )
    {
        /* The 1:1 mapping in _PDCLIB_config.h ensures this works. */
        *_PDCLIB_errno_func() = 0; //errno;
    }
    return rc;
}
