#include "pdclib/_PDCLIB_glue.h"

extern void _exit( int status ) _PDCLIB_NORETURN;

void _PDCLIB_Exit( int status )
{
    _exit( status );
}
