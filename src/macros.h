#ifndef __MACROS_H
#define __MACROS_H

#define uapply (foldr (.) id . map (uncurry subst) . reverse)

#endif
