#ifndef __MACROS_H
#define __MACROS_H

#define uapply (foldl' (.) id . map (uncurry subst))

#endif
