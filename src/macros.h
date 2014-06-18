#ifndef __MACROS_H
#define __MACROS_H

#define uapply (foldl' (flip (.)) id . map (uncurry subst))

#endif
