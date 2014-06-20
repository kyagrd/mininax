mininax
=======

* WARNING: type checking test/path.mininax will up most of your 4GB memory

Mininax is a prototype reference implementation of the Nax programming language,
which is described in [my Ph.D. dissertation draft](https://dl.dropboxusercontent.com/u/2589099/thesis/Nax_KiYungAhn_thesis_draft.pdf),
but only implements the core part of the language without syntactic sugars
(e.g., type synonyms, fixpoint derivation). There are few other differences
in the syntax compared to the version of the language in my dissertation.
Mininax supports case function syntax rather than case expression syntax.
A case function is a list of case alternatives that awaits an argument
to scrutinize. For example, `{ False -> e1; True -> e2 }` is a case function,
which means `\ x -> case x of { False -> e1; True -> e2 }` if you had case expressions. 
In addition, mininax has better GADT declaration syntax than the language syntax
described in my Ph.D. dissertation.

Here is an example mininax code.
```haskell
data Unit = Unit ;                                                              
data Bool = False | True ;                                                      
data Maybe a = Nothing | Just a ;                                               
data Either a b = Left a | Right b ;                                            
data Pair a b = Pair a b ;                                                      
                                                                                
id = \x -> x ;                                                                  
flip = \f -> \x -> \y -> f y x ;                                                
x = id;                                                                         
z = {True -> True; False -> False};                                             
z2 = {Nothing -> False; Just x -> True};                                        
b = True;                                                                       
c = x b;                                                                        
p = Pair ;                                                                      
z3 = Pair True False;                                                           
                                                                                
data N r = Z | S r ;                                                            
-- Use (In 0 ...) for regular recursive values without any index                
zero = In 0 Z ;                                                                 
succ = \n -> In 0 (S n) ;                                                       
                                                                                
one = succ zero ;                                                               
two = succ one ;                                                                
three = succ two ;                                                              
                                                                                
plus = mit add { Z   -> \m -> m                                                 
               ; S n -> \m -> succ (add n m) } ;                                
mult = mit mul { Z   -> \m -> zero                                              
               ; S n -> \m -> plus m (mul n m)                                  
               } ;
factorial = mpr fac cast { Z   -> one
                         ; S n -> mult (succ (cast n)) (fac n)
                         } ;

n4 = plus (plus one one) (plus one one) ;
n9 = mult two three ;
n10 = factorial zero ;
n11 = factorial one ;
n12 = factorial two ;
n13 = factorial three ;

data L a r = N | C a r ;
nil = In 0 N ;
cons = \x -> \xs -> In 0 (C x xs) ;

z5 = cons nil nil ;
z6 = cons True nil ;

length = mit len { N -> zero; C x xs -> succ (len xs) } ;

n5 = length z6 ;
n6 = length z5 ;

-- term indices in ADT declaration
data T a r {i} = TN | TC a (r { `succ i });
-- to test (In 1 ...) works for term indices
tnil = In 1 TN ;
tcons = \x -> \xs -> In 1 (TC x xs) ;

data P r a = PN | PC a (r (Pair a a)) ;
-- Use (In 1 ...) for recursive values with one index
pnil = In 1 PN ;
pcons = \x -> \xs -> In 1 (PC x xs) ;

z7 = pcons True (pcons (Pair False True) pnil) ;
z8 = pcons one (pcons (Pair two three) pnil) ;
kkk = \x -> \y -> x ;
psum = mit sum {{ a . (a -> Mu N) -> Mu N }}
           { PN      -> \f -> zero
           ; PC x xs -> \f -> plus (f x) 
                                   (sum xs {Pair a b -> plus (f a) (f b)})
           } ;

n7 = psum z8 id ;
n8 = flip psum ;
n14 = flip psum id z8 ;

data V a r : { Mu N } -> * where
  { VN : V a r { `zero }
  ; VC : a -> r { n } -> V a r { `succ n }
  } ;

vnil = In 1 VN ;
vcons = \x -> \xs -> In 1 (VC x xs) ;

v1 = vcons one vnil ;
v2 = vcons two v1 ;

vlength = mit len {{ {n} . Mu N }}
              { VN -> zero
              ; VC x xs -> succ (len xs)
              } ;

vmap = \f -> mit map {{ {n} . Mu (V b) {n} }}
                 { VN      -> vnil
                 ; VC x xs -> vcons (f x) (map xs)
                 } ;

vapp = mit app {{ {n} . Mu (V b) {m} -> Mu (V b) {`plus n m} }}
            { VN      -> \ys -> ys
            ; VC x xs -> \ys -> vcons x (app xs ys)
            } ;

n15 = vlength v2 ;
v3 = vapp v2 v1 ;
v4 = vmap succ v3 ;
```

Runining `mininax test.mininax` will give results of
kind inference and type inference.
```
shell-prmompt> mininax test.mininax
Unit : *
Bool : *
Maybe : * -> *
Either : * -> * -> *
Pair : * -> * -> *
N : * -> *
L : * -> * -> *
T : * -> ({Mu N} -> *) -> {Mu N} -> *
P : (* -> *) -> * -> *
V : * -> ({Mu N} -> *) -> {Mu N} -> *

Unit : Unit
True : Bool
False : Bool
Just : a -> Maybe a
Nothing : Maybe a
Right : b -> Either a b
Left : a -> Either a b
Pair : a -> b -> Pair a b
id : _6 -> _6
flip : (_12 -> _10 -> a14) -> _10 -> _12 -> a14
x : _15 -> _15
z : Bool -> Bool
z2 : Maybe a16 -> Bool
b : Bool
c : Bool
p : a25 -> b24 -> Pair a25 b24
z3 : Pair Bool Bool
S : r -> N r
Z : N r
zero : Mu N
succ : Mu N -> Mu N
one : Mu N
two : Mu N
three : Mu N
plus : Mu N -> Mu N -> Mu N
mult : Mu N -> Mu N -> Mu N
factorial : Mu N -> Mu N
n4 : Mu N
n9 : Mu N
n10 : Mu N
n11 : Mu N
n12 : Mu N
n13 : Mu N
C : a -> r -> L a r
N : L a r
nil : Mu (L a110)
cons : _113 -> Mu (L _113) -> Mu (L _113)
z5 : Mu (L (Mu (L a122)))
z6 : Mu (L Bool)
length : Mu (L a136) -> Mu N
n5 : Mu N
n6 : Mu N
TC : a -> r {In 0 (S i)} -> T a r {i}
TN : T a r {i}
tnil : Mu (T a168) {i166}
tcons : _172 -> Mu (T _172) {In 0 (S i175)} -> Mu (T _172) {i175}
PC : a -> r (Pair a a) -> P r a
PN : P r a
pnil : Mu P a187
pcons : _192 -> Mu P (Pair _192 _192) -> Mu P _192
z7 : Mu P Bool
z8 : Mu P (Mu N)
kkk : _224 -> _226 -> _224
psum : Mu P a230 -> (a230 -> Mu N) -> Mu N
n7 : Mu N
n8 : (a283 -> Mu N) -> Mu P a283 -> Mu N
n14 : Mu N
VC : a301 -> r300 {n302} -> V a301 r300 {In 0 (S n302)}
VN : V a r {In 0 Z}
vnil : Mu (V a319) {In 0 Z}
vcons : _323 -> Mu (V _323) {n326} -> Mu (V _323) {In 0 (S n326)}
v1 : Mu (V (Mu N)) {In 0 (S (In 0 Z))}
v2 : Mu (V (Mu N)) {In 0 (S (In 0 (S (In 0 Z))))}
vlength : Mu (V a348) {n345} -> Mu N
vmap : (a383 -> _403) -> Mu (V a383) {n380} -> Mu (V _403) {n380}
vapp : Mu (V _448) {n422} -> Mu (V _448) {m420} -> Mu (V _448) {
    mit add461 {
      Z -> \ m462 -> m462 ;
      S n463 -> \ m464 -> In 0 (S (add461 n463 m464)) 
    }
    n422 m420 
  }
  
n15 : Mu N
v3 : Mu (V (Mu N)) {In 0 (S (In 0 (S (In 0 (S (In 0 Z))))))}
v4 : Mu (V (Mu N)) {In 0 (S (In 0 (S (In 0 (S (In 0 Z))))))}
```

You can try `-h` or `--help` option for more information.
```
shell-prmompt> mininax -h
miniax - command line program for the mininax langauge

Usage: mininax [-k|--kind] [-t|--type] [-e|--eval] [-a|--all] [FILE]
  mininax command line program

Available options:
  -h,--help                Show this help text
  -k,--kind                Kind Inference for type constructors
  -t,--type                Type Inference for data constructors and definitions
  -e,--eval                Evaluate definitions
  -a,--all                 Kind Infer, Type Infer, and Evaluate the program
  FILE                     File path argument
```

Using either `-e` option or `-a` option,
you can examine values of top level definitions.

```
shell-prmompt> mininax -e test.mininax
id = \ x -> x ;
flip = \ f -> \ x -> \ y -> f y x ;
x = \ x -> x ;
z = {
  True -> True ;
  False -> False 
}
 ;
z2 = {
  Nothing -> False ;
  Just x -> True 
}
 ;
b = True ;
c = True ;
p = Pair ;
z3 = Pair True False ;
zero = In 0 Z ;
succ = \ n -> In 0 (S n) ;
one = In 0 (S (In 0 Z)) ;
two = In 0 (S (In 0 (S (In 0 Z)))) ;
three = In 0 (S (In 0 (S (In 0 (S (In 0 Z)))))) ;
plus = mit add {
  Z -> \ m -> m ;
  S n -> \ m -> succ (add n m)
}
 ;
mult = mit mul {
  Z -> \ m -> zero ;
  S n -> \ m -> plus m (mul n m)
}
 ;
factorial = mpr fac cast {
  Z -> one ;
  S n -> mult (succ (cast n)) (fac n)
}
 ;
n4 = In 0 (S (In 0 (S (In 0 (S (In 0 (S (In 0 Z)))))))) ;
n9 = In 0 (S (In 0 (S (In 0 (S (In 0 (S (In 0 (S (In 0 (S (In 0 Z)))))))))))) ;
n10 = In 0 (S (In 0 Z)) ;
n11 = In 0 (S (In 0 Z)) ;
n12 = In 0 (S (In 0 (S (In 0 Z)))) ;
n13 = In 0 (S (In 0 (S (In 0 (S (In 0 (S (In 0 (S (In 0 (S (In 0 Z)))))))))))) ;
nil = In 0 N ;
cons = \ x -> \ xs -> In 0 (C x xs) ;
z5 = In 0 (C (In 0 N) (In 0 N)) ;
z6 = In 0 (C True (In 0 N)) ;
length = mit len {
  N -> zero ;
  C x xs -> succ (len xs)
}
 ;
n5 = In 0 (S (In 0 Z)) ;
n6 = In 0 (S (In 0 Z)) ;
tnil = In 1 TN ;
tcons = \ x -> \ xs -> In 1 (TC x xs) ;
pnil = In 1 PN ;
pcons = \ x -> \ xs -> In 1 (PC x xs) ;
z7 = In 1 (PC True (In 1 (PC (Pair False True) (In 1 PN)))) ;
z8 = In 1 (PC (In 0 (S (In 0 Z))) (In 1 (PC (Pair (In 0 (S (In 0 (S (In 0 Z))))) (In 0 (S (In 0 (S (In 0 (S (In 0 Z)))))))) (In 1 PN)))) ;
kkk = \ x -> \ y -> x ;
psum = mit sum {{ a . (a -> Mu N) -> Mu N }} {
  PN -> \ f -> zero ;
  PC x xs -> \ f -> plus (f x) (sum xs {Pair a b -> plus (f a) (f b)} ) 
}
 ;
n7 = In 0 (S (In 0 (S (In 0 (S (In 0 (S (In 0 (S (In 0 (S (In 0 Z)))))))))))) ;
n8 = \ x -> \ y -> mit sum {{ a . (a -> Mu N) -> Mu N }} {
  PN -> \ f -> zero ;
  PC x xs -> \ f -> plus (f x) (sum xs {Pair a b -> plus (f a) (f b)} ) 
}
y x ;
n14 = In 0 (S (In 0 (S (In 0 (S (In 0 (S (In 0 (S (In 0 (S (In 0 Z)))))))))))) ;
vnil = In 1 VN ;
vcons = \ x -> \ xs -> In 1 (VC x xs) ;
v1 = In 1 (VC (In 0 (S (In 0 Z))) (In 1 VN)) ;
v2 = In 1 (VC (In 0 (S (In 0 (S (In 0 Z))))) (In 1 (VC (In 0 (S (In 0 Z))) (In 1 VN)))) ;
vlength = mit len {{ {n} . Mu N }} {
  VN -> zero ;
  VC x xs -> succ (len xs)
}
 ;
vmap = \ f -> mit map {{ {n} . Mu (V b) {n} }} {
  VN -> vnil ;
  VC x xs -> vcons (f x) (map xs)
}
 ;
vapp = mit app {{ {n} . Mu (V b) {m} -> Mu (V b) {`plus n m} }} {
  VN -> \ ys -> ys ;
  VC x xs -> \ ys -> vcons x (app xs ys)
}
 ;
n15 = In 0 (S (In 0 (S (In 0 Z)))) ;
v3 = In 1 (VC (In 0 (S (In 0 (S (In 0 Z))))) (In 1 (VC (In 0 (S (In 0 Z))) (In 1 (VC (In 0 (S (In 0 Z))) (In 1 VN)))))) ;
v4 = In 1 (VC (In 0 (S (In 0 (S (In 0 (S (In 0 Z))))))) (In 1 (VC (In 0 (S (In 0 (S (In 0 Z))))) (In 1 (VC (In 0 (S (In 0 (S (In 0 Z))))) (In 1 VN)))))) ;
```
