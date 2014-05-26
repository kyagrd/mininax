mininax
=======

Implementaton of type inference and evaluator for the Nax programing langauge
without certain features including term indices and GADTs.
The features for GADTs include heterogeneous return type indicies
and exsistential type variables in the types for data constructors.
These GADT related featurs are excluded in mininax.


Here is an example miniax code.
```haskell
data Unit = Unit ;
data Bool = False | True ;
data Maybe a = Nothing | Just a ;
data Either a b = Left a | Right b ;
data Pair a b = Pair a b ;
data N r = Z | S r ;
data L a r = N | C a r ;
data P r a = PN | PC a (r (Pair a a)) ;
data MM = MM (Mu N);
data MMM a = MMM (Mu P a);
data T a r {i} = TN | TC a (r { In 0 (S i) });
data V a r : { Mu N } -> * where
  { VN : V a r { In 0 Z }
  ; VC : a -> r { n } -> V a r { In 0 (S n) }
  } ;
data XX a : * where
  { D1 : a -> XX a
  ; D2 : (b -> a) -> b -> XX a
  } ;
data YY : * -> * where
  { DD1 : Mu N -> YY (Mu N)
  ; DD3 : (b -> a) -> b -> YY a
  } ;
id = \x -> x ;
x = id;
z = {True -> True; False -> False};
z2 = {Nothing -> False; Just x -> True};
b = True;
c = x b;
p = Pair ;
z3 = Pair True False;
zero = In 0 Z ;
succ = \n -> In 0 (S n) ;
-- Use (In 0 ...) for regular recursive values without any index
nil = In 0 N ;
cons = \x -> \xs -> In 0 (C x xs) ;
-- Use (In 1 ...) for recursive values with one index
pnil = In 1 PN ;
pcons = \x -> \xs -> In 1 (PC x xs) ;
-- to test (In 1 ...) works for term indices
tnil = In 1 TN ;
tcons = \x -> \xs -> In 1 (TC x xs) ;
vnil = In 1 VN ;
vcons = \x -> \xs -> In 1 (VC x xs) ;
one = succ zero ;
two = succ one ;
three = succ two ;
-- pppp = mit add { S n -> n } ; -- must fail
z5 = cons nil nil ;
z6 = cons True nil ;
z7 = pcons True (pcons (Pair False True) pnil) ;
z8 = pcons one (pcons (Pair two three) pnil) ;
z9 = { D1 n   -> succ n
     ; D2 f x -> f x
     } ;
-- z10 = { D1 n   -> succ n
--       ; D2 f x -> x -- must fail
--       } ;
flip = \f -> \x -> \y -> f y x ;
plus = mit add { Z   -> \m -> m
               ; S n -> \m -> succ (add n m) } ;
length = mit len { N -> zero; C x xs -> succ (len xs) } ;
psum = mit sum {{ a . (a -> Mu N) -> Mu N }}
           { PN      -> \f -> zero
           ; PC x xs -> \f -> plus (f x)
                                   (sum xs {Pair a b -> plus (f a) (f b)} )
           } ;
mult = mit mul { Z   -> \m -> zero
               ; S n -> \m -> plus m (mul n m)
               } ;
factorial = mpr fac cast { Z   -> one
                         ; S n -> mult (succ (cast n)) (fac n)
                         } ;
vlength = mit len {{ {n} . Mu N }} { VN -> zero ; VC x xs -> succ (len xs) } ;
vmap = \f -> mit map {{ {n} . Mu (V b) {n} }}
                 { VN -> vnil
                 ; VC x xs -> vcons (f x) (map xs)
                 } ;
n4 = plus (plus one one) (plus one one) ;
n5 = length z6 ;
n6 = length z5 ;
n7 = psum z8 id ;
n8 = flip psum ;
n9 = mult two three ;
n10 = factorial zero ;
n11 = factorial one ;
n12 = factorial two ;
n13 = factorial three ;
v1 = vcons one vnil ;
v2 = vcons two v1 ;
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
P : (* -> *)-> * -> *
MM : *
MMM : * -> *
T : * -> ({Mu N }-> *)-> {Mu N }-> *
V : * -> ({Mu N }-> *)-> {Mu N }-> *
XX : * -> *
YY : * -> *

Unit : Unit
True : Bool
False : Bool
Just : a -> Maybe a
Nothing : Maybe a
Right : a351 -> Either a a351
Left : a -> Either a a351
Pair : a -> a351 -> Pair a a351
S : r -> N r
Z : N r
C : a -> r -> L a r
N : L a r
PC : a -> r (Pair a a)-> P r a
PN : P r a
MM : Mu N -> MM
MMM : Mu P a -> MMM a
TC : a -> r {In 0 (S i)}-> T a r {i }
TN : T a r {i }
VC : a -> r {n }-> V a r {In 0 (S n)}
VN : V a r {In 0 Z }
D2 : (a351 -> a)-> a351 -> XX a
D1 : a -> XX a
DD3 : (a351 -> a)-> a351 -> YY a
DD1 : Mu N -> YY (Mu N)
id : _50 -> _50
x : _51 -> _51
z : Bool -> Bool
z2 : Maybe a56 -> Bool
b : Bool
c : Bool
p : a61 -> b60 -> Pair a61 b60
z3 : Pair Bool Bool
zero : Mu N
succ : Mu N -> Mu N
nil : Mu (L a74)
cons : a81 -> Mu (L a81)-> Mu (L a81)
pnil : Mu P a85
pcons : a94 -> Mu P (Pair a94 a94)-> Mu P a94
tnil : Mu (T a101){i99 }
tcons : a110 -> Mu (T a110){In 0 (S i108)}-> Mu (T a110){i108 }
vnil : Mu (V a116){In 0 Z }
vcons : a125 -> Mu (V a125){n123 }-> Mu (V a125){In 0 (S n123)}
one : Mu N
two : Mu N
three : Mu N
z5 : Mu (L (Mu (L a134)))
z6 : Mu (L Bool)
z7 : Mu P Bool
z8 : Mu P (Mu N)
z9 : XX (Mu N)-> Mu N
flip : (_183 -> _181 -> a185)-> _181 -> _183 -> a185
plus : Mu N -> Mu N -> Mu N
length : Mu (L a218)-> Mu N
psum : Mu P a265 -> (a265 -> Mu N)-> Mu N
mult : Mu N -> Mu N -> Mu N
factorial : Mu N -> Mu N
vlength : Mu (V a318){n327 }-> Mu N
vmap : (a347 -> a351)-> Mu (V a347){n360 }-> Mu (V a351){n360 }
n4 : Mu N
n5 : Mu N
n6 : Mu N
n7 : Mu N
n8 : (a379 -> Mu N)-> Mu P a379 -> Mu N
n9 : Mu N
n10 : Mu N
n11 : Mu N
n12 : Mu N
n13 : Mu N
v1 : Mu (V (Mu N)) {In 0 (S (In 0 Z)) }
v2 : Mu (V (Mu N)) {In 0 (S (In 0 (S (In 0 Z)))) }
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

Using either `-e` option or `-a` optoin,
you can examine values of top level definitions.

```
shell-prmompt> mininax -e test.mininax
id = \ x -> x ;
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
nil = In 0 N ;
cons = \ x -> \ xs -> In 0 (C x xs) ;
pnil = In 1 PN ;
pcons = \ x -> \ xs -> In 1 (PC x xs) ;
tnil = In 1 TN ;
tcons = \ x -> \ xs -> In 1 (TC x xs) ;
vnil = In 1 VN ;
vcons = \ x -> \ xs -> In 1 (VC x xs) ;
one = In 0 (S (In 0 Z)) ;
two = In 0 (S (In 0 (S (In 0 Z)))) ;
three = In 0 (S (In 0 (S (In 0 (S (In 0 Z)))))) ;
z5 = In 0 (C (In 0 N)(In 0 N)) ;
z6 = In 0 (C True (In 0 N)) ;
z7 = In 1 (PC True (In 1 (PC (Pair False True)(In 1 PN)))) ;
z8 = In 1 (PC (In 0 (S (In 0 Z)))(In 1 (PC (Pair (In 0 (S (In 0 (S (In 0 Z)))))(In 0 (S (In 0 (S (In 0 (S (In 0 Z)))))))) (In 1 PN)))) ;
z9 = {
  D1 n -> succ n ;
  D2 f x -> f x 
}
 ;
flip = \ f -> \ x -> \ y -> f y x ;
plus = mit add {
  Z -> \ m -> m ;
  S n -> \ m -> succ (add n m)
}
 ;
length = mit len {
  N -> zero ;
  C x xs -> succ (len xs)
}
 ;
psum = mit sum {{ a . (a -> Mu N)-> Mu N }} {
  PN -> \ f -> zero ;
  PC x xs -> \ f -> plus (f x)(sum xs {Pair a b -> plus (f a)(f b)}) 
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
vlength = mit len {{ {n }. Mu N }} {
  VN -> zero ;
  VC x xs -> succ (len xs)
}
 ;
vmap = \ f -> mit map {{ {n }. Mu (V b){n }}} {
  VN -> vnil ;
  VC x xs -> vcons (f x)(map xs)
}
 ;
n4 = In 0 (S (In 0 (S (In 0 (S (In 0 (S (In 0 Z)))))))) ;
n5 = In 0 (S (In 0 Z)) ;
n6 = In 0 (S (In 0 Z)) ;
n7 = In 0 (S (In 0 (S (In 0 (S (In 0 (S (In 0 (S (In 0 (S (In 0 Z)))))))))))) ;
n8 = \ x -> \ y -> mit sum {{ a . (a -> Mu N)-> Mu N }} {
  PN -> \ f -> zero ;
  PC x xs -> \ f -> plus (f x)(sum xs {Pair a b -> plus (f a)(f b)}) 
}
y x ;
n9 = In 0 (S (In 0 (S (In 0 (S (In 0 (S (In 0 (S (In 0 (S (In 0 Z)))))))))))) ;
n10 = In 0 (S (In 0 Z)) ;
n11 = In 0 (S (In 0 Z)) ;
n12 = In 0 (S (In 0 (S (In 0 Z)))) ;
n13 = In 0 (S (In 0 (S (In 0 (S (In 0 (S (In 0 (S (In 0 (S (In 0 Z)))))))))))) ;
v1 = In 1 (VC (In 0 (S (In 0 Z)))(In 1 VN)) ;
v2 = In 1 (VC (In 0 (S (In 0 (S (In 0 Z)))))(In 1 (VC (In 0 (S (In 0 Z)))(In 1 VN)))) ;
```
