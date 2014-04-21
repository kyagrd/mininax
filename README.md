mininax
=======

Implementaton of type inference and evaluator for the Nax programing langauge
without certain features including term indices and GADTs.
The features for GADTs include heterogeneous return type indicies
and exsistential type variables in the types for data constructors.
These GADT related featurs are excluded in mininax.


Here is an example miniax code.
```haskell
-- test.miniax
data Unit = Unit ;
data Bool = False | True ;
data Maybe a = Nothing | Just a ;
data Either a b = Left a | Right b ;
data Pair a b = Pair a b ;
data N r = Z | S r ;
data L a r = N | C a r ;
data P r a = PN | PC a (r (Pair a a)) ;
-- Use (Mu <ty>) constructs recursive type (e.g., Mu N)
data MM = MM (Mu N);
-- Use (Mu <ty>) can also construct recursive type constructors
-- that expect indices (e.g., Mu P)
data MMM a = MMM (Mu P a);
id = \x -> x ;
x = id;
z = {True -> True; False -> False};
z2 = {Nothing -> False; Just x -> True};
b = True ;
c = x b;
p = Pair ;
z3 = Pair True False;
zero = In 0 Z ;
succ = \n -> In 0 (S n) ;
-- Use (In 0 <tm>) for regular recursive values without any index
nil = In 0 N ;
cons = \x -> \xs -> In 0 (C x xs) ;
-- Use (In 1 <tm>) for recursive values with one index
pnil = In 1 PN ;
pcons = \x -> \xs -> In 1 (PC x xs) ;
one = succ zero ;
two = succ one ;
three = succ two ;
z5 = cons nil nil ;
z6 = cons True nil ;
z7 = pcons True (pcons (Pair False True) pnil) ;
z8 = pcons one (pcons (Pair two three) pnil) ;
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
               ; S n -> \m -> plus m (mul n m) } ;
factorial = mpr fac cast { Z   -> one
                         ; S n -> mult (succ (cast n)) (fac n)
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

Unit : Unit
True : Bool
False : Bool
Just : a -> Maybe a
Nothing : Maybe a
Right : b -> Either a b
Left : a -> Either a b
Pair : a -> b -> Pair a b
S : r -> N r
Z : N r
C : a -> r -> L a r
N : L a r
PC : a -> r (Pair a a)-> P r a
PN : P r a
MM : Mu N -> MM
MMM : Mu P a -> MMM a
id : a1 -> a1
x : a2 -> a2
z : Bool -> Bool
z2 : Maybe a6 -> Bool
b : Bool
c : Bool
p : a11 -> b10 -> Pair a11 b10
z3 : Pair Bool Bool
zero : Mu N
succ : Mu N -> Mu N
nil : Mu (L a24)
cons : a31 -> Mu (L a31)-> Mu (L a31)
pnil : Mu P a35
pcons : a44 -> Mu P (Pair a44 a44)-> Mu P a44
one : Mu N
two : Mu N
three : Mu N
z5 : Mu (L (Mu (L a53)))
z6 : Mu (L Bool)
z7 : Mu P Bool
z8 : Mu P (Mu N)
flip : (a88 -> a86 -> a90)-> a86 -> a88 -> a90
plus : Mu N -> Mu N -> Mu N
length : Mu (L a118)-> Mu N
psum : Mu P a162 -> (a162 -> Mu N)-> Mu N
mult : Mu N -> Mu N -> Mu N
factorial : Mu N -> Mu N
n4 : Mu N
n5 : Mu N
n6 : Mu N
n7 : Mu N
n8 : (a213 -> Mu N)-> Mu P a213 -> Mu N
n9 : Mu N
n10 : Mu N
n11 : Mu N
n12 : Mu N
n13 : Mu N
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
succ = \ n -> In 0 S n ;
nil = In 0 N ;
cons = \ x -> \ xs -> In 0 C x xs ;
pnil = In 1 PN ;
pcons = \ x -> \ xs -> In 1 PC x xs ;
one = In 0 S (In 0 Z) ;
two = In 0 S (In 0 S (In 0 Z)) ;
three = In 0 S (In 0 S (In 0 S (In 0 Z))) ;
z5 = In 0 C (In 0 N)(In 0 N) ;
z6 = In 0 C True (In 0 N) ;
z7 = In 1 PC True (In 1 PC (Pair False True)(In 1 PN)) ;
z8 = In 1 PC (In 0 S (In 0 Z)) (In 1 PC (Pair (In 0 S (In 0 S (In 0 Z)))(In 0 S (In 0 S (In 0 S (In 0 Z)))))(In 1 PN)) ;
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
  PC x xs -> \ f -> plus (f x)(sum xs {
    Pair a b -> plus (f a)(f b)
  }
  ) 
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
n4 = In 0 S (In 0 S (In 0 S (In 0 S (In 0 Z)))) ;
n5 = In 0 S (In 0 Z) ;
n6 = In 0 S (In 0 Z) ;
n7 = In 0 S (In 0 S (In 0 S (In 0 S (In 0 S (In 0 S (In 0 Z)))))) ;
n8 = \ x -> \ y -> mit sum {{ a . (a -> Mu N)-> Mu N }} {
  PN -> \ f -> zero ;
  PC x xs -> \ f -> plus (f x)(sum xs {
    Pair a b -> plus (f a)(f b)
  }
  ) 
}
y x ;
n9 = In 0 S (In 0 S (In 0 S (In 0 S (In 0 S (In 0 S (In 0 Z)))))) ;
n10 = In 0 S (In 0 Z) ;
n11 = In 0 S (In 0 Z) ;
n12 = In 0 S (In 0 S (In 0 Z)) ;
n13 = In 0 S (In 0 S (In 0 S (In 0 S (In 0 S (In 0 S (In 0 Z)))))) ;
```
