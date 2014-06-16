mininax
=======

Mininax is a prototype reference implementaton of the Nax programing langauge,
which is described in [my Ph.D. dissertation draft](https://dl.dropboxusercontent.com/u/2589099/thesis/Nax_KiYungAhn_thesis_draft.pdf),
but only implements the core part of the language without syntactic suguars
(e.g., type synonyms, fixpoint derivation). There are few other differences
in the syntax compared to the version of the langauge in my dissertation.
Mininax supports case function syntax rather than case expression syntax.
A case function is a list of case alternatives that awaits an argument
to scrutinize. For example, `{ False -> e1; True -> e2 }` is a case function,
which means `\ x -> case x of { False -> e1; True -> e2 }` if you had case expressions. 
In addition, mininax has better GADT delcleration syntax than the language syntax
described in my Ph.D. dissertation.

Here is an example miniax code.
```haskell
TODO
```

Runining `mininax test.mininax` will give results of
kind inference and type inference.
```
shell-prmompt> mininax test.mininax
TODO
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
TODO
```
