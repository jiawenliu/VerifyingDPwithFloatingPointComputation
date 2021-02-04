# Coq Formalization of Differential Privacy in Floating Point COmputation

## Dependencies

- Coq (This has been tested with 8.11 and 8.12)

- The following OPAM packages:
  
  + `coq-flocq` (tested with 3.3.1)
  + `coq-mathcomp-ssreflect` (tested with 1.11)
  + `coq-mathcomp-fingroup` (tested with 1.11)
  + `coq-mathcomp-algebra` (tested with 1.11)
  + `gappa` (tested with 1.3.5)
  + `gappalib-coq` (tested with 1.4.4)
  
- Deriving (https://github.com/arthuraa/deriving, tested with revision 8d7cd4d)

- Extensional Structures (https://github.com/arthuraa/extructures, tested with
  revision d5dafd2)

- Gappa (http://gappa.gforge.inria.fr, tested with Gappa 1.3.5)
  
## Compiling

cd src/ and hit `make`

## Contents

- src/:

  * `Expressions.v`: arithmetic expressions

  * `ExpressionTransition.v`: The operational semantics for expressions, in terms of fixed floating point computation and error approximation.

  * `Command.v`: the grammar of the language

  * `CommandSemantics.v`: The operational semantics of the commands

  * `apRHL+.v`: The extended approximate probbailistic relational hoare logic

  * lib/:  The main definitions are:
     
    + `MachineType.v`: The fixed flaoting point type of 64 bits.

  * distr/:  The main definitions are:
    
    + `Extra.v`: addenda to mathcomp and extructures

    + `Prob.v`: theory of finite probability distributions

    + `Unif.v` : the unif distirbution defined over fixed floating point number ranging from 0 to 1,  (0, 1].

- example/:

  * snap/: the bulk of the development.  This files defines the syntax of Imp
    commands, their semantics, and the inlining and dead-store elimination
    passes.  The main definitions are:
     
    + `snapMech.v`: The example of Snapping mechanism implementation

    + `snapMechValiditor.v`: The formal verification of Snapping mechanism.
  