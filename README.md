# Higher-Order Rewriting Toolkit

The tool `hrstk` is a tool for higher-order equational systems (HES) / higher-order
rewrite systems (HRSs)  a la [Nipkow](https://doi.org/10.1016/S0304-3975(97)00143-6), i.e., higher-order 
rewriting modulo beta/eta. The implementation keeps terms in beta-short eta-long normal form
at all times.

The tool functioning modes for unification of deterministic higher-order patterns (DHPs)
(`-m unif`), computing and checking naive joinability of 
critical pairs (`-m cps`) of deterministic higher-order patttern rewrite systems (DPRSs),
checking whether a conjectured equation is joinable by a given DPRS (`-m conj`)
as well as various termination methods for HRSs (`-m term`):

* the normalized computability path order [NCPO](https://jniederhauser.at/docs/wst2025.pdf) (`-t ncpo`)
* polynomial interpretations with a fixed shape (`-t poly`) adapted from this 
  [paper](https://doi.org/10.4230/LIPIcs.RTA.2012.176)

The tool outputs `YES` if the problem of the respective mode could be solved.
otherwise `MAYBE` is reported. For a human-checkable output, use the flag `-v`.

Supported formats are the fragment of 
[TPTP THF0](https://tptp.org/UserDocs/TPTPLanguage/TPTPLanguage.shtml) (`-i tptp`)
where axioms / conjectures are of the form `∀...∀ l = r`, free variables
of the equation are locally universally quantified and all terms are in
beta-normal form. Furthermore, the tool can read the higher-order
[ARI](https://project-coco.uibk.ac.at/ARI/)
format (`-i ari`) as used in [TPDB](https://github.com/TermCOMP/TPDB-ARI). 
Type checking/inference is performed automatically after parsing.

The tool makes heavy use of SMT solvers using the awesome new library 
[hasmtlib](https://github.com/bruderj15/Hasmtlib). 
Via the `-s` command-line argument, you can choose your favorite SMT solver to solve the
constraints computed by `hrstk`. (Currently available: `cvc5`, `z3` and `yices2`.)

## Installation / Run

Use `cabal run hrstk -- <ARGS>` or install it via `cabal build` or `cabal install`.

## Testing

Run `cabal run hrstk-test` for unit/property tests.

## Input Requirements

The input must be in beta-normal form. Equations are eta-expanded and pulled down to their return sort
automatically after parsing and type checking/inference. Moreover, the following conditions are automatically
checked after reading the input file:

### Unification

An equation of DHPs which will not be pulled down to its return sort. Additional equations are ignored.

### Critical Pairs

The input should be a DPRS.

### Conjecture Joinability

The input should be a HRS. Queries can be done by including conjectures in both
ARI and TPTP.

### Termination

The input system should be an HRS. Furthermore, the interpretation 
shape for polynomial interpretations only supports essentially second-order systems, i.e.,
all constants have types of order at most two, free variables have types of order at most one and 
bound variables have base types. All these conditions are checked automatically after reading the
input file.


