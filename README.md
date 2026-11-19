# Higher-Order Rewriting Toolkit

The higher-order rewriting toolkit (hrstk) is a collection of tools for
higher-order rewrite systems (HRSs) due to Wolfram and
[Nipkow](https://doi.org/10.1016/S0304-3975(97)00143-6),
i.e., higher-order rewriting modulo beta/eta. After preprocessing,
the implementation keeps terms in beta-short eta-long normal form at all times.
The tool largely focuses on a subclass of HRSs called
deterministic higher-order pattern rewrite systems ([DPRSs](https://arxiv.org/abs/2610.38576)).

## Requirements

For some problem, the tools generate SMT constraints which are then
sent to a solver via the awesome [hasmtlib](https://github.com/bruderj15/Hasmtlib).
Via the `-s` command-line argument, you can choose your favorite SMT solver to solve the
constraints computed by the tools. (Currently available: `cvc5`, `z3` and `yices2`,
default: `cvc5`.)

## Installation

With `cabal install` you get the following executables with
symlinks in `~/.cabal/bin/`:

* `hrstk-info`: file info
* `hrstk-term`: termination tool for HRSs
* `hrstk-conf`: confluence tool for DPRSs
* `hrstk-conj`: conjecture joinability for DPRSs
* `hrstk-unif`: unification of [deterministic higher-order patterns](https://doi.org/10.1007/978-3-540-25938-1_12)
* `hrstk-gen`: generation of terms/determinitic higher-order patterns

You can use `[tool] --help` to get more information for each tool.
Use the option `-v` to get verbose output.

## Input format

Supported are the higher-order
[ARI](https://project-coco.uibk.ac.at/ARI/)
format (`-i ari`) as used in [TPDB](https://github.com/TermCOMP/TPDB-ARI)
as well as the proposed HRS format for [ARI-COPS](https://project-coco.uibk.ac.at/ARI/hrs.php).
Furthermore, the tool can read a fragment of
[TPTP THF0](https://tptp.org/UserDocs/TPTPLanguage/TPTPLanguage.shtml) (`-i tptp`)
where axioms / conjectures are of the form `∀...∀ l = r`, free variables
of the equation are locally universally quantified and all terms are in
beta-normal form. 
Type checking/inference is performed automatically after parsing.
Terms are automatically eta-expanded and rules are pulled down to sort.

## hrstk-info

Given the supplied system, the tool

* determines whether it is a PRS, DPRS, EPRS, HRS or HES
* checks whether it is left-linear
* checks whether it is second-order
* indicates when eta-expansion was performed
* indicates when equations were pulled down to sort

## hrstk-term

Termination tool for HRSs. The following methods are implemented:

* the normalized computability path order [NCPO](https://jniederhauser.at/docs/wst2025.pdf) (`-m ncpo`)
* polynomial interpretations with a fixed shape (`-t poly`) for second-order HRSs adapted from this 
  [paper](https://doi.org/10.4230/LIPIcs.RTA.2012.176)

If no concrete method is given, the tool tries NCPO before polynomial interpretations.

## hrstk-conf

Confluence tool for DPRSs.
The following methods are implemented:

* orthogonalityof DPRSs (`-c ortho`)
* [development closedness](https://doi.org/10.1016/S0304-3975(96)00173-9) of PRSs (`-c dc`)
* local confluence by joinability of critical pairs) for DPRSs (`-c lc`)
* Knuth & Bendix' criterion (local confluence + termination) for DPRSs (`-c kb`)

If no concrete method is given, the tool tries orthogonality before development closedness
and Knuth & Bendix' criterion.

## hrstk-conj

The tool reads a file containing a DPRS plus a conjecture (using an extension of the ARI
format with `(conjecture term term)`) and tries to join the conjecture using
the DPRS.

## hrstk-unif

The tool reads an equation of deterministic higher-order patterns and tries
to [unify](https://arxiv.org/abs/2601.14211) them. The eqution will not be pulled
down to sort.

## hrstk-gen

The tool generates a random sequence of terms. Use `-n` to set the number
and `-d` to restrict to deterministic higher-order patterns.

## Testing

Run `cabal test` for unit/property tests.

