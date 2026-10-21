## What changed

Filled `AlgebraicGeometry.ProEtale.VaryingRing.moduleEvalG_unique` in
`Sheaf.AlgebraicGeometry.VaryingRingOperations`. For each system, postcompose
both unit equations with the direct image of the inverse comparison. The two
inverse components then have the same image under the level adjunction's
Hom equivalence. Injectivity, natural transformation extensionality and
isomorphism extensionality prove equality.

The declaration signature, definitions, attributes and imports are unchanged.
Updated the existing uniqueness node's proof and proof dependencies to match
this shorter argument. No new declaration or module is introduced.

Validation: the full item module compiled on the project server with
`lcompile.py`, without warnings (24.4 seconds). Searches through `msearch.py`
used Loogle (`"mateEquiv", "unit"`), Lean Finder (uniqueness from unit
compositions), and grep (`unit_mateEquiv|mateEquiv_unit`). The existing
adjunction Hom-equivalence API gives a shorter proof than expanding mates.

## Proved and sorry left

Closed 1 of the original 5 holes:

- `AlgebraicGeometry.ProEtale.VaryingRing.moduleEvalG_unique`
  (`lem-sp-varying-ring-module-eval-g-uniqueness`).

Added 0 holes and split off 0 statements. The following 4 original holes
remain unchanged:

- `AlgebraicGeometry.ProEtale.VaryingRing.moduleEvalG_exists`
  (`lem-sp-varying-ring-module-eval-g-existence`).
- `AlgebraicGeometry.ProEtale.VaryingRing.extension_exact`
  (`def-sp-varying-ring-operations`).
- `AlgebraicGeometry.ProEtale.VaryingRing.evalPMate_isIso`
  (`def-sp-varying-ring-operations`).
- `AlgebraicGeometry.ProEtale.VaryingRing.evalJInv_isIso`
  (`def-sp-varying-ring-operations`).

This is a partial proof delivery, with one hole proved and no decomposition.

## No longer needed

No imports or modules are removed. For the uniqueness argument alone,
`lem-coef-semilinear-derived-sections` and
`def-cbc-strict-constant-tower-operations` are removed from the uniqueness
node's `proof_deps`: the proof uses the specified level adjunction and unit
equations, without constructing any geometric operations. Both remain
statement dependencies, and their modules remain needed elsewhere in the item.
No claim is made that either module leaves the targets' closure.

## Where the brief, the DAG or earlier work was wrong

The uniqueness node's planned naturality and triangle-identity calculations
are unnecessary. Its hypotheses already imply equality of the two inverse
components under the level Hom equivalence. No mathematical statement was
changed or disputed. The other four holes require geometric construction or
derived comparison arguments; this delivery does not replace or split them.

## Second reading by D9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
