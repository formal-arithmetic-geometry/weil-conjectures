## What changed

Proved `AlgebraicGeometry.ProEtale.SpTowerClasses.powerSystem_ordinary_cokernel`
in `Sheaf.Paper.PowerSystemOrdinaryCokernel` without changing its statement.
The proof adapts the existing fixed-modulus cokernel argument to variable powers
on the sequence site. It constructs the quotient coefficient action using
`PresheafOfModules.sheafify` with the identity on the underlying abelian sheaf,
proves the specified forgetful functor fully faithful using its section formulas,
and identifies the quotient projection with the actual supplied adjunction unit.
All supporting declarations are proved private helpers in the item module.
The node proof and proof dependencies now describe this construction.

Added proof imports of `Sheaf.Paper.SemilinearSystemModels` (including its private
proved vertical-slice sheaf criterion), Mathlib module sheafification, and
`Mathlib.Algebra.Module.ZMod`. The two original public imports stay unchanged.

## Proved and sorry left

Closed the one original hole, `powerSystem_ordinary_cokernel`
(node `lem-sfb-power-system-ordinary-cokernel`). Added zero holes; zero holes
remain in the item. This is a complete proof, not a decomposition.

Validation: the complete module compiled through `lcompile.py` in 15.1 seconds
with no warnings, below the unchanged 60-second per-file limit.

## No longer needed

No original imports were removed: both are needed by the unchanged statement.
The proof does not need `lem-pur-system-ringed-sequence-site`
(`Sheaf.CategoryTheory.SystemRingedSequenceSite`): it constructs the action
on the existing sequence-site model directly instead of transporting through
strict-system equivalence. It does not need
`lem-cbc-constant-ring-module-sheaves`
(`Sheaf.CategoryTheory.ConstantRingModuleSheaves`): the variable coefficient
presheaf is sheafified directly using Mathlib's existing general construction.
Both dependencies are removed from this node's proof plan; this does not claim
that either module is unused by the rest of the library.

## Where the brief, the DAG or earlier work was wrong

The statement and its planned ordinary-quotient argument are correct.
The existing fixed-modulus construction in
`Sheaf.Paper.DivisibleExtensionDerivedReduction` provides the categorical
comparison argument. Extending the raw coefficient action on the sequence site
handles the varying moduli without another unresolved intermediate theorem.
The construction also covers zero towers and the empty scheme: only local
bijectivity of constant sheafification is used, never injectivity or
surjectivity of its section maps on each object.

## Second reading by J4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
