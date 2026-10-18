## What changed

Completed `CategoryTheory.ringedOverFunctor_preservesFiniteColimits` in
`Sheaf.CategoryTheory.RingedDerivedRestriction`, without changing any declaration's type
or any definition. The proof uses the cocontinuous sheaf adjunction for `Over.forget U`
to obtain colimit preservation for restriction of abelian sheaves. Forgetting module
structure commutes with restriction by a reflexive natural isomorphism. The existing
colimit-preservation and isomorphism-reflection results for `SheafOfModules.toSheaf`
then transfer finite-colimit preservation to module restriction.

Added the proof-only import
`WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification` for the
already-proved forgetful-functor colimit API. All public imports are retained.

## Proved and sorry left

Closed the only original hole:
`CategoryTheory.ringedOverFunctor_preservesFiniteColimits`
(blueprint `def-weil-pbc-ringed-derived-restriction`).

Holes closed: 1. Holes added: 0. Holes remaining in the delivered module: 0.
No new intermediate statements or split-offs were introduced. The proof applies
existing fully proved categorical results; it does not rely on a new admitted theorem.

## No longer needed

Removed the unused proof-only import `Mathlib.Algebra.Homology.ShortComplex.ExactFunctor`.
The finite-colimit proof does not need short-complex exactness, an explicit module-sheaf
right adjoint, or derived internal-Hom restriction results. No DAG dependency or module
is claimed globally pruned: the recorded node has no proof dependencies, and the public
imports are part of this module's existing exported interface.

The searched `WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafOver` and
`Sheaf.Algebra.Homology.RingedInternalHomExactRestriction` are not imported: the smaller
forgetful-functor API and Mathlib's cocontinuous adjunction suffice.

## Where the brief, the DAG or earlier work was wrong

The docstrings attach this module to `def-weil-pbc-ringed-derived-restriction`, but the
node's current Lean attachment names `Sheaf.CategoryTheory.RingedDerivedRestrictionGeneral`
instead. That latter source file is absent from the read-only shared repository snapshot.
The node is a definition node with empty proof/proof_deps fields, so there is no numbered
proof plan to realize for this remaining exactness theorem. The delivered proof directly
formalizes the existing theorem docstring, using the library's proven forgetful-functor
API and Mathlib's adjunction. No change to that more general attachment is required.

## Second reading by A3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
