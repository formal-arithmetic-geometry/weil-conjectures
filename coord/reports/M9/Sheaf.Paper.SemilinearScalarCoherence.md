## What changed

Proved `WeilConjectures.SemilinearSections.systemScalarCoherence_nonempty` in
`Sheaf.Paper.SemilinearScalarCoherence`, with its statement and existing public import
preserved. Added proof imports of `Sheaf.Paper.ScalarDataExistence`,
`Mathlib.CategoryTheory.Adjunction.CompositionIso`, and
`WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate`.

The existing scalar-data theorem applied to constant towers supplies each normalized
scalar adjunction. Mathlib adjunction conjugation supplies the composite comparison
and its transpose equation. Private, proved helpers establish the strict transition
cocycle from the section formulas, prove preservation of that equation under ordinary
exact localization, and transpose it to the actual reduction cocycle. Updated the
item node's proof, proof dependencies and proof origin to this route.

## Proved and sorry left

Closed the one original hole:
`WeilConjectures.SemilinearSections.systemScalarCoherence_nonempty`
(node `lem-coef-semilinear-scalar-coherence`). Added zero holes and zero split-off
statements. The delivered module has no `sorry`. This closes the assigned hole using
existing declared dependencies; it does not claim that every imported dependency is
independent of `sorry`.

Validation: the delivered module compiled cleanly through `lcompile.py` in 19.0 s,
with no warnings. All added helper theorems are proved; there are no new modules.

## No longer needed

No existing public import or declaration was removed, and no module is withdrawn.
The former plan's following dependencies are not used directly by this proof:

- `lem-pc-derived-adjoint-functors`
  (`Sheaf.CategoryTheory.DerivedCategory.AdjointFunctors`): normalized adjunctions
  are already provided by `lem-coef-semilinear-scalar-data`.
- `lem-pc-kflat-resolution`
  (`Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`): no new
  K-flat resolution is constructed here.
- `lem-pur-derived-change-of-rings`
  (`Sheaf.Algebra.Homology.OrdinaryDerivedChangeOfRings`): the needed generic
  sheaf-ring models are already in the normalized scalar-data theorem.
- `lem-pur-left-derived-from-kflat-class`
  (`WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass`):
  no new derived scalar functor is constructed here.
- `lem-weil-pbc-exact-functor-derived-functor`
  (`Sheaf.CategoryTheory.ExactFunctorDerivedFunctor`): exact localization and its
  factorization identities suffice; the Kan-extension characterization is unused.
- `lem-weil-pbc-ringed-topoi-module-adjunction`
  (`Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction`): the ordinary scalar
  adjunction and normalization are already present in ScalarData.
- `lem-weil-pbc-ringed-topos-kflat-pullback`
  (`Sheaf.Paper.KFlatRingedToposPullback`): the coherence calculation uses only
  exact restrictions and the existing scalar adjunctions, not K-flat pullback.
- `lem-weil-pbc-site-derived-tensor-descent`
  (`Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients`):
  no system tensor or internal-Hom structure is needed for scalar coherence.

These are removals from this node's direct proof dependencies, not claims that their
modules are globally unreachable or absent from the existing scalar construction's
transitive dependencies. The exact-functor factorization dependency is retained.
The unit statement and route are unchanged.

## Where the brief, the DAG or earlier work was wrong

The original proof plan asked to construct normalized scalar adjunctions afresh,
although the already proved `semilinearScalarData` supplies them. Its constant-tower
specialization works for every sheaf-ring morphism. The remaining coherence is
strict-transition functoriality followed by localization and adjunction transposition;
no additional tensor-descent or K-flat-pullback obligation is needed.

The proof treats identity indices and zero coefficient rings uniformly and imposes
no extra flatness, boundedness, nonzero-ring or invertibility hypothesis.

## Second reading by M9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
