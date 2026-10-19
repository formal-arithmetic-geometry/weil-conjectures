## What changed

Proved AlgebraicGeometry.Etale.closedImmersion_coprojection.
A private generic helper applies Adjunction.tensorRightCompIsoOfTensorIso to the
closed derived direct-image adjunction and the finite proper projection isomorphism.
The ambient result is specialized to pullbacks, shifted twist objects, and the two
invertible factors on the separated diagonal. Existing public signatures are unchanged.

The module compiles with the normal package options in 14.2 seconds, without warnings
or errors. Explicit types on the diagonal morphism and its two pulled-back complexes
avoid expensive inference of derived-category instances. No timeout limit was raised.
The existing declaration signature and all public imports are unchanged.

## Proved and sorry left

Closed 1 of 1 original holes: AlgebraicGeometry.Etale.closedImmersion_coprojection
(node sk-lem-coprojection). All four conjuncts have complete Lean proofs.
Added holes: zero. Sorry left in delivered modules: none.
Private proved helpers: coprojectionOfProjection and ambientCoprojection.
This is a proof from existing library declarations, not a decomposition into new holes;
existing upstream dependencies may themselves depend on unresolved theorems.

## No longer needed

Removed direct proof imports:

- WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
- Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorClosed
- Sheaf.Algebra.Homology.FlatCoverFunctor
- WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory
- Sheaf.CategoryTheory.ExactFunctorDerivedFunctor
- WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection
- Sheaf.CategoryTheory.KInjectiveTotalDerived
- WeilConjectures.SixFunctors.Finite.Exact
- Sheaf.CategoryTheory.RingedSiteModules
- WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
- Mathlib.CategoryTheory.Adjunction.Basic
- Mathlib.AlgebraicGeometry.Morphisms.Finite
- Mathlib.CategoryTheory.Yoneda
- Sheaf.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses

The exact-functor and K-injective comparison machinery, ringed-site module transport,
and finite-direct-image exactness are not used directly: the existing closed ambient
adjunction already supplies the adjunction of the actual derived direct image.
Tensor structure, pullback compatibility, inverse-tensor adjunction and Yoneda are
implemented by existing upstream declarations. The following nodes are removed from
direct proof dependencies and obsolete tool approvals:

- lem-weil-pbc-ring-sheaves-grothendieck
- lem-pc-sheaf-modules-tensor-closed
- lem-pc-sites-modules-functorial-flat-cover
- prop-weil-pbc-inverse-image-modules-exact (retained as a statement dependency)
- lem-weil-pbc-exact-functor-derived-functor
- lem-weil-pbc-kinjective-total-derived
- lemma-weil-pbc-finite-direct-image-exact
- def-weil-sheaf-of-modules-category
- lem-galois-yoneda-fully-faithful
- lem-weil-pbc-closed-immersion-finite

The tensor and inverse-image infrastructure is used through its existing upstream
interfaces; the adjunction of the actual derived direct image is supplied by
lem-exc-closed-ambient. Generic uniqueness of right adjoints packages the Yoneda
argument. Removing a direct import does not assert that its module is absent from
the entire targets' transitive import closure.

## Where the brief, the DAG or earlier work was wrong

The current EtaleClosedAmbientAdjoint already proves the IsLeftAdjoint
instance for R(lowerStar), so no additional identification with a termwise direct
image is needed here. The existing generic adjunction helper realizes the source's
Hom/Yoneda argument without using the compactification-defined upper shriek.
The source Coprojection theorem itself was not used, since its right adjoint differs
from the right adjoint in this item's statement.

The sandbox inherited diagnostic heartbeat options from an interrupted attempt; these
were removed. The generic helper explicitly imports KFlat and UpperStarMonoidal.Comparison
because their declarations must be visible at its definition. The diagonal proof needed
explicit local types; it now compiles without a definition change or any consumer adaptation.
No new nodes, definitions in the public API, or statement repairs are needed.
Preflight requested a record for the private helper's section variables and local instance:
coord/changes/etale-closed-coprojection-private-setup.md. It documents their scope and
the unchanged interfaces of all consumers; no consumer adaptation is necessary.

## Second reading by B5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
