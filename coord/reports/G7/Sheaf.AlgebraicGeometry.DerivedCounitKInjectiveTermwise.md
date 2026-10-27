## What changed

Proved `AlgebraicGeometry.Etale.derivedCounitKInjectiveTermwise` directly from
Mathlib's `CategoryTheory.Adjunction.derivedε_fac_app` for the existing homotopy
adjunction. The K-injective unit is invertible; expanding the existing
`rightDerivedFunctorObjQIso` and cancelling its image gives the original
five-factor formula. The statement, universes, and public imports are unchanged.
Updated the theorem docstring and the node's proof, proof dependencies and proof
origin to match this calculation. No definitions or consumer interfaces changed.
The final module compiles cleanly through `lcompile.py` (41.9 seconds).

## Proved and sorry left

Closed the sole hole:
`AlgebraicGeometry.Etale.derivedCounitKInjectiveTermwise`
(node `lem-asd-derived-counit-k-injective-termwise`).
One original hole closed, zero holes added, zero holes left in the delivered module.
No split-off declarations or new modules.

## No longer needed

Removed these nine private proof imports:

- `Sheaf.AlgebraicGeometry.ExactUnboundedExchange`
- `Sheaf.AlgebraicGeometry.KInjectiveResolutionsExist`
- `Sheaf.CategoryTheory.ExactFunctorDerivedFunctor`
- `Sheaf.CategoryTheory.KInjectiveTotalDerived`
- `WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact`
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp`
- `WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction`
- `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`

The last four are already supplied by the public imports; their constructions
remain used transitively. The other five modules' separate theorems and exchange
definitions are unnecessary for this direct calculation.

Removed from this node's proof dependencies:

- `def-kun-unbounded-exchange`: no exchange transformation occurs in this proof.
- `lem-weil-pbc-exact-functor-derived-functor`: the canonical exact descent and
  the derived-adjunction instances are already constructed in the source library.
- `lem-weil-pbc-kinjective-hom-derived`: no explicit Hom-bijection calculation.
- `lem-weil-pbc-kinjective-total-derived`: the existing canonical right-derived
  unit and its K-injective invertibility instance suffice; no existential derived
  functor construction is needed.
- `lem-weil-pbc-right-adjoint-preserves-kinjective`: only I, not its direct image,
  needs to be K-injective for counit compatibility and cancellation.
- `prop-weil-pbc-inverse-image-modules-exact`: the coefficient-sheaf exactness
  instances are supplied by the existing functor definitions; the separate
  ringed-site module comparison theorem is not used.
- `prop-weil-pbc-kinjective-resolutions-exist`: the stronger functorial-resolution
  theorem is unnecessary; the source library already supplies the category's
  K-injective derivability structure.

Retained the inverse-image definitions, exact descent definition and termwise
homotopy adjunction in the proof route. Removed five now-unused top-level tool
approvals, retaining the homotopy-adjunction approval in its original order.
These are local dependency removals, not claims that other parents no longer use
these modules. No module or declaration is withdrawn; the unit route is preserved.

## Where the brief, the DAG or earlier work was wrong

The planned five-Hom-bijection computation is valid but unnecessary: the existing
derived adjunction is defined using Mathlib's general construction, whose
`derivedε_fac_app` supplies the precise compatibility equation directly.
There is no statement error or repair, and no change to a target or definition.

## Second reading by G7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
