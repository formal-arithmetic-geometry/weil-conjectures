## What changed

Proved `AlgebraicGeometry.Etale.exists_normalizedDerivedDirectImageCoherence` without
changing its statement. The compositor is the inverse of the existing
`Functor.rightDerivedFunctorPlusCompIso'`, and the identity comparison is
`lowerStarIdDerivedPlus`. The proof checks the prescribed normalization, uniqueness,
associativity, and both unit laws.

Private proved helpers establish the inverse compositor's normalization, extension of
natural-transformation equality from injective representatives, and the right identity
calculation. A private coefficient-category generalization assembles these facts, and the
public theorem specializes it to `ModuleCat Λ`. All helpers are proved; no new public
interface or modules are added.

Updated the existing node's proof route to match the generic derived-functor API and the
underived coherence theorems actually used. The unit route is preserved.

## Proved and sorry left

Closed the one original hole in
`AlgebraicGeometry.Etale.exists_normalizedDerivedDirectImageCoherence`
(node `lem-cbc-etale-derived-direct-image-coherence`). Zero holes added; zero holes left
in the delivered module. No split-off statements.

## No longer needed

Removed these private imports:

- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence`: the generic
  `rightDerivedFunctorPlusCompIso'_assoc` and `lowerStarComp_assoc'` prove associativity
  directly; no compactification or lower-shriek theory is used.
- `WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact`: preservation of
  injectives follows directly from the existing constant-coefficient étale pullback
  adjunction and its preservation of monomorphisms.
- `Sheaf.AlgebraicGeometry.EtaleModuleEnoughInjectives`: the already available
  Grothendieck abelian instances for `Sheaf T.smallEtaleTopology (ModuleCat Λ)` supply
  enough injectives directly; the separate SheafOfModules formulation is unnecessary.
- `Mathlib.Algebra.Homology.DerivedCategory.KInjective`: no Hom bijection is needed;
  naturality at an injective representative is sufficient for uniqueness.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`: redundant, already publicly
  imported by the retained coherence API.

The proof no longer directly uses nodes `def-pc-fibre-product`,
`prop-weil-pbc-inverse-image-modules-exact`,
`lem-weil-pbc-module-sheaves-enough-injectives`, or
`lem-weil-pbc-kinjective-hom-derived`. Fibre-product comparisons and their coherence
are already proved by the source library; the construction and naturality of derived
functors are already supplied by its universal-property API. The unused top-level
`tool_uses` approvals for the module inverse-image exactness and dedicated enough-injectives
nodes were removed; the right-derived injective-computation approval was retained.
These are removals from this proof's dependencies, not claims that all other parents have
stopped using these modules or nodes. No module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The DAG's representative-by-representative construction and use of the K-injective Hom
bijection are unnecessary: the source library already constructs and proves coherence of
bounded-below derived compositors. Its forward comparisons are opposite to the direction
needed here, so the proof explicitly takes inverses and verifies the normalization.

The enough-injectives dependency's specialized theorem is stated for constant-ring
SheafOfModules (and abelian sheaves), whereas this item's statement uses sheaves valued
in `ModuleCat Λ`. The existing general Grothendieck abelian sheaf instances give exactly
the category needed, without an encoding conversion or any new assumptions.

## Second reading by K5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
