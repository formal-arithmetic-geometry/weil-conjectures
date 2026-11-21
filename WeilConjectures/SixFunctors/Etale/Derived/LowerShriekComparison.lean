/-
Copyright (c) 2026 Weil conjectures project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weil conjectures project
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusAdjunction
public import WeilConjectures.Compactification.RefinementPullback
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComparison.CompositionLaw
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComparison.Defs
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComparison.IdentityLaw
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.BaseChange

/-!
# Comparison of derived lower shrieks along a refinement of compactifications

Let `f : X ⟶ Y` be a morphism of schemes, let `c` and `d` be compactifications of `f` and let
`r : c.Refinement d` be a refinement, i.e. a morphism `q = r.hom : c.Z ⟶ d.Z` with
`c.i ≫ q = d.i` and `q ≫ d.g = c.g`. This file constructs the comparison

`Rf_!(d)[A]+ ⟶ Rf_!(c)[A]+`

of the bounded below derived lower shrieks attached to the two compactifications, under the
hypothesis that the square formed by `c.i : X ⟶ c.Z`, `d.i : X ⟶ d.Z`, `𝟙 X` and `q` is
cartesian, i.e. `q ⁻¹ (X) = X`. With `q = r.hom`, the comparison is the composite

```
D(d.i)_! ⋙ R(d.g)_*
  ⟶ D(d.i)_! ⋙ Dq^* ⋙ Rq_* ⋙ R(d.g)_*    (unit of `Dq^* ⊣ Rq_*`)
  ⟶ D(c.i)_! ⋙ Rq_* ⋙ R(d.g)_*           (inverse of base change for `j_!`)
  ⟶ D(c.i)_! ⋙ R(c.g)_*                  (composition of derived pushforwards)
```

## Main definitions

- `AlgebraicGeometry.Etale.refinementLowerStarComp`: the composition isomorphism
  `(r.hom)_* ⋙ (d.g)_* ≅ (c.g)_*` of pushforwards attached to a refinement.

- `AlgebraicGeometry.Etale.rightDerivedLowerShriekOfCompactificationPlusComparison`: the
  comparison `Rf_!(d)[A]+ ⟶ Rf_!(c)[A]+` above.

## Main results

- `AlgebraicGeometry.Etale.rightDerivedLowerShriekOfCompactificationPlusComparison_id`: the
  identity law, i.e. the comparison attached to the identity refinement of a
  compactification is the identity.

- `AlgebraicGeometry.Etale.rightDerivedLowerShriekOfCompactificationPlusComparison_comp`:
  the composition law, i.e. the comparison attached to a composite `r.comp s` of
  refinements is the composite of the two comparisons. Since the comparison runs from the
  coarser to the finer compactification, it is contravariant in the refinement and the
  order of the composite is reversed.

## Implementation details

The comparison goes from the *coarser* compactification `d` to the *finer* one `c`. Neither
direction is formal: the adjunctions produce a cospan of natural transformations into
`D(d.i)_! ⋙ Dq^* ⋙ Rq_* ⋙ R(d.g)_*`, and one of the two legs has to be inverted. Inverting the
leg coming from the base change comparison for `j_!` is what the cartesian hypothesis allows;
inverting the other leg is proper base change and gives the opposite direction.

Only the bounded below variant is constructed here. The unbounded variant is
`AlgebraicGeometry.Etale.rightDerivedLowerShriekOfCompactificationComparison`, in
`WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded`. That the
comparison is an isomorphism is proper base change and is not proved here.

The identity and composition laws rest on the corresponding laws for the base change
isomorphisms (`AlgebraicGeometry.Etale.refinementLowerShriekBaseChangeDerivedPlusIso_inv_id`,
`AlgebraicGeometry.Etale.refinementLowerShriekBaseChangeDerivedPlusIso_inv_comp`), for the
derived units (`AlgebraicGeometry.Etale.derivedPlus_unit_comp_upperStarCompDerivedPlus`) and
for the composition isomorphisms of the derived pushforwards
(`Functor.rightDerivedFunctorPlusCompIso'_assoc`,
`AlgebraicGeometry.Etale.refinementLowerStarComp_comp`).

This module imports its parts: the definitions are in
`WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComparison.Defs`, the identity law in
`WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComparison.IdentityLaw` and the composition
law in `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComparison.CompositionLaw`.
-/
