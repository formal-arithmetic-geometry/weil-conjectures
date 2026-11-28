/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Integral.IntegralReductionTowerWellDefined
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.CategoryTheory.Limits.Cones

/-! # The integral reduction tower

The natural-number index n denotes exponent n+1. We use the chosen complex
representative K and its chosen K-flat resolution q:P→K. The already recorded
chain-level maps are characterized by the sheafified pure-tensor formulas.

## Implementation details

Compatibility of the maps from K with the tower follows from the pure-tensor formulas
τ_n γ_(n+1)=γ_n on sections, sheafification, and induction over composites of consecutive
arrows of the opposite natural-number category.

## References

* [Bhatt--Scholze, *The pro-étale topology for schemes*, Proposition 3.5.1(1) and
  Definition 3.5.2]
* [Stacks, Tag 06YL]
-/

@[expose] public section

set_option autoImplicit false

universe d t u

open CategoryTheory CategoryTheory.Limits Opposite

namespace WeilConjectures

attribute [local irreducible] completedIntegralCoefficientSheafUnrestricted

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (Y : AlgebraicGeometry.Scheme.{t})
  (D : FiniteFieldDatum.{d}) (hl : l ≠ D.p)

/-- The inverse system of the restricted termwise reductions of P, with transitions
[id⊗ρ_n]. For a K-flat resolution of K this represents Res_n(K⊗ᴸA_{E,n+1}). -/
noncomputable def integralReductionTower
    (P : CochainComplex (completedIntegralModuleSheaves l E Y D hl) ℤ) :
    ℕᵒᵖ ⥤ completedIntegralDerivedCategory l E Y D hl :=
  Functor.ofOpSequence
    (X := fun n => DerivedCategory.Q.obj (integralTowerComplex l E Y D hl n P))
    (fun n =>
    DerivedCategory.Q.map (integralTowerTransition l E Y D hl P n))

/-- The map c_n=[q]⁻¹≫[γ_n] to the reduction at exponent n+1, where γ_n(x)=x⊗1. -/
noncomputable def integralReductionTowerMap
    {P K : CochainComplex (completedIntegralModuleSheaves l E Y D hl) ℤ}
    (q : P ⟶ K)
    (hq : CochainComplex.IsKFlatResolutionIndependentCoefficients
      (J := AlgebraicGeometry.Scheme.ProEt.topology Y)
      (R := completedIntegralCommRingSheaf l E Y D hl) q) (n : ℕ) :
    DerivedCategory.Q.obj K ⟶ (integralReductionTower l E Y D hl P).obj (op n) :=
  (integralTowerAugmentationIso l E Y D hl q hq).inv ≫
    DerivedCategory.Q.map (integralTowerUnit l E Y D hl P n)

/-- The maps from K are compatible with every arrow in the reduction tower. -/
theorem integralReductionTowerMap_naturality
    {P K : CochainComplex (completedIntegralModuleSheaves l E Y D hl) ℤ}
    (q : P ⟶ K)
    (hq : CochainComplex.IsKFlatResolutionIndependentCoefficients
      (J := AlgebraicGeometry.Scheme.ProEt.topology Y)
      (R := completedIntegralCommRingSheaf l E Y D hl) q)
    (i j : ℕᵒᵖ) (f : i ⟶ j) :
    ((Functor.const ℕᵒᵖ).obj (DerivedCategory.Q.obj K)).map f ≫
        integralReductionTowerMap l E Y D hl q hq j.unop =
      integralReductionTowerMap l E Y D hl q hq i.unop ≫
        (integralReductionTower l E Y D hl P).map f := by
  have hcomp (n : ℕ) :
      integralTowerUnit l E Y D hl P (n + 1) ≫ integralTowerTransition l E Y D hl P n =
        integralTowerUnit l E Y D hl P n := by
    have hunit : integralTowerUnitCondition l E Y D hl P (integralTowerUnit l E Y D hl P) :=
      (integralTowerMaps_existUnique l E Y D hl P).exists.choose_spec.1
    have hstep : integralTowerTransitionCondition l E Y D hl P
        (integralTowerTransition l E Y D hl P) :=
      (integralTowerMaps_existUnique l E Y D hl P).exists.choose_spec.2
    ext a U x
    change (((integralTowerTransition l E Y D hl P n).f a).val.app U)
      ((((integralTowerUnit l E Y D hl P (n + 1)).f a).val.app U) x) =
      (((integralTowerUnit l E Y D hl P n).f a).val.app U) x
    erw [hunit (n + 1) a U x, hunit n a U x]
    simpa only [map_one] using hstep n a U 1 x
  let : HasSheafify (AlgebraicGeometry.Scheme.ProEt.topology Y)
      AddCommGrpCat.{max u (t + 1)} := integralCoefficientAbSheafify.{t, u} Y
  let : (AlgebraicGeometry.Scheme.ProEt.topology Y).WEqualsLocallyBijective
      AddCommGrpCat.{max u (t + 1)} := integralCoefficientAbLocallyBijective.{t, u} Y
  let α : (Functor.const ℕᵒᵖ).obj (DerivedCategory.Q.obj K) ⟶
      integralReductionTower l E Y D hl P :=
    NatTrans.ofOpSequence (fun n ↦ integralReductionTowerMap l E Y D hl q hq n)
      (by
        intro n
        simp only [Functor.const_obj_map, integralReductionTower,
          Functor.ofOpSequence_map_homOfLE_succ, integralReductionTowerMap,
          Category.assoc, ← Functor.map_comp, hcomp]
        exact Category.id_comp _)
  exact α.naturality f

/-- The reduction tower together with its compatible maps from K, as a cone.
The comparison isomorphisms and both independence identities for another resolution
are integralTowerComparison and integralReductionTowerWellDefined, respectively. -/
noncomputable def integralReductionTowerCone
    {P K : CochainComplex (completedIntegralModuleSheaves l E Y D hl) ℤ}
    (q : P ⟶ K)
    (hq : CochainComplex.IsKFlatResolutionIndependentCoefficients
      (J := AlgebraicGeometry.Scheme.ProEt.topology Y)
      (R := completedIntegralCommRingSheaf l E Y D hl) q) :
    Cone (integralReductionTower l E Y D hl P) where
  pt := DerivedCategory.Q.obj K
  π :=
    { app := fun n => integralReductionTowerMap l E Y D hl q hq n.unop
      naturality := integralReductionTowerMap_naturality l E Y D hl q hq }

end WeilConjectures
