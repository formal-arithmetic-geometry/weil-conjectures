/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q63
-/
module

public import Sheaf.Paper.IntegralReductionTowerWellDefinedUnrestricted
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.CategoryTheory.Limits.Cones

/-! # The integral reduction tower

Source: Bhatt--Scholze, p. 24, Proposition 3.5.1(1) and Definition 3.5.2;
Stacks Project, Tag 06YL (blueprint: def-weil-integral-reduction-tower).

The natural-number index n denotes exponent n+1. We use the chosen complex
representative K and its chosen K-flat resolution q:P→K. The already recorded
chain-level maps are characterized by the sheafified pure-tensor formulas.

The interface omits the unused auxiliary finite-field datum. It uses the existing
completed coefficient ring, projections and scalar extension with independent
site and coefficient universes.

## Main definitions

- `canonicalIntegralReductionTower`: the inverse system of restricted finite reductions.
- `canonicalIntegralReductionTowerMap`: the compatible maps from the represented object.
- `canonicalIntegralReductionTowerCone`: the augmented reduction tower.
-/

@[expose] public section

set_option autoImplicit false

universe t u

open CategoryTheory CategoryTheory.Limits Opposite

namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (Y : AlgebraicGeometry.Scheme.{t})

/-- The inverse system of the restricted termwise reductions of P, with transitions
[id⊗ρ_n]. For a K-flat resolution of K this represents Res_n(K⊗ᴸA_{E,n+1}).
Source: Bhatt--Scholze, p. 24, Definition 3.5.2; Stacks Tag 06YL
(blueprint: def-weil-integral-reduction-tower). -/
noncomputable def canonicalIntegralReductionTower
    (P : CochainComplex (scalarReductionSource l E Y) ℤ) :
    ℕᵒᵖ ⥤ DerivedCategory (scalarReductionSource l E Y) :=
  Functor.ofOpSequence
    (X := fun n ↦ DerivedCategory.Q.obj (unrestrictedTowerComplex l E Y n P))
    (fun n ↦
    DerivedCategory.Q.map (unrestrictedTowerTransition l E Y P n))

/-- The map c_n=[q]⁻¹≫[γ_n] to the reduction at exponent n+1, where γ_n(x)=x⊗1.
Source: Bhatt--Scholze, p. 24, Definition 3.5.2; Stacks Tag 06YL
(blueprint: def-weil-integral-reduction-tower). -/
noncomputable def canonicalIntegralReductionTowerMap
    {P K : CochainComplex (scalarReductionSource l E Y) ℤ}
    (q : P ⟶ K)
    (hq : CochainComplex.IsKFlatResolutionIndependentCoefficients
      (J := AlgebraicGeometry.Scheme.ProEt.topology Y)
      (R := completedIntegralCommRingSheafUnrestricted l E Y) q) (n : ℕ) :
    DerivedCategory.Q.obj K ⟶ (canonicalIntegralReductionTower l E Y P).obj (op n) :=
  (unrestrictedTowerAugmentationIso l E Y q hq).inv ≫
    DerivedCategory.Q.map (unrestrictedTowerUnit l E Y P n)

/-- The maps from K are compatible with every arrow in the reduction tower.
Source: Bhatt--Scholze, p. 24, Definition 3.5.2; Stacks Tag 06YL
(blueprint: def-weil-integral-reduction-tower).
Proof: the defining pure-tensor formulas give τ_n γ_(n+1)=γ_n on sections,
since the coefficient reduction sends 1 to 1. The universal property of
sheafification and equality degree by degree give equality of chain maps.
Localization preserves composition. Precompose with [q]⁻¹ to obtain
c_(n+1)≫t_n=c_n. Every arrow m→n of the opposite natural-number category is
a finite composite of consecutive arrows (the identity when m=n), so induction
on m-n gives the stated compatibility for all arrows. -/
theorem canonicalIntegralReductionTowerMap_naturality
    {P K : CochainComplex (scalarReductionSource l E Y) ℤ}
    (q : P ⟶ K)
    (hq : CochainComplex.IsKFlatResolutionIndependentCoefficients
      (J := AlgebraicGeometry.Scheme.ProEt.topology Y)
      (R := completedIntegralCommRingSheafUnrestricted l E Y) q)
    (i j : ℕᵒᵖ) (f : i ⟶ j) :
    ((Functor.const ℕᵒᵖ).obj (DerivedCategory.Q.obj K)).map f ≫
        canonicalIntegralReductionTowerMap l E Y q hq j.unop =
      canonicalIntegralReductionTowerMap l E Y q hq i.unop ≫
        (canonicalIntegralReductionTower l E Y P).map f := by
  have hcomp (n : ℕ) :
      unrestrictedTowerUnit l E Y P (n + 1) ≫ unrestrictedTowerTransition l E Y P n =
        unrestrictedTowerUnit l E Y P n := by
    have hunit : unrestrictedTowerUnitCondition l E Y P (unrestrictedTowerUnit l E Y P) :=
      unrestrictedTowerUnit_condition l E Y P
    ext a U x
    change (((unrestrictedTowerTransition l E Y P n).f a).val.app U)
        ((((unrestrictedTowerUnit l E Y P (n + 1)).f a).val.app U) x) =
      (((unrestrictedTowerUnit l E Y P n).f a).val.app U) x
    rw [hunit (n + 1) a U x, hunit n a U x]
    change (((unrestrictedIntegralTransition l E Y n).app P).f a).val.app U
        (unrestrictedIntegralTensorSection l E Y (n + 1) (P.X a) U 1 x) =
      unrestrictedIntegralTensorSection l E Y n (P.X a) U 1 x
    simpa [unrestrictedIntegralTransition] using
      (unrestrictedIntegralTransition_existsUnique l E Y n).exists.choose_spec P a U 1 x
  let : HasSheafify (AlgebraicGeometry.Scheme.ProEt.topology Y)
      AddCommGrpCat.{max u (t + 1)} := integralCoefficientAbSheafify.{t, u} Y
  let : (AlgebraicGeometry.Scheme.ProEt.topology Y).WEqualsLocallyBijective
      AddCommGrpCat.{max u (t + 1)} := integralCoefficientAbLocallyBijective.{t, u} Y
  let α : (Functor.const ℕᵒᵖ).obj (DerivedCategory.Q.obj K) ⟶
      canonicalIntegralReductionTower l E Y P :=
    NatTrans.ofOpSequence (fun n ↦ canonicalIntegralReductionTowerMap l E Y q hq n)
      (by
        intro n
        simp only [Functor.const_obj_map, canonicalIntegralReductionTower,
          Functor.ofOpSequence_map_homOfLE_succ, canonicalIntegralReductionTowerMap,
          Category.assoc, ← Functor.map_comp, hcomp]
        exact Category.id_comp _)
  exact α.naturality f

/-- The reduction tower together with its compatible maps from K, as a cone.
The comparison isomorphisms and both independence identities for another resolution
are unrestrictedTowerComparison and unrestrictedReductionTowerWellDefined, respectively.
Source: Bhatt--Scholze, p. 24, Definition 3.5.2; Stacks Tag 06YL
(blueprint: def-weil-integral-reduction-tower). -/
noncomputable def canonicalIntegralReductionTowerCone
    {P K : CochainComplex (scalarReductionSource l E Y) ℤ}
    (q : P ⟶ K)
    (hq : CochainComplex.IsKFlatResolutionIndependentCoefficients
      (J := AlgebraicGeometry.Scheme.ProEt.topology Y)
      (R := completedIntegralCommRingSheafUnrestricted l E Y) q) :
    Cone (canonicalIntegralReductionTower l E Y P) where
  pt := DerivedCategory.Q.obj K
  π :=
    { app := fun n ↦ canonicalIntegralReductionTowerMap l E Y q hq n.unop
      naturality := canonicalIntegralReductionTowerMap_naturality l E Y q hq }

end WeilConjectures
