/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.CupProduct
public import WeilConjectures.SixFunctors.ProEtale.Adic.ConstantCohomologyDualityFrobenius

/-!
# The cup product on `Hⁿ(S_proét, ℤ/ℓᵐ)`

Through the explicit comparison `Hom_{D(S_ét, Λ)}(Λ_S, Λ_S[n]) ≅ Hⁿ(S_proét, ℤ_ℓ/ℓᵐ)`,
`Λ = ℤ/ℓᵐ` (`AlgebraicGeometry.ProEtale.unitShiftAddEquivFiniteAdicH`), the cup product of the
étale cohomology classes (`AlgebraicGeometry.Etale.cupProduct`) defines a biadditive cup product
`Hⁱ(S, ℤ/ℓᵐ) × Hʲ(S, ℤ/ℓᵐ) ⟶ Hᵏ(S, ℤ/ℓᵐ)`, `i + j = k`
(`AlgebraicGeometry.ProEtale.finiteAdicCup`). It is graded commutative
(`AlgebraicGeometry.ProEtale.finiteAdicCup_comm`), and, for an automorphism `e` of a connected
`S`, compatible with the pullbacks `e^*` (`AlgebraicGeometry.ProEtale.finiteAdicCup_pullback`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

namespace AlgebraicGeometry.ProEtale

open Scheme

variable (l : ℕ) [Fact l.Prime] (m : ℕ) (S : Scheme.{u})

section Shift

variable {C : Type*} [Category C] [HasShift C ℤ]

/-- The identification `N[a] = N[b]` for `a = b`. -/
abbrev shiftCast (N : C) {a b : ℤ} (h : a = b) : N⟦a⟧ ⟶ N⟦b⟧ :=
  eqToHom (by rw [h])

end Shift

lemma frobeniusOperator_comp_shiftCast {Λ : Type (u + 1)} [CommRing Λ] {X : Scheme.{u}}
    (g : X ⟶ X) {a b : ℤ} (h : a = b)
    (x : 𝟙_ (Etale.DerivedCategoryModule Λ X) ⟶ (𝟙_ (Etale.DerivedCategoryModule Λ X))⟦a⟧) :
    Etale.frobeniusOperator g (Etale.shiftWeilDatum g (Etale.leftDerivedUpperStarUnitIso _ g).hom b)
        (x ≫ shiftCast (𝟙_ (Etale.DerivedCategoryModule Λ X)) h) =
      Etale.frobeniusOperator g
        (Etale.shiftWeilDatum g (Etale.leftDerivedUpperStarUnitIso _ g).hom a) x ≫
        shiftCast (𝟙_ (Etale.DerivedCategoryModule Λ X)) h := by
  subst h
  simp

variable [CompactSpace S] [QuasiSeparatedSpace S]

/-- The cup product `Hⁱ(S, ℤ/ℓᵐ) × Hʲ(S, ℤ/ℓᵐ) ⟶ Hᵏ(S, ℤ/ℓᵐ)`, `i + j = k`, of pro-étale
cohomology: the cup product of `D(S_ét, ℤ/ℓᵐ)`, read through
`AlgebraicGeometry.ProEtale.unitShiftAddEquivFiniteAdicH`. -/
noncomputable def finiteAdicCup (i j k : ℕ) (h : i + j = k) :
    FiniteAdicH S l m i →+ FiniteAdicH S l m j →+ FiniteAdicH S l m k :=
  AddMonoidHom.mk' (fun x ↦ AddMonoidHom.mk' (fun y ↦ unitShiftAddEquivFiniteAdicH l m S k
      (Etale.cupProduct _ i j ((unitShiftAddEquivFiniteAdicH l m S i).symm x)
        ((unitShiftAddEquivFiniteAdicH l m S j).symm y) ≫
          shiftCast (𝟙_ (Etale.DerivedCategoryModule _ S)) (by omega)))
      fun y y' ↦ by simp [Preadditive.add_comp])
    fun x x' ↦ by ext y; simp [Preadditive.add_comp]

lemma finiteAdicCup_apply (i j k : ℕ) (h : i + j = k) (x : FiniteAdicH S l m i)
    (y : FiniteAdicH S l m j) :
    finiteAdicCup l m S i j k h x y = unitShiftAddEquivFiniteAdicH l m S k
      (Etale.cupProduct _ i j ((unitShiftAddEquivFiniteAdicH l m S i).symm x)
        ((unitShiftAddEquivFiniteAdicH l m S j).symm y) ≫
          shiftCast (𝟙_ (Etale.DerivedCategoryModule _ S)) (by omega)) :=
  rfl

set_option maxHeartbeats 1600000 in
-- the derived categories of étale sheaves make unification slow
/-- **The cup product on `Hⁿ(S, ℤ/ℓᵐ)` is graded commutative**:
`y ⌣ x = (-1)^{ij} x ⌣ y`. -/
theorem finiteAdicCup_comm (i j k : ℕ) (h : i + j = k) (x : FiniteAdicH S l m i)
    (y : FiniteAdicH S l m j) :
    finiteAdicCup l m S j i k (by omega) y x =
      (((i : ℤ) * j).negOnePow : ℤ) • finiteAdicCup l m S i j k h x y := by
  rw [finiteAdicCup_apply, finiteAdicCup_apply]
  refine (congrArg (unitShiftAddEquivFiniteAdicH l m S k) ?_).trans
    (map_zsmul (unitShiftAddEquivFiniteAdicH l m S k) _ _)
  rw [Etale.cupProduct_comm, Units.smul_def, Preadditive.zsmul_comp, Category.assoc,
    eqToHom_trans]

set_option maxHeartbeats 1600000 in
-- the derived categories of étale sheaves make unification slow
/-- **The cup product on `Hⁿ(S, ℤ/ℓᵐ)` is compatible with the pullback along an automorphism**
`e` of a connected `S`: `e^*(x ⌣ y) = e^* x ⌣ e^* y`. -/
theorem finiteAdicCup_pullback [ConnectedSpace S] (e : S ≅ S) (i j k : ℕ) (h : i + j = k)
    (x : FiniteAdicH S l m i) (y : FiniteAdicH S l m j) :
    finiteAdicHPullback e l m k (finiteAdicCup l m S i j k h x y) =
      finiteAdicCup l m S i j k h (finiteAdicHPullback e l m i x)
        (finiteAdicHPullback e l m j y) := by
  have hsymm (n : ℕ) (z : FiniteAdicH S l m n) :
      (unitShiftAddEquivFiniteAdicH l m S n).symm (finiteAdicHPullback e l m n z) =
        Etale.frobeniusOperator e.hom (Etale.shiftWeilDatum e.hom
          (Etale.leftDerivedUpperStarUnitIso _ e.hom).hom n)
            ((unitShiftAddEquivFiniteAdicH l m S n).symm z) := by
    rw [AddEquiv.symm_apply_eq, ← finiteAdicHPullback_unitShiftAddEquivFiniteAdicH,
      AddEquiv.apply_symm_apply]
  rw [finiteAdicCup_apply, finiteAdicCup_apply, finiteAdicHPullback_unitShiftAddEquivFiniteAdicH]
  refine congrArg (unitShiftAddEquivFiniteAdicH l m S k) ?_
  rw [hsymm, hsymm, ← Etale.frobeniusOperator_cupProduct]
  exact frobeniusOperator_comp_shiftCast _ _ _

end AlgebraicGeometry.ProEtale
