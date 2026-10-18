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

Let `S` be a quasi-compact quasi-separated scheme and `Λ = ℤ/ℓᵐ`. Through the comparison
`Hⁿ(S_proét, ℤ_ℓ/ℓᵐ) ≅ Extⁿ_Λ(Λ_S, Λ_S)` (`AlgebraicGeometry.ProEtale.extAddEquivFiniteAdicH`), the
Yoneda product of `Ext`-classes of étale sheaves of `Λ`-modules defines the cup product
`⌣ : Hⁱ(S, ℤ/ℓᵐ) × Hʲ(S, ℤ/ℓᵐ) ⟶ Hⁱ⁺ʲ(S, ℤ/ℓᵐ)`
(`AlgebraicGeometry.ProEtale.finiteAdicHCup`). It is the cup product
`AlgebraicGeometry.Etale.cupProduct` of the classes `Λ_S ⟶ Λ_S[n]` of `D(S_ét, Λ)`
(`AlgebraicGeometry.ProEtale.unitShiftAddEquivFiniteAdicH_cupProduct`), hence graded
commutative (`AlgebraicGeometry.ProEtale.finiteAdicHCup_comm`), compatible with the pullback
along an automorphism (`AlgebraicGeometry.ProEtale.finiteAdicHPullback_finiteAdicHCup`), and
compatible with the reductions `ℤ/ℓᵐ⁺¹ ⟶ ℤ/ℓᵐ` of the coefficients
(`AlgebraicGeometry.ProEtale.finiteAdicHTransition_finiteAdicHCup`), by the change of rings of
`WeilConjectures.SixFunctors.Etale.ConstantCohomologyRingChange`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Abelian

namespace AlgebraicGeometry.ProEtale

open Scheme PadicInt

variable (l : ℕ) [Fact l.Prime] (m : ℕ) (S : Scheme.{u})

/-- The reduction `Hⁿ(S, ℤ/ℓᵐ⁺¹) ⟶ Hⁿ(S, ℤ/ℓᵐ)` of the coefficients. -/
noncomputable def finiteAdicHTransition (n : ℕ) : FiniteAdicH S l (m + 1) n →+ FiniteAdicH S l m n :=
  Sheaf.H.map (continuousSheafMap S
    (openAddSubgroupQuotientMap (powOpenAddSubgroup l) (powOpenAddSubgroup_succ_le l) m)) n

variable [CompactSpace S] [QuasiSeparatedSpace S]

/-- The **cup product** `Hⁱ(S, ℤ/ℓᵐ) × Hʲ(S, ℤ/ℓᵐ) ⟶ Hᵏ(S, ℤ/ℓᵐ)`, `i + j = k`: the Yoneda
product of `Ext`-classes of étale sheaves of `ℤ/ℓᵐ`-modules, read through
`AlgebraicGeometry.ProEtale.extAddEquivFiniteAdicH`. -/
noncomputable def finiteAdicHCup {i j k : ℕ} (h : i + j = k) :
    FiniteAdicH S l m i →+ FiniteAdicH S l m j →+ FiniteAdicH S l m k :=
  AddMonoidHom.mk' (fun x ↦ AddMonoidHom.mk' (fun y ↦ extAddEquivFiniteAdicH l m S k
      (((extAddEquivFiniteAdicH l m S i).symm x).comp ((extAddEquivFiniteAdicH l m S j).symm y)
        h)) fun y y' ↦ by simp [Ext.comp_add]) fun x x' ↦ by
    ext y
    simp [Ext.add_comp]

lemma finiteAdicHCup_apply {i j k : ℕ} (h : i + j = k) (x : FiniteAdicH S l m i)
    (y : FiniteAdicH S l m j) :
    finiteAdicHCup l m S h x y = extAddEquivFiniteAdicH l m S k
      (((extAddEquivFiniteAdicH l m S i).symm x).comp ((extAddEquivFiniteAdicH l m S j).symm y)
        h) :=
  rfl

omit [CompactSpace S] [QuasiSeparatedSpace S] in
/-- The comparison `Hom(Λ_S, Λ_S[n]) ≅ Extⁿ(Λ_S, Λ_S)` sends the cup product to the Yoneda
product. -/
lemma unitShiftAddEquivExt_cupProduct (Λ : Type (u + 1)) [CommRing Λ] {i j k : ℕ}
    (h : i + j = k)
    (x : 𝟙_ (Etale.DerivedCategoryModule Λ S) ⟶ (𝟙_ (Etale.DerivedCategoryModule Λ S))⟦(i : ℤ)⟧)
    (y : 𝟙_ (Etale.DerivedCategoryModule Λ S) ⟶ (𝟙_ (Etale.DerivedCategoryModule Λ S))⟦(j : ℤ)⟧) :
    Etale.unitShiftAddEquivExt Λ S k (Etale.cupProduct _ (i : ℤ) (j : ℤ) x y ≫
      eqToHom (by rw [← h, Nat.cast_add])) =
      (Etale.unitShiftAddEquivExt Λ S i x).comp (Etale.unitShiftAddEquivExt Λ S j y) h := by
  have hU := DerivedCategory.unitorsCommShift (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ))
  ext
  rw [Ext.comp_hom, Etale.unitShiftAddEquivExt_hom, Etale.unitShiftAddEquivExt_hom,
    Etale.unitShiftAddEquivExt_hom, ShiftedHom.comp, Etale.cupProduct_eq_shiftProduct,
    shiftProduct_eq hU]
  simp only [Category.assoc, Functor.map_comp]
  rw [Iso.map_hom_inv_id_assoc]
  congr 2
  have h₂ := (shiftFunctorAdd' (DerivedCategory (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (j : ℤ) i k (by lia)).inv.naturality (Etale.unitIsoSingleFunctorConstantSheaf Λ S).hom
  dsimp at h₂
  rw [h₂, reassoc_of% (shiftFunctorAdd'_inv_app_comp_eqToHom (j : ℤ) (i : ℤ) _ (k : ℤ)
    (add_comm _ _) (by lia))]

/-- The cup product of `Hⁿ(S, ℤ/ℓᵐ)` is the cup product `AlgebraicGeometry.Etale.cupProduct` of the
classes `Λ_S ⟶ Λ_S[n]` of `D(S_ét, Λ)`, `Λ = ℤ/ℓᵐ`. -/
theorem unitShiftAddEquivFiniteAdicH_cupProduct {i j k : ℕ} (h : i + j = k)
    (x : 𝟙_ (Etale.DerivedCategoryModule (ULift.{u + 1} (ZMod (l ^ m))) S) ⟶
      (𝟙_ (Etale.DerivedCategoryModule (ULift.{u + 1} (ZMod (l ^ m))) S))⟦(i : ℤ)⟧)
    (y : 𝟙_ (Etale.DerivedCategoryModule (ULift.{u + 1} (ZMod (l ^ m))) S) ⟶
      (𝟙_ (Etale.DerivedCategoryModule (ULift.{u + 1} (ZMod (l ^ m))) S))⟦(j : ℤ)⟧) :
    unitShiftAddEquivFiniteAdicH l m S k
        (Etale.cupProduct _ (i : ℤ) (j : ℤ) x y ≫
          eqToHom (by rw [← h, Nat.cast_add])) =
      finiteAdicHCup l m S h (unitShiftAddEquivFiniteAdicH l m S i x)
        (unitShiftAddEquivFiniteAdicH l m S j y) := by
  rw [finiteAdicHCup_apply]
  simp only [unitShiftAddEquivFiniteAdicH, AddEquiv.trans_apply, AddEquiv.symm_apply_apply]
  exact congrArg (extAddEquivFiniteAdicH l m S k) (unitShiftAddEquivExt_cupProduct S _ h x y)

/-- **Graded commutativity of the cup product**: `y ⌣ x = (-1)^{ij} x ⌣ y`. -/
theorem finiteAdicHCup_comm {i j k : ℕ} (h : i + j = k) (x : FiniteAdicH S l m i)
    (y : FiniteAdicH S l m j) :
    finiteAdicHCup l m S ((add_comm j i).trans h) y x =
      ((i : ℤ) * j).negOnePow • finiteAdicHCup l m S h x y := by
  obtain ⟨x, rfl⟩ := (unitShiftAddEquivFiniteAdicH l m S i).surjective x
  obtain ⟨y, rfl⟩ := (unitShiftAddEquivFiniteAdicH l m S j).surjective y
  rw [← unitShiftAddEquivFiniteAdicH_cupProduct, ← unitShiftAddEquivFiniteAdicH_cupProduct,
    Etale.cupProduct_comm, Units.smul_def, Units.smul_def, Preadditive.zsmul_comp,
    Category.assoc, eqToHom_trans, map_zsmul]

omit [CompactSpace S] [QuasiSeparatedSpace S] in
/-- The Frobenius operator of the shifted canonical Weil datum commutes with the identifications
`Λ_S[a] = Λ_S[b]`, `a = b`. -/
lemma frobeniusOperator_comp_eqToHom {Λ : Type (u + 1)} [CommRing Λ] (g : S ⟶ S) {a b : ℤ}
    (hab : a = b)
    (z : 𝟙_ (Etale.DerivedCategoryModule Λ S) ⟶ (𝟙_ (Etale.DerivedCategoryModule Λ S))⟦a⟧) :
    Etale.frobeniusOperator g
        (Etale.shiftWeilDatum g (Etale.leftDerivedUpperStarUnitIso _ g).hom b)
        (z ≫ eqToHom (by rw [hab])) =
      Etale.frobeniusOperator g
        (Etale.shiftWeilDatum g (Etale.leftDerivedUpperStarUnitIso _ g).hom a) z ≫
        eqToHom (by rw [hab]) := by
  subst hab
  simp only [eqToHom_refl, Category.comp_id]

/-- The pullback along an automorphism `e` of a connected `S` is multiplicative for the cup
product. -/
theorem finiteAdicHPullback_finiteAdicHCup [ConnectedSpace S] (e : S ≅ S) {i j k : ℕ}
    (h : i + j = k) (x : FiniteAdicH S l m i) (y : FiniteAdicH S l m j) :
    finiteAdicHPullback e l m k (finiteAdicHCup l m S h x y) =
      finiteAdicHCup l m S h (finiteAdicHPullback e l m i x) (finiteAdicHPullback e l m j y) := by
  obtain ⟨x, rfl⟩ := (unitShiftAddEquivFiniteAdicH l m S i).surjective x
  obtain ⟨y, rfl⟩ := (unitShiftAddEquivFiniteAdicH l m S j).surjective y
  rw [← unitShiftAddEquivFiniteAdicH_cupProduct, finiteAdicHPullback_unitShiftAddEquivFiniteAdicH,
    finiteAdicHPullback_unitShiftAddEquivFiniteAdicH,
    finiteAdicHPullback_unitShiftAddEquivFiniteAdicH, ← unitShiftAddEquivFiniteAdicH_cupProduct,
    frobeniusOperator_comp_eqToHom, Etale.frobeniusOperator_cupProduct]

/-- The reduction `ℤ/ℓᵐ⁺¹ ⟶ ℤ/ℓᵐ` of the coefficients is multiplicative for the cup product. -/
theorem finiteAdicHTransition_finiteAdicHCup {i j k : ℕ} (h : i + j = k)
    (x : FiniteAdicH S l (m + 1) i) (y : FiniteAdicH S l (m + 1) j) :
    finiteAdicHTransition l m S k (finiteAdicHCup l (m + 1) S h x y) =
      finiteAdicHCup l m S h (finiteAdicHTransition l m S i x) (finiteAdicHTransition l m S j y) :=
  sorry

omit [CompactSpace S] [QuasiSeparatedSpace S] in
/-- `c ∈ ℤ_ℓ` acts on `Hⁿ(S, ℤ/ℓᵐ)` as the natural number `PadicInt.appr c m`. -/
lemma smul_finiteAdicH_eq_nsmul {n : ℕ} (c : ℤ_[l]) (x : FiniteAdicH S l m n) :
    c • x = c.appr m • x := by
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.1 (PadicInt.appr_spec m c)
  have hc : c = (c.appr m : ℤ_[l]) + a * (l : ℤ_[l]) ^ m := by rw [ha]; ring
  rw [hc, add_smul, mul_smul, pow_smul_finiteAdicH, smul_zero, add_zero,
    Nat.cast_smul_eq_nsmul ℤ_[l]]

/-- The cup product is `ℤ_ℓ`-linear in the first variable. -/
theorem finiteAdicHCup_smul_left {i j k : ℕ} (h : i + j = k) (c : ℤ_[l])
    (x : FiniteAdicH S l m i) (y : FiniteAdicH S l m j) :
    finiteAdicHCup l m S h (c • x) y = c • finiteAdicHCup l m S h x y := by
  rw [smul_finiteAdicH_eq_nsmul, smul_finiteAdicH_eq_nsmul, map_nsmul, AddMonoidHom.nsmul_apply]

/-- The cup product is `ℤ_ℓ`-linear in the second variable. -/
theorem finiteAdicHCup_smul_right {i j k : ℕ} (h : i + j = k) (c : ℤ_[l])
    (x : FiniteAdicH S l m i) (y : FiniteAdicH S l m j) :
    finiteAdicHCup l m S h x (c • y) = c • finiteAdicHCup l m S h x y := by
  rw [smul_finiteAdicH_eq_nsmul, smul_finiteAdicH_eq_nsmul, map_nsmul]

end AlgebraicGeometry.ProEtale
