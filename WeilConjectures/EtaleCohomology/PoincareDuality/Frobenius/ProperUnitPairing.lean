/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.DualTateData
public import WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.TraceEquivariance
public import WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.UnitPairing
public import WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.UntwistedPerfectness
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLowerStarWeil
public import WeilConjectures.SixFunctors.Etale.Derived.WeilFrobeniusAdjunction

/-!
# Frobenius-equivariant finite-level duality for a smooth proper scheme over `𝔽_q`

Let `X₀` be smooth and proper of relative dimension `d` over `k₀ = 𝔽_q`, with connected geometric
fibre `a : X̄ ⟶ Spec k̄`, and `Λ = ℤ/ℓᵐ` with `ℓ` invertible. For `i + j = 2d` there is a biadditive
pairing `Hⁱ(X̄, Λ) × Hʲ(X̄, Λ) ⟶ Λ`, nondegenerate on both sides, with `⟨F x, F y⟩ = q^d ⟨x, y⟩` for
the Frobenius operators `F` of the geometric Galois Frobenius
(`AlgebraicGeometry.Etale.exists_unitPairing_frobeniusOperator_geometricGaloisFrobenius`).

It is the untwisted degreewise Poincaré pairing of `Λ_X̄`, which is nondegenerate
(`AlgebraicGeometry.Etale.TateOrientation.nondegenerate_untwistedDegreewisePoincarePairing`) and a
`q^d`-similitude
(`AlgebraicGeometry.Etale.TateOrientation.untwistedDegreewisePoincarePairing_unit_frobeniusOperator`)
given the Weil equivariance of the smooth trace
(`AlgebraicGeometry.Etale.exists_tateOrientation_isWeilMorphism_untwistedSmoothTrace`), read through
`Hⁱ_c = Hⁱ` (`a` proper), `Λ_X̄ ≅ Λ_X̄^∨` (a morphism of Weil objects,
`AlgebraicGeometry.Etale.isWeilMorphism_unitCoefficientDualIso_inv`) and `Λ(-d) ≅ Λ` over `k̄`.
The identification `Hⁱ(X̄, Λ) ≅ Hⁱ_c(X̄, Λ)` intertwines the Frobenius operators
(`AlgebraicGeometry.Etale.frobeniusOperator_unitShiftAddEquivLowerStar_comp_lowerShriek`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Opposite

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

open Scheme

section General

variable (A : Type*) [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

/-- The derived tensor product acts on a morphism in its second variable by whiskering (for the
monoidal structure of `D(X_ét)` found by instance search). -/
lemma derivedTensor_obj_map_eq_whiskerLeft (X : Scheme.{u})
    (K : DerivedCategory (Sheaf X.smallEtaleTopology A))
    {M M' : DerivedCategory (Sheaf X.smallEtaleTopology A)} (f : M ⟶ M') :
    ((derivedTensor A X).obj K).map f = K ◁ f :=
  rfl

/-- The derived tensor product acts on a morphism in its first variable by whiskering (for the
monoidal structure of `D(X_ét)` found by instance search). -/
lemma derivedTensor_map_app_eq_whiskerRight (X : Scheme.{u})
    {K K' : DerivedCategory (Sheaf X.smallEtaleTopology A)} (f : K ⟶ K')
    (M : DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    ((derivedTensor A X).map f).app M = f ▷ M :=
  rfl

/-- The coefficient dual of the unit is the unit, `RHom(Λ_X, Λ_X) ≅ Λ_X` (for an arbitrary
coefficient category; `AlgebraicGeometry.Etale.coefficientDualUnitIso` for `A = Mod_Λ`). -/
noncomputable def unitCoefficientDualIso (X : Scheme.{u}) :
    (DerivedCategory.coefficientDual A X).obj
        (op (𝟙_ (DerivedCategory (Sheaf X.smallEtaleTopology A)))) ≅
      𝟙_ (DerivedCategory (Sheaf X.smallEtaleTopology A)) :=
  (((derivedTensorHomAdjunction A (𝟙_ (DerivedCategory (Sheaf X.smallEtaleTopology A)))).ofNatIsoLeft
    (derivedTensorLeftUnitorNatIso A X)).rightAdjointUniq Adjunction.id).app _

/-- Read through `Λ_X ≅ Λ_X^∨`, the evaluation `Λ_X ⊗ᴸ Λ_X^∨ ⟶ Λ_X` is the left unitor. -/
lemma derivedTensor_map_unitCoefficientDualIso_inv_comp_coefficientEvaluation
    (X : Scheme.{u}) :
    ((derivedTensor A X).obj (𝟙_ _)).map (unitCoefficientDualIso A X).inv ≫
      DerivedCategory.coefficientEvaluation (𝟙_ (DerivedCategory (Sheaf X.smallEtaleTopology A))) =
        (λ_ (𝟙_ (DerivedCategory (Sheaf X.smallEtaleTopology A)))).hom := by
  have h := Adjunction.rightAdjointUniq_hom_app_counit Adjunction.id
    ((derivedTensorHomAdjunction A (𝟙_ (DerivedCategory (Sheaf X.smallEtaleTopology A)))).ofNatIsoLeft
      (derivedTensorLeftUnitorNatIso A X)) (𝟙_ _)
  rw [Adjunction.ofNatIsoLeft_counit, NatTrans.comp_app, Functor.whiskerLeft_app,
    Adjunction.id_counit, NatTrans.id_app, Functor.id_map, ← Adjunction.rightAdjointUniq_inv_app,
    ← Iso.app_inv] at h
  rw [derivedTensor_obj_map_eq_whiskerLeft,
    ← cancel_epi (λ_ (𝟙_ (DerivedCategory (Sheaf X.smallEtaleTopology A)))).inv, Iso.inv_hom_id,
    ← leftUnitor_inv_naturality_assoc]
  exact h

variable [UpperStarPreservesFlat A]

/-- The identification `Λ_X ≅ Λ_X^∨` intertwines the canonical datum of `Λ_X` with the
contragredient datum of `Λ_X^∨` (a morphism of Weil objects). -/
lemma map_unitCoefficientDualIso_inv_comp_contragredientWeilDatum {X : Scheme.{u}}
    (g : X ⟶ X) :
    L((g)^*[A]).map (unitCoefficientDualIso A X).inv ≫
        contragredientWeilDatum A g (leftDerivedUpperStarUnitIso A g) =
      (leftDerivedUpperStarUnitIso A g).hom ≫ (unitCoefficientDualIso A X).inv := by
  apply ((derivedTensorHomAdjunction A
    (𝟙_ (DerivedCategory (Sheaf X.smallEtaleTopology A)))).homEquiv _ _).symm.injective
  have hev : (derivedTensorHomAdjunction A
      (𝟙_ (DerivedCategory (Sheaf X.smallEtaleTopology A)))).counit.app (𝟙_ _) =
      DerivedCategory.coefficientEvaluation (𝟙_ (DerivedCategory (Sheaf X.smallEtaleTopology A))) :=
    rfl
  rw [Adjunction.homEquiv_counit, Adjunction.homEquiv_counit, Functor.map_comp,
    Functor.map_comp, Category.assoc, Category.assoc, hev,
    derivedTensor_map_contragredientWeilDatum_comp_coefficientEvaluation,
    derivedTensor_map_unitCoefficientDualIso_inv_comp_coefficientEvaluation]
  have hU := leftDerivedUpperStarTensorComparison_leftUnitor_hom A g
    (𝟙_ (DerivedCategory (Sheaf X.smallEtaleTopology A)))
  rw [← leftDerivedUpperStarTensorIso_hom, ← derivedTensor_map_app_eq_whiskerRight] at hU
  have hT : ((derivedTensor A X).obj (L((g)^*[A]).obj (𝟙_ _))).map
        (L((g)^*[A]).map (unitCoefficientDualIso A X).inv) ≫
      (leftDerivedUpperStarTensorIso A g (𝟙_ _) _).inv =
      (leftDerivedUpperStarTensorIso A g (𝟙_ _) _).inv ≫
        L((g)^*[A]).map (((derivedTensor A X).obj (𝟙_ _)).map (unitCoefficientDualIso A X).inv) := by
    rw [Iso.comp_inv_eq, Category.assoc, leftDerivedUpperStarTensorIso_hom_naturality_right,
      Iso.inv_hom_id_assoc]
  rw [(derivedTensor A X |>.map (leftDerivedUpperStarUnitIso A g).inv).naturality_assoc,
    reassoc_of% hT, ← Functor.map_comp_assoc,
    derivedTensor_map_unitCoefficientDualIso_inv_comp_coefficientEvaluation, ← hU]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [
    ← NatTrans.comp_app_assoc, ← Functor.map_comp, Iso.inv_hom_id,
    CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp,
    derivedTensor_obj_map_eq_whiskerLeft]
  exact (leftUnitor_naturality _).symm


/-- For a proper `a`, `Ra_* Λ_X ≅ Ra_! Λ_X`, given by the inverse of
`AlgebraicGeometry.Etale.rightDerivedLowerShriekIsoRightDerivedLowerStar` at the unit. It is
stated as an existence statement so that the unit object occurring in it is the one of the
generic monoidal structure. -/
lemma exists_iso_rightDerivedLowerStar_unit_rightDerivedLowerShriek {X Y : Scheme.{u}}
    (a : X ⟶ Y) [IsProper a] :
    ∃ s : (R((a)_*[A])).obj (𝟙_ (DerivedCategory (Sheaf X.smallEtaleTopology A))) ≅
      (R(a)_![A]).obj (𝟙_ (DerivedCategory (Sheaf X.smallEtaleTopology A))),
      s.hom = (rightDerivedLowerShriekIsoRightDerivedLowerStar A a).inv.app
        (𝟙_ (DerivedCategory (Sheaf X.smallEtaleTopology A))) :=
  ⟨((rightDerivedLowerShriekIsoRightDerivedLowerStar A a).app _).symm, rfl⟩

end General

variable {Λ : Type (u + 1)} [CommRing Λ]

/-- The canonical identification `Λ_X ≅ Λ_X^∨` is a morphism of Weil objects, from the canonical
datum of `Λ_X` to the contragredient datum of `Λ_X^∨`. -/
lemma isWeilMorphism_unitCoefficientDualIso_inv {X : Scheme.{u}} (g : X ⟶ X) :
    IsWeilMorphism g (leftDerivedUpperStarUnitIso _ g).hom
      (contragredientWeilDatum _ g (leftDerivedUpperStarUnitIso _ g))
      (unitCoefficientDualIso (ModuleCat.{u + 1} Λ) X).inv :=
  map_unitCoefficientDualIso_inv_comp_contragredientWeilDatum _ g

/-- Postcomposing an additive equivalence of Hom groups with an isomorphism of the target. -/
lemma _root_.CategoryTheory.exists_addEquiv_comp_iso_hom {C D : Type*} [Category C]
    [Preadditive C] [Category D] [Preadditive D] {Z A : C} {W B B' : D}
    (e : (Z ⟶ A) ≃+ (W ⟶ B)) (s : B ≅ B') :
    ∃ e' : (Z ⟶ A) ≃+ (W ⟶ B'), ∀ x, e' x = e x ≫ s.hom :=
  ⟨e.trans s.postcompAddEquiv, fun x ↦ by simp⟩

variable [Finite Λ]

/-- `Ra_* ≅ Ra_!` is a morphism of Weil objects for the induced data, for `a` proper and a
cartesian square `g ≫ a = a ≫ h`. -/
lemma isWeilMorphism_rightDerivedLowerShriekIsoRightDerivedLowerStar_inv_app {X Y : Scheme.{u}}
    {a : X ⟶ Y} [IsProper a] {g : X ⟶ X} {h : Y ⟶ Y} (sq : IsPullback g a a h)
    {K : DerivedCategoryModule Λ X} (φ : (L((g)^*[ModuleCat.{u + 1} Λ])).obj K ⟶ K) :
    IsWeilMorphism h (lowerStarWeilDatum sq.toCommSq φ) (lowerShriekWeilDatum sq φ)
      ((rightDerivedLowerShriekIsoRightDerivedLowerStar _ a).inv.app K) :=
  IsWeilMorphism.of_iso_inv ((rightDerivedLowerShriekIsoRightDerivedLowerStar _ a).app K).symm
    (lowerShriekWeilDatum_comp_rightDerivedLowerShriekIsoRightDerivedLowerStar_hom_app sq φ).symm

section FiniteLevel

variable {k₀ : Type u} [Field k₀] [Finite k₀] {X₀ : Scheme.{u}} (f : X₀ ⟶ Spec (.of k₀)) (d : ℕ)
  [SmoothOfRelativeDimension d f] [IsProper f]
  (Λ) [HasTateTwist Λ] [Module.Injective Λ Λ]
  [HasInvertibleExponent Λ (Spec (.of (AlgebraicClosure k₀)))]
  [HasInvertibleExponent Λ f.geometricFiber] [IsProper f.geometricFiberToAlgebraicClosure]
  [GeometricallyConnected f.geometricFiberToAlgebraicClosure] [ConnectedSpace f.geometricFiber]

set_option maxHeartbeats 1000000 in
/-- **Finite-level Frobenius-equivariant Poincaré duality for the constant sheaf** (finite level
of blueprint `thm-pod-qbar-coefficient-pairing`, with the similitude of
`cor-pod-untwisted-similitude`). For `X₀` smooth and proper of relative dimension `d` over
`k₀ = 𝔽_q` with connected geometric fibre `X̄`, a finite self-injective cogenerating quotient
ring `Λ` of `ℤ` invertible on `X̄`, and `i + j = 2d`, there is a biadditive pairing
`Hⁱ(X̄, Λ) × Hʲ(X̄, Λ) ⟶ Λ`, nondegenerate on both sides, with `⟨F x, F y⟩ = q^d ⟨x, y⟩` for the
Frobenius operators `F` of the geometric Galois Frobenius. -/
theorem exists_unitPairing_frobeniusOperator_geometricGaloisFrobenius
    (hΛ : Function.Surjective (Int.cast : ℤ → Λ))
    (hcog : ∀ (M : ModuleCat.{u + 1} Λ) (x : M), x ≠ 0 → ∃ χ : M →ₗ[Λ] Λ, χ x ≠ 0)
    (i j : ℤ) (hij : i + j = 2 * d) :
    ∃ P : (𝟙_ (DerivedCategoryModule Λ f.geometricFiber) ⟶
          (𝟙_ (DerivedCategoryModule Λ f.geometricFiber))⟦i⟧) →+
        (𝟙_ (DerivedCategoryModule Λ f.geometricFiber) ⟶
          (𝟙_ (DerivedCategoryModule Λ f.geometricFiber))⟦j⟧) →+ Λ,
      (∀ x, (∀ y, P x y = 0) → x = 0) ∧ (∀ y, (∀ x, P x y = 0) → y = 0) ∧
      ∀ x y, P (frobeniusOperator f.geometricGaloisFrobenius.hom (shiftWeilDatum
          f.geometricGaloisFrobenius.hom
            (leftDerivedUpperStarUnitIso _ f.geometricGaloisFrobenius.hom).hom i) x)
        (frobeniusOperator f.geometricGaloisFrobenius.hom (shiftWeilDatum
          f.geometricGaloisFrobenius.hom
            (leftDerivedUpperStarUnitIso _ f.geometricGaloisFrobenius.hom).hom j) y) =
        (Nat.card k₀ ^ d) • P x y := by
  obtain ⟨γ, τ, hTr, hτ⟩ := exists_tateOrientation_isWeilMorphism_untwistedSmoothTrace f d Λ
  obtain ⟨ι⟩ := nonempty_tateObject_iso_unit Λ (AlgebraicClosure k₀) (-(d : ℤ))
  have hnd := fun K ↦ γ.nondegenerate_untwistedDegreewisePoincarePairing hΛ hcog K i j hij
  have hG := γ.untwistedDegreewisePoincarePairing_frobeniusOperator
    f.isPullback_geometricGaloisFrobenius
    (leftDerivedUpperStarUnitIso _ f.geometricGaloisFrobenius.hom).hom
    (contragredientWeilDatum _ f.geometricGaloisFrobenius.hom
      (leftDerivedUpperStarUnitIso _ f.geometricGaloisFrobenius.hom))
    (isWeilPairing_coefficientEvaluation _
      (leftDerivedUpperStarUnitIso _ f.geometricGaloisFrobenius.hom)) τ hTr (Nat.card k₀) hτ
    i j hij
  obtain ⟨s, hs⟩ := exists_iso_rightDerivedLowerStar_unit_rightDerivedLowerShriek
    (ModuleCat.{u + 1} Λ) f.geometricFiberToAlgebraicClosure
  have hsW := hs ▸ isWeilMorphism_rightDerivedLowerShriekIsoRightDerivedLowerStar_inv_app
    f.isPullback_geometricGaloisFrobenius
    (leftDerivedUpperStarUnitIso _ f.geometricGaloisFrobenius.hom).hom
  have hιW := ((isWeilMorphism_unitCoefficientDualIso_inv (Λ := Λ)
    f.geometricGaloisFrobenius.hom).rightDerivedLowerStar_map
      f.isPullback_geometricGaloisFrobenius.toCommSq).shift j
  have hFx := fun x ↦ ((hsW.shift i).frobeniusOperator_comp
    (unitShiftAddEquivLowerStar Λ f.geometricFiberToAlgebraicClosure i x)).trans
      (congrArg (· ≫ s.hom⟦i⟧') (frobeniusOperator_unitShiftAddEquivLowerStar
        f.isPullback_geometricGaloisFrobenius.toCommSq i x))
  have hFy := fun y ↦ (hιW.frobeniusOperator_comp
    (unitShiftAddEquivLowerStar Λ f.geometricFiberToAlgebraicClosure j y)).trans
      (congrArg (· ≫ _) (frobeniusOperator_unitShiftAddEquivLowerStar
        f.isPullback_geometricGaloisFrobenius.toCommSq j y))
  obtain ⟨eI, heI⟩ := exists_addEquiv_comp_iso_hom
    (unitShiftAddEquivLowerStar Λ f.geometricFiberToAlgebraicClosure i)
    ((shiftFunctor (DerivedCategoryModule Λ (Spec (.of (AlgebraicClosure k₀)))) i).mapIso s)
  obtain ⟨eJ, heJ⟩ := exists_addEquiv_comp_iso_hom
    (unitShiftAddEquivLowerStar Λ f.geometricFiberToAlgebraicClosure j)
    ((shiftFunctor (DerivedCategoryModule Λ (Spec (.of (AlgebraicClosure k₀)))) j).mapIso
      ((R((f.geometricFiberToAlgebraicClosure)_*[ModuleCat.{u + 1} Λ])).mapIso
        (unitCoefficientDualIso (ModuleCat.{u + 1} Λ) _).symm))
  simp only [Functor.mapIso_hom] at heI
  simp only [Functor.mapIso_hom, Iso.symm_hom] at heJ
  obtain ⟨eL⟩ : Nonempty ((𝟙_ (DerivedCategoryModule Λ (Spec (.of (AlgebraicClosure k₀)))) ⟶
      tateObject Λ (Spec (.of (AlgebraicClosure k₀))) (-d)) ≃+ Λ) :=
    ⟨ι.postcompAddEquiv.trans (endUnitAddEquiv Λ (Spec (.of (AlgebraicClosure k₀)))).symm⟩
  have a3 := fun x y y' ↦ (congrArg (γ.untwistedDegreewisePoincarePairing _ i j hij (eI x))
    (eJ.map_add y y')).trans ((γ.untwistedDegreewisePoincarePairing _ i j hij (eI x)).map_add _ _)
  have a4 := fun x x' y ↦ (congrArg (fun z ↦ γ.untwistedDegreewisePoincarePairing _ i j hij z
    (eJ y)) (eI.map_add x x')).trans
      (LinearMap.map_add₂ (γ.untwistedDegreewisePoincarePairing _ i j hij) _ _ (eJ y))
  refine ⟨AddMonoidHom.mk' (fun x ↦ AddMonoidHom.mk' (fun y ↦
    eL (γ.untwistedDegreewisePoincarePairing _ i j hij (eI x) (eJ y)))
      fun y y' ↦ (congrArg eL (a3 x y y')).trans (eL.map_add _ _)) fun x x' ↦
        AddMonoidHom.ext fun y ↦ (congrArg eL (a4 x x' y)).trans (eL.map_add _ _),
    fun x hx ↦ ?_, fun y hy ↦ ?_, fun x y ↦ ?_⟩
  · refine eI.injective (((hnd _).1 (eI x) fun y' ↦ ?_).trans (map_zero eI).symm)
    obtain ⟨y, rfl⟩ := eJ.surjective y'
    have := hx y
    rw [AddMonoidHom.mk'_apply, AddMonoidHom.mk'_apply] at this
    exact (AddEquiv.map_eq_zero_iff eL).1 this
  · refine eJ.injective (((hnd _).2 (eJ y) fun x' ↦ ?_).trans (map_zero eJ).symm)
    obtain ⟨x, rfl⟩ := eI.surjective x'
    have := hy x
    rw [AddMonoidHom.mk'_apply, AddMonoidHom.mk'_apply] at this
    exact (AddEquiv.map_eq_zero_iff eL).1 this
  · sorry
  rw [AddMonoidHom.mk'_apply, AddMonoidHom.mk'_apply, AddMonoidHom.mk'_apply,
      AddMonoidHom.mk'_apply, heI, heJ, heI, heJ, ← hFx, ← hFy, ← heI, ← heJ, hG,
      ← Nat.cast_pow, Nat.cast_smul_eq_nsmul, map_nsmul]

end FiniteLevel

end AlgebraicGeometry.Etale
