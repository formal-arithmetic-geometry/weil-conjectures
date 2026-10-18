/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import WeilConjectures.Algebra.Module.ZModSelfInjective
public import WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.DualTateData
public import WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.TraceEquivariance
public import WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.UnitPairing
public import WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.UntwistedPerfectness
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLowerStarWeil
public import WeilConjectures.SixFunctors.Etale.Derived.WeilFrobeniusAdjunction
public import WeilConjectures.SixFunctors.ProEtale.Adic.FiniteAdicHFinite
public import WeilConjectures.WeilSheaf.CohomologyAdicConstantLattice

/-!
# Frobenius-equivariant Poincaré duality for a smooth proper geometrically connected scheme

Let `X₀` be smooth, proper and geometrically connected of pure dimension `d` over `k₀ = 𝔽_q`, and
`Hⁱ = Hⁱ(X₀ ⊗ k̄, ℚ̄_ℓ)` with its geometric Frobenius `F`. For `i + j = 2d` there is a perfect
pairing `Hⁱ × Hʲ ⟶ ℚ̄_ℓ` with `⟨F x, F y⟩ = q^d ⟨x, y⟩`
(`AlgebraicGeometry.WeilSheaf.exists_isPerfPair_cohomology_adicConstant_of_isProper`).

At each finite level `Λ = ℤ/ℓᵐ` the untwisted degreewise Poincaré pairing
`H^i_c(X̄, Λ) × H^j(X̄, Λ) ⟶ Λ(-d)` of the geometric fibre is nondegenerate
(`AlgebraicGeometry.Etale.TateOrientation.nondegenerate_untwistedDegreewisePoincarePairing`) and a
`q^d`-similitude for the Frobenius operators
(`AlgebraicGeometry.Etale.TateOrientation.untwistedDegreewisePoincarePairing_unit_frobeniusOperator`),
given the Weil equivariance of the smooth trace
(`AlgebraicGeometry.Etale.exists_tateOrientation_isWeilMorphism_untwistedSmoothTrace`). Read through
`H^i_c = H^i` (`a` proper), the adjunction `La^* ⊣ Ra_*` (which intertwines the Frobenius operators,
`AlgebraicGeometry.Etale.frobeniusOperator_unitShiftAddEquivLowerStar`) and a trivialisation of
`Λ(-d)` over `k̄`, these are the finite-level dualities of
`AlgebraicGeometry.WeilSheaf.exists_isPerfPair_cohomology_adicConstant_of_unitPairing`, which
transports them to `ℚ̄_ℓ`
(`AlgebraicGeometry.Etale.exists_unitPairing_frobeniusOperator_geometricGaloisFrobenius`).

This is clause (1) of blueprint `thm-pod-qbar-coefficient-pairing` for the constant sheaf on a
proper `X₀` (`H_c = H`), with the similitude of `cor-pod-untwisted-similitude`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Opposite

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

open Scheme

variable {Λ : Type (u + 1)} [CommRing Λ]

/-- Read through `Λ_X ≅ Λ_X^∨` (`AlgebraicGeometry.Etale.coefficientDualUnitIso`), the evaluation
`Λ_X ⊗ᴸ Λ_X^∨ ⟶ Λ_X` is the left unitor. -/
lemma derivedTensor_map_coefficientDualUnitIso_inv_comp_coefficientEvaluation
    (X : Scheme.{u}) :
    ((derivedTensor _ X).obj (𝟙_ (DerivedCategoryModule Λ X))).map
        (coefficientDualUnitIso Λ X).inv ≫
      DerivedCategory.coefficientEvaluation (𝟙_ (DerivedCategoryModule Λ X)) =
        (λ_ (𝟙_ (DerivedCategoryModule Λ X))).hom := by
  have h := Adjunction.rightAdjointUniq_hom_app_counit Adjunction.id
    ((derivedTensorHomAdjunction _ (𝟙_ (DerivedCategoryModule Λ X))).ofNatIsoLeft
      (derivedTensorLeftUnitorNatIso _ X)) (𝟙_ _)
  rw [Adjunction.ofNatIsoLeft_counit, NatTrans.comp_app, Functor.whiskerLeft_app,
    Adjunction.id_counit, NatTrans.id_app, Functor.id_map, ← Adjunction.rightAdjointUniq_inv_app,
    ← Iso.app_inv] at h
  have e1 : (λ_ (𝟙_ (DerivedCategoryModule Λ X))).inv ≫
      ((derivedTensor _ X).obj (𝟙_ (DerivedCategoryModule Λ X))).map
        (coefficientDualUnitIso Λ X).inv =
      (coefficientDualUnitIso Λ X).inv ≫ (λ_ _).inv := by
    rw [derivedTensor_obj_map]
    exact (leftUnitor_inv_naturality _).symm
  rw [← cancel_epi (λ_ (𝟙_ (DerivedCategoryModule Λ X))).inv, Iso.inv_hom_id, reassoc_of% e1]
  exact h

/-- The canonical identification `Λ_X ≅ Λ_X^∨` is a morphism of Weil objects, from the canonical
datum of `Λ_X` to the contragredient datum of `Λ_X^∨`. -/
lemma isWeilMorphism_coefficientDualUnitIso_inv {X : Scheme.{u}} (g : X ⟶ X) :
    IsWeilMorphism g (leftDerivedUpperStarUnitIso _ g).hom
      (contragredientWeilDatum _ g (leftDerivedUpperStarUnitIso _ g))
      (coefficientDualUnitIso Λ X).inv := by
  let := leftDerivedUpperStarMonoidal (ModuleCat.{u + 1} Λ) g
  have hε : Functor.LaxMonoidal.ε L((g)^*[ModuleCat.{u + 1} Λ]) =
      (leftDerivedUpperStarUnitIso _ g).inv := by
    rw [← cancel_mono (leftDerivedUpperStarUnitIso _ g).hom, Iso.inv_hom_id]
    have := leftDerivedUpperStarUnitIso_hom_eq_η (Λ := Λ) g
    exact this ▸ Functor.Monoidal.ε_η _
  unfold IsWeilMorphism
  apply ((derivedTensorHomAdjunction _ (𝟙_ (DerivedCategoryModule Λ X))).homEquiv _
    _).symm.injective
  simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc]
  erw [derivedTensor_map_contragredientWeilDatum_comp_coefficientEvaluation,
    derivedTensor_map_coefficientDualUnitIso_inv_comp_coefficientEvaluation]
  rw [← leftDerivedUpperStarMonoidal_μ, ← hε, derivedTensor_obj_map, derivedTensor_obj_map,
    derivedTensor_map_app, ← whisker_exchange_assoc, Functor.LaxMonoidal.μ_natural_right_assoc,
    ← Functor.map_comp_assoc, ← derivedTensor_obj_map,
    derivedTensor_map_coefficientDualUnitIso_inv_comp_coefficientEvaluation,
    ← Functor.LaxMonoidal.left_unitality_assoc]
  exact (leftUnitor_naturality _).symm

/-- Composition with an isomorphism, as an additive equivalence of Hom groups, is composition. -/
lemma _root_.CategoryTheory.Iso.postcompAddEquiv_apply' {C : Type*} [Category C] [Preadditive C]
    {X Y Y' : C} (e : Y ≅ Y') (f : X ⟶ Y) : e.postcompAddEquiv f = f ≫ e.hom := by
  simp

variable [Finite Λ]

/-- **Frobenius operators on `Hⁿ(X, Λ)` and on `Hⁿ_c(Y, Ra_! Λ)`.** For `a` proper and a cartesian
square `g ≫ a = a ≫ h`, the identification `Hom(Λ_X, Λ_X[n]) ≅ Hom(Λ_Y, (Ra_! Λ_X)[n])` given by
the adjunction `La^* ⊣ Ra_*` and `Ra_* ≅ Ra_!` intertwines the Frobenius operators of the canonical
Weil data, `Ra_!` carrying the induced datum. -/
theorem frobeniusOperator_unitShiftAddEquivLowerStar_comp_lowerShriek {X Y : Scheme.{u}}
    {a : X ⟶ Y} [IsProper a] {g : X ⟶ X} {h : Y ⟶ Y} (sq : IsPullback g a a h) (n : ℤ)
    (x : 𝟙_ (DerivedCategoryModule Λ X) ⟶ (𝟙_ (DerivedCategoryModule Λ X))⟦n⟧) :
    frobeniusOperator h (shiftWeilDatum h
        (lowerShriekWeilDatum sq (leftDerivedUpperStarUnitIso _ g).hom) n)
      (unitShiftAddEquivLowerStar Λ a n x ≫
        ((rightDerivedLowerShriekIsoRightDerivedLowerStar _ a).inv.app _)⟦n⟧') =
      unitShiftAddEquivLowerStar Λ a n (frobeniusOperator g
          (shiftWeilDatum g (leftDerivedUpperStarUnitIso _ g).hom n) x) ≫
        ((rightDerivedLowerShriekIsoRightDerivedLowerStar _ a).inv.app _)⟦n⟧' := by
  have hw : IsWeilMorphism h (lowerStarWeilDatum sq.toCommSq (leftDerivedUpperStarUnitIso _ g).hom)
      (lowerShriekWeilDatum sq (leftDerivedUpperStarUnitIso _ g).hom)
      ((rightDerivedLowerShriekIsoRightDerivedLowerStar _ a).inv.app _) :=
    IsWeilMorphism.of_iso_inv ((rightDerivedLowerShriekIsoRightDerivedLowerStar _ a).app _).symm
      (lowerShriekWeilDatum_comp_rightDerivedLowerShriekIsoRightDerivedLowerStar_hom_app
        (Λ := Λ) sq _).symm
  rw [(hw.shift n).frobeniusOperator_comp, frobeniusOperator_unitShiftAddEquivLowerStar sq.toCommSq]

section FiniteLevel

variable {k₀ : Type u} [Field k₀] [Finite k₀] {X₀ : Scheme.{u}} (f : X₀ ⟶ Spec (.of k₀)) (d : ℕ)
  [SmoothOfRelativeDimension d f] [IsProper f]
  (Λ) [HasTateTwist Λ] [Module.Injective Λ Λ]
  [HasInvertibleExponent Λ (Spec (.of (AlgebraicClosure k₀)))]
  [HasInvertibleExponent Λ f.geometricFiber] [IsProper f.geometricFiberToAlgebraicClosure]
  [GeometricallyConnected f.geometricFiberToAlgebraicClosure] [ConnectedSpace f.geometricFiber]

/-- **Finite-level Frobenius-equivariant Poincaré duality for the constant sheaf** (finite level of
blueprint `thm-pod-qbar-coefficient-pairing`, with the similitude of `cor-pod-untwisted-similitude`).
For `X₀` smooth and proper of relative dimension `d` over `k₀ = 𝔽_q` with connected geometric fibre
`X̄`, a finite self-injective cogenerating quotient ring `Λ` of `ℤ` invertible on `X̄`, and
`i + j = 2d`, there is a biadditive pairing `Hⁱ(X̄, Λ) × Hʲ(X̄, Λ) ⟶ Λ`, nondegenerate on both sides,
with `⟨F x, F y⟩ = q^d ⟨x, y⟩` for the Frobenius operators `F` of the geometric Galois Frobenius. -/
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
  obtain ⟨h₁, h₂⟩ := γ.nondegenerate_untwistedDegreewisePoincarePairing hΛ hcog (𝟙_ _) i j hij
  have hF := γ.untwistedDegreewisePoincarePairing_unit_frobeniusOperator
    f.isPullback_geometricGaloisFrobenius _ (isWeilPairing_coefficientEvaluation _
      (leftDerivedUpperStarUnitIso _ f.geometricGaloisFrobenius.hom)) _
    (isWeilMorphism_coefficientDualUnitIso_inv _) τ hTr (Nat.card k₀) hτ i j hij
  let eI := (unitShiftAddEquivLowerStar Λ f.geometricFiberToAlgebraicClosure i).trans
    ((shiftFunctor (DerivedCategoryModule Λ (Spec (.of (AlgebraicClosure k₀)))) i).mapIso
      ((rightDerivedLowerShriekIsoRightDerivedLowerStar _
        f.geometricFiberToAlgebraicClosure).app _).symm).postcompAddEquiv
  let eJ := (unitShiftAddEquivLowerStar Λ f.geometricFiberToAlgebraicClosure j).trans
    ((shiftFunctor (DerivedCategoryModule Λ (Spec (.of (AlgebraicClosure k₀)))) j).mapIso
      ((R((f.geometricFiberToAlgebraicClosure)_*[ModuleCat.{u + 1} Λ])).mapIso
        (coefficientDualUnitIso Λ _).symm)).postcompAddEquiv
  let eL := ι.postcompAddEquiv.trans (endUnitAddEquiv Λ (Spec (.of (AlgebraicClosure k₀)))).symm
  have heI (x) : eI x = unitShiftAddEquivLowerStar Λ _ i x ≫
      ((rightDerivedLowerShriekIsoRightDerivedLowerStar _
        f.geometricFiberToAlgebraicClosure).inv.app _)⟦i⟧' :=
    by rw [AddEquiv.trans_apply, Iso.postcompAddEquiv_apply']; rfl
  have heJ (y) : eJ y = unitShiftAddEquivLowerStar Λ _ j y ≫
      ((R((f.geometricFiberToAlgebraicClosure)_*[ModuleCat.{u + 1} Λ])).map
        (coefficientDualUnitIso Λ _).inv)⟦j⟧' :=
    by rw [AddEquiv.trans_apply, Iso.postcompAddEquiv_apply']; rfl
  let B := γ.untwistedDegreewisePoincarePairing (𝟙_ _) i j hij
  refine ⟨AddMonoidHom.mk' (fun x ↦ AddMonoidHom.mk' (fun y ↦ eL (B (eI x) (eJ y)))
    fun y y' ↦ by simp) fun x x' ↦ by ext y; simp, fun x hx ↦ ?_, fun y hy ↦ ?_, fun x y ↦ ?_⟩
  · refine eI.injective ((h₁ (eI x) fun y' ↦ ?_).trans (map_zero eI).symm)
    obtain ⟨y, rfl⟩ := eJ.surjective y'
    exact (AddEquiv.map_eq_zero_iff eL).1 (hx y)
  · refine eJ.injective ((h₂ (eJ y) fun x' ↦ ?_).trans (map_zero eJ).symm)
    obtain ⟨x, rfl⟩ := eI.surjective x'
    exact (AddEquiv.map_eq_zero_iff eL).1 (hy x)
  · change eL (B (eI _) (eJ _)) = _ • eL (B (eI x) (eJ y))
    rw [heI, heJ, heI, heJ, ← frobeniusOperator_unitShiftAddEquivLowerStar_comp_lowerShriek
      f.isPullback_geometricGaloisFrobenius, ← frobeniusOperator_unitShiftAddEquivLowerStar
      f.isPullback_geometricGaloisFrobenius.toCommSq, hF, ← Nat.cast_pow, Nat.cast_smul_eq_nsmul,
      map_nsmul]

end FiniteLevel

end AlgebraicGeometry.Etale

namespace AlgebraicGeometry.WeilSheaf

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))] (d : ℕ)
  [IsProper (X ↘ Spec (CommRingCat.of k₀))]
  [SmoothOfRelativeDimension d (X ↘ Spec (CommRingCat.of k₀))]
  [GeometricallyConnected (X ↘ Spec (CommRingCat.of k₀))]

/-- Blueprint `thm-pod-qbar-coefficient-pairing` (clause (1), for the constant sheaf on a proper
`X₀`, with the similitude of `cor-pod-untwisted-similitude`): for `X₀` smooth, proper and
geometrically connected of pure dimension `d` over `k₀` and `i + j = 2d`, there is a perfect pairing
`Hⁱ(X₀ ⊗ k̄, ℚ̄_ℓ) × Hʲ(X₀ ⊗ k̄, ℚ̄_ℓ) ⟶ ℚ̄_ℓ` with `⟨F x, F y⟩ = q^d ⟨x, y⟩` for the geometric
Frobenius `F`. -/
theorem exists_isPerfPair_cohomology_adicConstant_of_isProper (i j : ℕ) (h : i + j = 2 * d) :
    ∃ P : ((adicConstant k₀ l X).cohomology i).carrier →ₗ[PadicAlgCl l]
        ((adicConstant k₀ l X).cohomology j).carrier →ₗ[PadicAlgCl l] PadicAlgCl l,
      P.IsPerfPair ∧ ∀ x y, P (((adicConstant k₀ l X).cohomology i).frobenius x)
        (((adicConstant k₀ l X).cohomology j).frobenius y) =
          (Nat.card k₀ : PadicAlgCl l) ^ d * P x y := by
  classical
  let f := X ↘ Spec (CommRingCat.of k₀)
  let a := f.geometricFiberToAlgebraicClosure
  have : ConnectedSpace f.geometricFiber :=
    GeometricallyConnected.geometrically_connectedSpace (f := f)
      (Scheme.specAlgebraicClosure k₀).hom f.geometricFiberProj a (IsPullback.of_hasPullback _ _)
  have : IsProper a :=
    MorphismProperty.of_isPullback (P := @IsProper) (IsPullback.of_hasPullback _ _) ‹_›
  have : GeometricallyConnected a :=
    MorphismProperty.of_isPullback (P := @GeometricallyConnected)
      (IsPullback.of_hasPullback _ _) ‹_›
  have := smoothOfRelativeDimension_isStableUnderBaseChange (n := d)
  have : SmoothOfRelativeDimension d a :=
    MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension d)
      (IsPullback.of_hasPullback _ _) ‹_›
  have hl : ((l : ℕ) : AlgebraicClosure k₀) ≠ 0 := by
    intro h0
    have h1 : ((l : ℕ) : k₀) = 0 := by
      exact (algebraMap k₀ (AlgebraicClosure k₀)).injective (by simpa using h0)
    exact (Fact.out : ringChar k₀ ≠ l)
      ((Nat.Prime.eq_one_or_self_of_dvd (Fact.out : l.Prime) _
        (ringChar.dvd h1)).resolve_left (CharP.ringChar_ne_one))
  have hfin : ∀ m k, Finite (ProEtale.FiniteAdicH f.geometricFiber l m k) :=
    fun m k ↦ ProEtale.finite_finiteAdicH l a hl m k
  have key (m : ℕ) : ∃ P : (𝟙_ (Etale.DerivedCategoryModule (ULift.{u + 1} (ZMod (l ^ m)))
        f.geometricFiber) ⟶ (𝟙_ (Etale.DerivedCategoryModule (ULift.{u + 1} (ZMod (l ^ m)))
          f.geometricFiber))⟦(i : ℤ)⟧) →+
      (𝟙_ (Etale.DerivedCategoryModule (ULift.{u + 1} (ZMod (l ^ m))) f.geometricFiber) ⟶
        (𝟙_ (Etale.DerivedCategoryModule (ULift.{u + 1} (ZMod (l ^ m)))
          f.geometricFiber))⟦(j : ℤ)⟧) →+ ULift.{u + 1} (ZMod (l ^ m)),
      (∀ x, (∀ y, P x y = 0) → x = 0) ∧ (∀ y, (∀ x, P x y = 0) → y = 0) ∧
      ∀ x y, P (Etale.frobeniusOperator f.geometricGaloisFrobenius.hom
          (Etale.shiftWeilDatum f.geometricGaloisFrobenius.hom
            (Etale.leftDerivedUpperStarUnitIso _ f.geometricGaloisFrobenius.hom).hom i) x)
        (Etale.frobeniusOperator f.geometricGaloisFrobenius.hom
          (Etale.shiftWeilDatum f.geometricGaloisFrobenius.hom
            (Etale.leftDerivedUpperStarUnitIso _ f.geometricGaloisFrobenius.hom).hom j) y) =
        (Nat.card k₀ ^ d) • P x y := by
    let Λ := ULift.{u + 1} (ZMod (l ^ m))
    have : NeZero (l ^ m) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
    have : NeZero (ringChar Λ) := by rw [ringChar.eq Λ (l ^ m)]; infer_instance
    have : HasInvertibleExponent Λ (Spec (.of (AlgebraicClosure k₀))) :=
      ⟨l ^ m, Nat.pos_of_ne_zero (NeZero.ne _), ULift.ext _ _ (by simp [Λ]), by
        simpa using ((Ne.isUnit (pow_ne_zero m hl)).map
          (Scheme.ΓSpecIso (.of (AlgebraicClosure k₀))).inv.hom)⟩
    have : HasInvertibleExponent Λ f.geometricFiber := .of_hom a
    have hcog : ∀ (M : ModuleCat.{u + 1} Λ) (x : M), x ≠ 0 → ∃ χ : M →ₗ[Λ] Λ, χ x ≠ 0 :=
      fun M x hx ↦ ZModLike.exists_apply_ne_zero (n := l ^ m)
        (Nat.pos_of_ne_zero (NeZero.ne _)) (ULift.ext _ _ (by
          simpa using (Nat.cast_pow l m).symm.trans (ZMod.natCast_self (l ^ m))))
        (fun x ↦ ⟨(ZMod.intCast_surjective x.down).choose, ULift.ext _ _ (by
          simpa using (ZMod.intCast_surjective x.down).choose_spec)⟩)
        (fun z hz ↦ (ZMod.intCast_zmod_eq_zero_iff_dvd z _).1 (by
          simpa using congrArg ULift.down hz)) hx
    have hΛ : Function.Surjective (Int.cast : ℤ → Λ) := fun x ↦
      ⟨(ZMod.intCast_surjective x.down).choose, ULift.ext _ _
        ((ULift.down_intCast _).trans (ZMod.intCast_surjective x.down).choose_spec)⟩
    exact Etale.exists_unitPairing_frobeniusOperator_geometricGaloisFrobenius (f := f) (d := d)
      (Λ := Λ)
      hΛ hcog i j
      (by exact_mod_cast h)
  choose P hPl hPr hPF using key
  obtain ⟨P', hP', hP'F⟩ := exists_isPerfPair_cohomology_adicConstant_of_unitPairing (Y := X) hfin
    i j (Nat.card k₀ ^ d) P hPl hPr hPF
  refine ⟨P', hP', fun x y ↦ ?_⟩
  rw [hP'F, map_natCast, Nat.cast_pow]

end AlgebraicGeometry.WeilSheaf
