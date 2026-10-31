/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CompactSupportStrictScalarCompositionPrelude

import all WeilConjectures.AlgebraicGeometry.CompactSupportStrictScalarArrowComposition
import all WeilConjectures.AlgebraicGeometry.OrdinaryOpenScalarComposition
import WeilConjectures.AlgebraicGeometry.ConstantCompletedScalarAssociativity
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.RestrictScalars

/-! # Tensor units and coefficient identities for strict scalar composition

The existing unit constructions and finite-quotient equations are factored out
without changing their definitions or signatures. The coherence lemmas identify
the actual scalar and selection associators with these specified unit maps.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] WeilConjectures.SemilinearSections.moduleAbelian
attribute [local irreducible] CategoryTheory.Functor.mapDerivedCategory
  CategoryTheory.Functor.rightDerivedFunctor
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale.StrictTower
namespace WeilConjectures.PurStrictScalar

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (F : Type u) [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
  (i : E →ₐ[ℚ_[l]] F)
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (j : F →ₐ[ℚ_[l]] L)

/-- Identity on the constant coefficient ring, including its chosen integral model.
Source: auxiliary proof Step 6
(blueprint: lem-pur-compact-support-strict-scalar-identity-units).
Proof: the identity field embedding is identity on its valuation ring; constant
sheafification preserves the identity homomorphism and the universe lift. -/
theorem constantMap_identity (W : Scheme.{u}) :
    constantMap l E E (AlgHom.id ℚ_[l] E) W = 𝟙 _ := by
  unfold constantMap
  have hi : CommRingCat.ofHom
      (integralScalarIntegerInclusion l E E (AlgHom.id ℚ_[l] E)).ulift.{u + 1, u + 1} =
        𝟙 (CommRingCat.of (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E))) := by
    ext x
    rfl
  rw [hi, CategoryTheory.Functor.map_id]

/-- The ordinary tensor multiplication unit, conjugate to identity restriction.
Source: Stacks 07A6; auxiliary proof Step 6
(blueprint: lem-pur-compact-support-strict-scalar-identity-units). -/
def compositionUnitOrdinary (W : Scheme.{u}) :
    pbcExtend (constantMap l E E (AlgHom.id ℚ_[l] E) W) ≅ 𝟭 _ :=
  eqToIso (congrArg (fun a ↦ pbcExtend a) (constantMap_identity l E W)) ≪≫
    ((conjugateIsoEquiv (pbcScalarAdjunction (𝟙 ((constants l E).ring W)))
      (Adjunction.id : (𝟭 (pbcModules W ((constants l E).ring W))) ⊣ 𝟭 _)).symm
        (PurCompactSupport.restrictIdentity_existsUnique
          ((constants l E).ring W)).exists.choose).symm

/-- The strict-tower tensor multiplication unit is localized from the ordinary one.
Source: Stacks 0940; auxiliary proof Step 6
(blueprint: lem-pur-compact-support-strict-scalar-identity-units). -/
def compositionUnitTower (W : Scheme.{u}) :
    T l E E (AlgHom.id ℚ_[l] E) W ≅ 𝟭 _ :=
  haveI := (tensor_exact l E E (AlgHom.id ℚ_[l] E) W).1
  haveI := (tensor_exact l E E (AlgHom.id ℚ_[l] E) W).2
  Functor.mapDerivedCategoryNatIso
      ((Functor.whiskeringRight ℕᵒᵖ _ _).mapIso (compositionUnitOrdinary l E W)) ≪≫
    Functor.mapDerivedCategoryIdIso _

/-- The completed tensor multiplication unit with the recorded adjunction normalization.
Source: Stacks 07A6; auxiliary proof Steps 6 and 9
(blueprint: lem-pur-compact-support-strict-scalar-identity-units). -/
def compositionUnitCompleted (W : Scheme.{u}) :
    pbcDerivedExtend (completedCoefficientMap l E E (AlgHom.id ℚ_[l] E) W) ≅ 𝟭 _ :=
  eqToIso (congrArg (fun a ↦ pbcDerivedExtend a)
      (PurCompactSupport.completedMap_identity l E W)) ≪≫
    PurCompactSupport.tensorIdentity ((PurCompactSupport.completed l E).ring W)

/-- Arithmetic selection by one is the identity on the ordinary strict tower category.
Source: auxiliary proof Step 6
(blueprint: lem-pur-compact-support-strict-scalar-identity-units).
Proof: n+1-1=n on objects; the order-category arrow and composite transitions agree. -/
theorem compositionSelectionOneOrdinary (W : Scheme.{u}) :
    ordinarySubsequence l E W 1 = 𝟭 _ := by
  have hi : CategoryTheory.StrictTowerArithmetic.index 1 = 𝟭 ℕᵒᵖ := by
    apply CategoryTheory.Functor.ext
    · intro a b f
      apply Subsingleton.elim
    · intro n
      cases n
      simp [CategoryTheory.StrictTowerArithmetic.index]
  change CategoryTheory.StrictTowerArithmetic.restriction _ 1 = _
  simp only [CategoryTheory.StrictTowerArithmetic.restriction, hi]
  rfl

/-- The canonical identity selection comparison on derived strict towers.
Source: Stacks 0940; auxiliary proof Step 6
(blueprint: lem-pur-compact-support-strict-scalar-identity-units). -/
def compositionSelectionOne (W : Scheme.{u}) : subsequence l E W 1 ≅ 𝟭 _ :=
  Functor.mapDerivedCategoryNatIso (eqToIso (compositionSelectionOneOrdinary l E W)) ≪≫
    Functor.mapDerivedCategoryIdIso _

/-- Identity inclusion has ramification one, without an extra hypothesis.
Source: auxiliary proof Step 6
(blueprint: lem-pur-compact-support-strict-scalar-identity-units).
Proof: the integral inclusion is the identity, so mapping its uniformizer ideal fixes it. -/
theorem compositionRamificationOne :
    PurCompactSupport.Ramification l E E (AlgHom.id ℚ_[l] E) 1 := by
  have hi : integralScalarIntegerInclusion l E E (AlgHom.id ℚ_[l] E) =
      RingHom.id _ := by
    ext x
    rfl
  change Ideal.map _ _ = _
  rw [hi, Ideal.map_id]

private theorem quotientCast_apply (a b : ℕ) (hab : a = b)
    (x : Padic.coefficientExtensionIntegers l L) :
    (eqToHom (congrArg
      (fun m ↦ CommRingCat.of (ULift.{u + 1} (Padic.coefficientExtensionRing l L m)))
      hab)).hom (ULift.up (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l L a) x)) =
        ULift.up (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l L b) x) := by
  cases hab
  rfl

/-- Finite quotient coefficient squares preserve the composite inclusion.
The final cast is exactly reassociation of h*(e*n) with (h*e)*n.
Source: auxiliary proof Steps 1 and 6
(blueprint: lem-pur-compact-support-strict-scalar-identity-units).
Proof: quotient induction reduces both maps to the same composite integral
inclusion. Associativity of multiplication identifies the target exponent;
constant sheafification preserves the resulting equation, including n=1. -/
theorem compositionFiniteCoefficients (W : Scheme.{u}) (e h : ℕ)
    (he : PurCompactSupport.Ramification l E F i e)
    (hh : PurCompactSupport.Ramification l F L j h) (n : ℕ) (_hn : 1 ≤ n) :
    PurCompactSupport.ramifiedSheafMap l E F i e he n W ≫
        PurCompactSupport.ramifiedSheafMap l F L j h hh (e * n) W ≫
        eqToHom (congrArg
          (fun m ↦ ((constantSheaf (ProEt.topology W) CommRingCat.{u + 1}).obj
            (CommRingCat.of (ULift.{u + 1} (Padic.coefficientExtensionRing l L m)))))
          (Nat.mul_assoc h e n).symm) =
      PurCompactSupport.ramifiedSheafMap l E L (j.comp i) (h * e)
        (compositionRamification l E F i L j e h he hh) n W := by
  unfold PurCompactSupport.ramifiedSheafMap
  rw [← eqToHom_map (constantSheaf (ProEt.topology W) CommRingCat.{u + 1})
    (congrArg (fun m ↦ CommRingCat.of
      (ULift.{u + 1} (Padic.coefficientExtensionRing l L m))) (Nat.mul_assoc h e n).symm)]
  rw [← CategoryTheory.Functor.map_comp_assoc, ← CategoryTheory.Functor.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  rintro ⟨x⟩
  refine Quotient.inductionOn' x ?_
  intro x
  change (eqToHom (congrArg
    (fun m ↦ CommRingCat.of (ULift.{u + 1} (Padic.coefficientExtensionRing l L m)))
      (Nat.mul_assoc h e n).symm)).hom (ULift.up
    (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l L (h * (e * n)))
      (integralScalarIntegerInclusion l F L j (integralScalarIntegerInclusion l E F i x)))) = _
  rw [quotientCast_apply l L _ _ (Nat.mul_assoc h e n).symm]
  rfl

/-- Identity inclusions preserve every positive quotient coefficient map.
Source: auxiliary proof Step 6
(blueprint: lem-pur-compact-support-strict-scalar-identity-units).
Proof: quotient induction makes the map the identity on quotient representatives;
constant sheafification preserves identity maps. -/
theorem identityFiniteCoefficients (W : Scheme.{u}) (n : ℕ) (_hn : 1 ≤ n) :
    PurCompactSupport.ramifiedSheafMap l E E (AlgHom.id ℚ_[l] E) 1
        (compositionRamificationOne l E) n W ≫
        eqToHom (congrArg
          (fun m ↦ ((constantSheaf (ProEt.topology W) CommRingCat.{u + 1}).obj
            (CommRingCat.of (ULift.{u + 1} (Padic.coefficientExtensionRing l E m)))))
          (Nat.one_mul n)) = 𝟙 _ := by
  unfold PurCompactSupport.ramifiedSheafMap
  rw [← eqToHom_map (constantSheaf (ProEt.topology W) CommRingCat.{u + 1})
    (congrArg (fun m ↦ CommRingCat.of
      (ULift.{u + 1} (Padic.coefficientExtensionRing l E m))) (Nat.one_mul n))]
  rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_id]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  rintro ⟨x⟩
  refine Quotient.inductionOn' x ?_
  intro x
  change (eqToHom (congrArg
    (fun m ↦ CommRingCat.of (ULift.{u + 1} (Padic.coefficientExtensionRing l E m)))
      (Nat.one_mul n))).hom (ULift.up
    (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (1 * n))
      (integralScalarIntegerInclusion l E E (AlgHom.id ℚ_[l] E) x))) = _
  rw [quotientCast_apply l E _ _ (Nat.one_mul n)]
  rfl

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

attribute [local irreducible] reductionChange reductionDerivedChange
  pbcScalarAdjunction pbcDerivedScalarAdjunction
  PurCompactSupport.tensorComposition
  PurCompactSupport.tensorIdentity

attribute [local irreducible] HasDerivedCategory.standard
attribute [local irreducible] completedCoefficientMap
  compositionCompleted compositionUnitCompleted
  completedIntegralCommRingSheafUnrestricted

private theorem compositionCompleted_identity_iso (W : Scheme.{u}) :
    compositionCompleted l E E (AlgHom.id ℚ_[l] E) E (AlgHom.id ℚ_[l] E) W =
      Functor.isoWhiskerRight (compositionUnitCompleted l E W)
          (pbcDerivedExtend (completedCoefficientMap l E E (AlgHom.id ℚ_[l] E) W)) ≪≫
        Functor.leftUnitor
          (pbcDerivedExtend (completedCoefficientMap l E E (AlgHom.id ℚ_[l] E) W)) := by
  delta compositionCompleted compositionUnitCompleted
  exact tensorComposition_identity_iso_of_eq (W := W)
    ((PurCompactSupport.completed l E).ring W)
    (completedCoefficientMap l E E (AlgHom.id ℚ_[l] E) W)
    (PurCompactSupport.completedMap_identity l E W)
    (PurCompactSupport.completedMap_composition l E E (AlgHom.id ℚ_[l] E)
      E (AlgHom.id ℚ_[l] E) W)

/-- The completed scalar associator is tensoring its specified unit.
Source: Stacks 07A6 and 0940; strict scalar composition unit calculation.
(blueprint: lem-pur-compact-support-strict-scalar-identity-units).
Proof: Use the normalized adjunction identity-composition equation for the actual completed ring
map. Evaluate
its right-whiskered unit and remove the functor left unitor. -/
theorem compositionCompleted_identity_left (W : Scheme.{u})
    (K : DerivedCategory (scalarReductionSource l E W)) :
    (compositionCompleted l E E (AlgHom.id ℚ_[l] E) E (AlgHom.id ℚ_[l] E) W).hom.app K =
      (pbcDerivedExtend (completedCoefficientMap l E E (AlgHom.id ℚ_[l] E) W)).map
        ((compositionUnitCompleted l E W).hom.app K) := by
  rw [compositionCompleted_identity_iso]
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Functor.leftUnitor_hom_app]
  erw [Category.comp_id]


attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

private theorem compositionOrdinary_identity_left (W : Scheme.{u}) :
    compositionOrdinary l E E (AlgHom.id ℚ_[l] E) E (AlgHom.id ℚ_[l] E) W =
      Functor.isoWhiskerRight (compositionUnitOrdinary l E W)
        (pbcExtend (constantMap l E E (AlgHom.id ℚ_[l] E) W)) := by
  let R := (constants l E).ring W
  have hbase (a : R ⟶ R) (ha : a = 𝟙 R) (hc : a ≫ a = a) :
      (((pbcScalarAdjunction a).comp (pbcScalarAdjunction a)).ofNatIsoRight
        (pbcRestrictComp a a a hc)).leftAdjointUniq (pbcScalarAdjunction a) =
      Functor.isoWhiskerRight
        (eqToIso (congrArg (fun b ↦ pbcExtend b) ha) ≪≫
          ((conjugateIsoEquiv (pbcScalarAdjunction (𝟙 R))
            (Adjunction.id : (𝟭 (pbcModules W R)) ⊣ 𝟭 _)).symm
              (PurCompactSupport.restrictIdentity_existsUnique R).exists.choose).symm)
        (pbcExtend a) := by
    cases ha
    simp only [eqToIso_refl, Iso.refl_trans]
    let ρ := (PurCompactSupport.restrictIdentity_existsUnique R).exists.choose
    have he : pbcRestrictComp (𝟙 R) (𝟙 R) (𝟙 R) hc =
        Functor.isoWhiskerLeft (pbcRestrict (𝟙 R)) ρ := by
      apply Iso.ext
      ext N U x
      exact (pbcRestrictComp_exists (𝟙 R) (𝟙 R) (𝟙 R) hc).exists.choose_spec N U x
        |>.trans ((PurCompactSupport.restrictIdentity_existsUnique R).exists.choose_spec
          N U x).symm
    rw [normalizedComparison_eq]
    have h := Adjunction.leftAdjointCompIso_id_comp (pbcScalarAdjunction (𝟙 R))
      (pbcScalarAdjunction (𝟙 R))
      (pbcRestrictComp (𝟙 R) (𝟙 R) (𝟙 R) hc) ρ (by rw [he]; rfl)
    rw [identityConjugate] at h
    apply Iso.ext
    apply NatTrans.ext
    funext N
    have hh := congrArg (fun z ↦ z.hom.app N) h
    simp only [Iso.trans_hom, NatTrans.comp_app, Functor.leftUnitor_hom_app] at hh
    erw [Category.comp_id] at hh
    exact hh
  exact hbase _ (constantMap_identity l E W) (constantMap_composition l E E
    (AlgHom.id ℚ_[l] E) E (AlgHom.id ℚ_[l] E) W)

/-- The strict tensor associator is tensoring its specified unit.
Source: Stacks 07A6 and 0940; strict scalar composition unit calculation.
(blueprint: lem-pur-compact-support-strict-scalar-identity-units).
Proof: The ordinary restriction compositor is identity on sections. Adjunction uniqueness
identifies its scalar
mate with tensoring the specified unit. Apply this equation degreewise and localize, using
the derived left-unit coherence. -/
theorem compositionTower_identity_left (W : Scheme.{u})
    (K : Derived (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) W) :
    (compositionTower l E E (AlgHom.id ℚ_[l] E) E (AlgHom.id ℚ_[l] E) W).hom.app K =
      (T l E E (AlgHom.id ℚ_[l] E) W).map ((compositionUnitTower l E W).hom.app K) := by
  have := (tensor_exact l E E (AlgHom.id ℚ_[l] E) W).1
  have := (tensor_exact l E E (AlgHom.id ℚ_[l] E) W).2
  have ho : compositionTowerOrdinary l E E (AlgHom.id ℚ_[l] E)
      E (AlgHom.id ℚ_[l] E) W =
        Functor.isoWhiskerRight
          ((Functor.whiskeringRight ℕᵒᵖ _ _).mapIso (compositionUnitOrdinary l E W))
          (tensor l E E (AlgHom.id ℚ_[l] E) W) := by
    apply Iso.ext
    apply NatTrans.ext
    funext N
    apply NatTrans.ext
    funext n
    exact congrArg (fun z ↦ z.hom.app (N.obj n))
      (compositionOrdinary_identity_left l E W)
  simp only [compositionTower, ho]
  exact derived_left_unit _ _ _ K

/-- The retained-level associator at one preserves the selection unit.
Source: Stacks 07A6 and 0940; strict scalar composition unit calculation.
(blueprint: lem-pur-compact-support-strict-scalar-identity-units).
Proof: After substituting the ordinary selection-by-one equality, its compositor and the
right-whiskered unit are
the same equality isomorphism. Localize this equation and use derived left-unit coherence. -/
theorem compositionRetained_identity_left (W : Scheme.{u})
    (K : Derived (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) W) :
    (compositionRetained l E W 1 1 (Nat.le_refl 1) (Nat.le_refl 1)).hom.app K =
      (subsequence l E W 1).map ((compositionSelectionOne l E W).hom.app K) := by
  unfold compositionRetained
  rw [identity_selection_compositor _ (compositionSelectionOneOrdinary l E W)]
  exact derived_left_unit _ _ _ K

/-- The tensor/selection square preserves the selection-by-one unit.
Source: Stacks 07A6 and 0940; strict scalar composition unit calculation.
(blueprint: lem-pur-compact-support-strict-scalar-identity-units).
Proof: The ordinary tensor/selection square is the identity natural isomorphism. Its square with the
selection-by-one equality commutes by equality transport. Exact localization preserves that unit
square; cancel
the inverse comparison to obtain the displayed equation. -/
theorem compositionSelection_identity_unit (W : Scheme.{u})
    (K : Derived (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) W) :
    (compositionSelection l E E (AlgHom.id ℚ_[l] E) W 1).hom.app K ≫
        (compositionSelectionOne l E W).hom.app
          ((T l E E (AlgHom.id ℚ_[l] E) W).obj K) =
      (T l E E (AlgHom.id ℚ_[l] E) W).map
        ((compositionSelectionOne l E W).hom.app K) := by
  have := (tensor_exact l E E (AlgHom.id ℚ_[l] E) W).1
  have := (tensor_exact l E E (AlgHom.id ℚ_[l] E) W).2
  let U := ordinarySubsequence l E W 1
  let V := tensor l E E (AlgHom.id ℚ_[l] E) W
  have h := Functor.mapDerivedCategorySquareIso_hom_app_id
    (Iso.refl _ : V ⋙ U ≅ U ⋙ V)
    (eqToIso (compositionSelectionOneOrdinary l E W))
    (eqToIso (compositionSelectionOneOrdinary l E W))
    (fun N ↦ by
      simp only [Iso.refl_hom, NatTrans.id_app, eqToIso.hom, eqToHom_app,
        eqToHom_map]
      erw [Category.id_comp]) K
  have h' : (compositionSelection l E E (AlgHom.id ℚ_[l] E) W 1).inv.app K ≫
      (T l E E (AlgHom.id ℚ_[l] E) W).map
        ((compositionSelectionOne l E W).hom.app K) =
      (compositionSelectionOne l E W).hom.app
        ((T l E E (AlgHom.id ℚ_[l] E) W).obj K) := by
    simp only [U, V, T, subsequence, ordinarySubsequence,
      compositionSelection, compositionSelectionOne,
      Functor.mapDerivedCategorySquareIso, Iso.trans_hom, Iso.trans_inv,
      Iso.symm_hom, Iso.symm_inv, NatTrans.comp_app,
      localized_iso_refl, Iso.refl_hom, Iso.refl_inv,
      NatTrans.id_app, Category.id_comp, Category.assoc] at h ⊢
    erw [Category.id_comp]
    exact h
  apply (cancel_epi
    ((compositionSelection l E E (AlgHom.id ℚ_[l] E) W 1).inv.app K)).mp
  rw [← Category.assoc, Iso.inv_hom_id_app, Category.id_comp]
  exact h'.symm

end WeilConjectures.PurStrictScalar
