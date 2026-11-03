/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteDiscreteOrdinaryEncodingSupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixDefinitions
public import WeilConjectures.AlgebraicGeometry.CoefficientScalarRepresentatives.CoefficientScalarRepresentatives
public import WeilConjectures.CategoryTheory.ConstantScalarRealization.ConstantRealizationDerivedScalarExtensionSupplement
public import Mathlib.CategoryTheory.Adjunction.Unique

/-! # Normalized finite condensed scalar coordinates

Source: current blueprint, prop-coef-integral-dualizing.proof.md, first paragraph;
the explicit scalar-identification step of lem-coef-finite-dualizing-condensed-agreement.
(blueprint: def-sf-finite-condensed-scalar-coordinates).

Restriction is normalized by the identity on additive sections. Its adjoint comparison
therefore specifies scalar extension, including its units and counits.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.FiniteDiscreteOrdinary

variable {A B : Type u} [CommRing A] [CommRing B]
  [TopologicalSpace A] [IsTopologicalRing A]
  [TopologicalSpace B] [IsTopologicalRing B]

/-- The stipulated section-action presentation of an encoding.
Source: the coefficient identification in the cited blueprint paragraph
(blueprint: def-sf-finite-condensed-scalar-coordinates). -/
def finiteInputHeartPresentation {T : Scheme.{u}} (E : Encoding A T) :
    E.ordinary.functor ⋙ E.fixed.functor ≅
      sectionEncoding A T E.ringIso ⋙ fixedRestriction A T :=
  eqToIso (congrArg₂ Functor.comp E.ordinary_functor E.fixed_functor)

/-- The exact fixed-scalar equivalence on derived constant-ring modules.
Source: Stacks 03CY and 015F (blueprint: def-sf-finite-condensed-scalar-coordinates). -/
def scalarFixedDerived {R : Type u} [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] {T : Scheme.{u}} (E : Encoding R T) :
    DerivedCategory (Ordinary R T) ≌
      DerivedCategory (Sheaf (Scheme.ProEt.topology T)
        (ModuleCat.{u + 1} (ULift.{u + 1} R))) :=
  letI := HasDerivedCategory.standard (Ordinary R T)
  E.fixed.mapDerivedCategory

/-- Insert the encoding's stipulated fixed section-action presentation.
Source: Stacks 03CY (blueprint: def-sf-finite-condensed-scalar-coordinates). -/
def fixedFunctorPresentation {R : Type u} [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] {T : Scheme.{u}} (E : Encoding R T) :
    E.fixed.functor ≅ fixedRestriction R T :=
  eqToIso E.fixed_functor

/-- Restriction to constant scalars is the action of the commutative-ring unit.
Source: Stacks 03CY (blueprint: def-sf-finite-condensed-scalar-coordinates). -/
private theorem fixedRestriction_smul {R : Type u} [CommRing R]
    [TopologicalSpace R] [IsTopologicalRing R] (T : Scheme.{u})
    (M : Ordinary R T) (U : T.ProEtᵒᵖ) (r : ULift.{u + 1} R) (x : M.val.obj U) :
    r • (show ((fixedRestriction R T).obj M).obj.obj U from x) =
      (realizationRingUnit (Scheme.ProEt.topology T) (ULift.{u + 1} R)).app U r • x := by
  let J := Scheme.ProEt.topology T
  have h : realizationRingUnit J (ULift.{u + 1} R) ≫
      (realizationRingIso J (ULift.{u + 1} R)).hom.hom =
        toSheafify J ((Functor.const T.ProEtᵒᵖ).obj
          (RingCat.of (ULift.{u + 1} R))) := by
    dsimp only [realizationRingIso, Iso.app_hom]
    rw [constantCommuteCompose_hom_app_hom]
    unfold realizationRingUnit
    rw [← Category.assoc, sheafComposeIso_inv_fac]
    exact (toSheafify_naturality J
      (Functor.constComp T.ProEtᵒᵖ (CommRingCat.of (ULift.{u + 1} R))
        (forget₂ CommRingCat RingCat)).hom).symm.trans (by rfl)
  have hi := congrArg (fun f ↦ f.hom.app U)
    (realizationRingIso J (ULift.{u + 1} R)).hom_inv_id
  change (realizationRingIso J (ULift.{u + 1} R)).inv.hom.app U
    ((toSheafify J ((Functor.const T.ProEtᵒᵖ).obj
      (RingCat.of (ULift.{u + 1} R)))).app U r) • x = _
  erw [← congrArg (fun f ↦ f.app U r) h]
  exact congrArg (fun a ↦ a • x) (ConcreteCategory.congr_hom hi _)

/-- Naturality of the constant-ring unit identifies the two restricted scalar actions.
Source: Stacks 03CY (blueprint: def-sf-finite-condensed-scalar-coordinates). -/
private theorem fixedRestriction_coefficient_smul (φ : A →+* B) (T : Scheme.{u})
    (M : Ordinary B T) (U : T.ProEtᵒᵖ) (r : ULift.{u + 1} A) (x : M.val.obj U) :
    r • (show ((fixedRestriction A T).obj
      ((CategoryTheory.ConstantScalarRealization.restriction
        (Scheme.ProEt.topology T) (RingHom.ulift.{u + 1, u + 1} φ)).obj M)).obj.obj U
          from x) =
      (RingHom.ulift.{u + 1, u + 1} φ) r •
        (show ((fixedRestriction B T).obj M).obj.obj U from x) := by
  let J := Scheme.ProEt.topology T
  trans (realizationRingUnit J (ULift.{u + 1} A)).app U r •
    (show ((CategoryTheory.ConstantScalarRealization.restriction J
      (RingHom.ulift.{u + 1, u + 1} φ)).obj M).val.obj U from x)
  · exact fixedRestriction_smul T
      ((CategoryTheory.ConstantScalarRealization.restriction J
        (RingHom.ulift.{u + 1, u + 1} φ)).obj M) U r x
  · trans (realizationRingUnit J (ULift.{u + 1} B)).app U
      ((RingHom.ulift.{u + 1, u + 1} φ) r) • x
    · have h := toSheafify_naturality (D := CommRingCat.{u + 1}) J
        ((Functor.const T.ProEtᵒᵖ).map
          (CommRingCat.ofHom (RingHom.ulift.{u + 1, u + 1} φ)))
      exact congrArg (fun a ↦ a • x)
        (congrArg (fun f ↦ f.app U r)
          (congrArg (fun f ↦ Functor.whiskerRight f
            (forget₂ CommRingCat RingCat)) h)).symm
    · exact (fixedRestriction_smul T M U _ x).symm

/-- The identity on sections is linear for both composite scalar restrictions.
Source: Stacks 03CY (blueprint: def-sf-finite-condensed-scalar-coordinates). -/
private def fixedRestrictionCoefficientIso (φ : A →+* B) (T : Scheme.{u}) :
    CategoryTheory.ConstantScalarRealization.restriction
        (Scheme.ProEt.topology T) (RingHom.ulift.{u + 1, u + 1} φ) ⋙ fixedRestriction A T ≅
      fixedRestriction B T ⋙ Sheaf.restrictScalars (Scheme.ProEt.topology T)
        (RingHom.ulift.{u + 1, u + 1} φ) := by
  refine NatIso.ofComponents (fun M ↦ ?_) ?_
  · apply ObjectProperty.isoMk
    refine NatIso.ofComponents (fun U ↦ ?_) ?_
    · exact
        { hom := ConcreteCategory.ofHom (C := ModuleCat.{u + 1} (ULift.{u + 1} A))
            { toFun := id
              map_add' := by intros; rfl
              map_smul' := by intros; exact fixedRestriction_coefficient_smul φ T M U _ _ }
          inv := ConcreteCategory.ofHom (C := ModuleCat.{u + 1} (ULift.{u + 1} A))
            { toFun := id
              map_add' := by intros; rfl
              map_smul' := by
                intros; exact (fixedRestriction_coefficient_smul φ T M U _ _).symm }
          hom_inv_id := by ext x; rfl
          inv_hom_id := by ext x; rfl }
    · intros; ext x; rfl
  · intros; apply Sheaf.hom_ext; ext U x; rfl

/-- The fixed-scalar restrictions commute by the unique identity-on-sections map.
Source: Stacks 03CY and the constant-ring scalar-restriction construction
(blueprint: def-sf-finite-condensed-scalar-coordinates).
Proof: insert the stipulated equalities of the fixed functors with fixedRestriction.
Restriction along the constant coefficient homomorphism and then along the constant
sheafification unit is restriction along their composite. Naturality of that unit
identifies this composite with restriction along φ followed by the target unit.
The identity on each additive section is therefore linear and natural. Its inverse
is the same identity, and its sectionwise characterization determines it uniquely. -/
theorem scalarFixedRestriction_existsUnique
    (φ : A →+* B) {T : Scheme.{u}} (EA : Encoding A T) (EB : Encoding B T) :
    ∃! e : CategoryTheory.ConstantScalarRealization.restriction
          (Scheme.ProEt.topology T) (RingHom.ulift.{u + 1, u + 1} φ) ⋙ EA.fixed.functor ≅
        EB.fixed.functor ⋙ Sheaf.restrictScalars (Scheme.ProEt.topology T)
          (RingHom.ulift.{u + 1, u + 1} φ),
      ∀ (M : Ordinary B T) (U : T.ProEtᵒᵖ) (x : M.val.obj U),
        (((Sheaf.restrictScalars (Scheme.ProEt.topology T)
            (RingHom.ulift.{u + 1, u + 1} φ)).map
              ((fixedFunctorPresentation EB).hom.app M)).hom.app U
          ((e.hom.app M).hom.app U
            (((fixedFunctorPresentation EA).inv.app
              ((CategoryTheory.ConstantScalarRealization.restriction
                (Scheme.ProEt.topology T) (RingHom.ulift.{u + 1, u + 1} φ)).obj M)).hom.app
                  U x))) = x := by
  let V := CategoryTheory.ConstantScalarRealization.restriction
    (Scheme.ProEt.topology T) (RingHom.ulift.{u + 1, u + 1} φ)
  let W := Sheaf.restrictScalars (Scheme.ProEt.topology T)
    (RingHom.ulift.{u + 1, u + 1} φ)
  let e := Functor.isoWhiskerLeft V (fixedFunctorPresentation EA) ≪≫
    fixedRestrictionCoefficientIso φ T ≪≫
      Functor.isoWhiskerRight (fixedFunctorPresentation EB).symm W
  refine ⟨e, ?_, ?_⟩
  · intro M U x
    change (((fixedFunctorPresentation EB).hom.app M).hom.app U)
      ((((fixedFunctorPresentation EB).inv.app M).hom.app U)
        ((((fixedFunctorPresentation EA).hom.app (V.obj M)).hom.app U)
          ((((fixedFunctorPresentation EA).inv.app (V.obj M)).hom.app U) x))) = x
    have hA := congrArg (fun f ↦ f.hom.app U x)
      ((fixedFunctorPresentation EA).app (V.obj M)).inv_hom_id
    have hB := congrArg (fun f ↦ f.hom.app U x)
      ((fixedFunctorPresentation EB).app M).inv_hom_id
    change ((fixedFunctorPresentation EA).hom.app (V.obj M)).hom.app U
      (((fixedFunctorPresentation EA).inv.app (V.obj M)).hom.app U x) = x at hA
    change ((fixedFunctorPresentation EB).hom.app M).hom.app U
      (((fixedFunctorPresentation EB).inv.app M).hom.app U x) = x at hB
    erw [hA]
    exact hB
  · intro d hd
    apply Iso.ext
    apply NatTrans.ext
    funext M
    apply Sheaf.hom_ext
    ext U x
    have h := hd M U
      (((fixedFunctorPresentation EA).hom.app (V.obj M)).hom.app U x)
    have hA := congrArg (fun f ↦ f.hom.app U x)
      ((fixedFunctorPresentation EA).app (V.obj M)).hom_inv_id
    change ((fixedFunctorPresentation EA).inv.app (V.obj M)).hom.app U
      (((fixedFunctorPresentation EA).hom.app (V.obj M)).hom.app U x) = x at hA
    change (((fixedFunctorPresentation EB).hom.app M).hom.app U)
      (((d.hom.app M).hom.app U)
        ((((fixedFunctorPresentation EA).inv.app (V.obj M)).hom.app U)
          ((((fixedFunctorPresentation EA).hom.app (V.obj M)).hom.app U) x))) = _ at h
    erw [hA] at h
    have h' := congrArg
      (fun y ↦ ((fixedFunctorPresentation EB).inv.app M).hom.app U y) h
    have hB := congrArg (fun f ↦ f.hom.app U ((d.hom.app M).hom.app U x))
      ((fixedFunctorPresentation EB).app M).hom_inv_id
    change ((fixedFunctorPresentation EB).inv.app M).hom.app U
      (((fixedFunctorPresentation EB).hom.app M).hom.app U
        ((d.hom.app M).hom.app U x)) = (d.hom.app M).hom.app U x at hB
    erw [hB] at h'
    exact h'

/-- The specified restriction comparison, determined uniquely by its action on sections.
Source: Stacks 03CY (blueprint: def-sf-finite-condensed-scalar-coordinates). -/
def scalarFixedRestriction
    (φ : A →+* B) {T : Scheme.{u}} (EA : Encoding A T) (EB : Encoding B T) :=
  (scalarFixedRestriction_existsUnique φ EA EB).choose

/-- Termwise localization of the identity-on-sections fixed restriction comparison.
Source: Stacks 015F (blueprint: def-sf-finite-condensed-scalar-coordinates). -/
def scalarFixedDerivedRestriction
    (φ : A →+* B) {T : Scheme.{u}} (EA : Encoding A T) (EB : Encoding B T) :
    CategoryTheory.ConstantScalarRealization.derivedRestriction
        (Scheme.ProEt.topology T) (RingHom.ulift.{u + 1, u + 1} φ) ⋙
          (scalarFixedDerived EA).functor ≅
      (scalarFixedDerived EB).functor ⋙ Sheaf.derivedRestrictScalars
        (Scheme.ProEt.topology T) (RingHom.ulift.{u + 1, u + 1} φ) :=
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso (scalarFixedRestriction φ EA EB) ≪≫
      Functor.mapDerivedCategoryCompIso _ _

/-- The fixed-scalar derived tensor is the actual ring-sheaf derived tensor transported
through G_A and G_B, as stipulated in the current definition node.
Source: Stacks 06YY (blueprint: def-sf-finite-condensed-scalar-coordinates). -/
def scalarFixedTensor
    (φ : A →+* B) {T : Scheme.{u}} (EA : Encoding A T) (EB : Encoding B T) :=
  letI := HasDerivedCategory.standard (Ordinary A T)
  letI := HasDerivedCategory.standard (Ordinary B T)
  ((scalarFixedDerived EA).inverse ⋙
    CategoryTheory.ConstantScalarRealization.derivedExtension
      (Scheme.ProEt.topology T) (RingHom.ulift.{u + 1, u + 1} φ)) ⋙
        (scalarFixedDerived EB).functor

/-- The transported ring-sheaf adjunction has actual fixed-scalar restriction on the right.
Source: Stacks 06YY (blueprint: def-sf-finite-condensed-scalar-coordinates). -/
def scalarFixedTensorAdjunction
    (φ : A →+* B) {T : Scheme.{u}} (EA : Encoding A T) (EB : Encoding B T) :
    scalarFixedTensor φ EA EB ⊣ Sheaf.derivedRestrictScalars
      (Scheme.ProEt.topology T) (RingHom.ulift.{u + 1, u + 1} φ) :=
  letI := HasDerivedCategory.standard (Ordinary A T)
  letI := HasDerivedCategory.standard (Ordinary B T)
  let GA := scalarFixedDerived EA
  let GB := scalarFixedDerived EB
  let V := CategoryTheory.ConstantScalarRealization.derivedRestriction
    (Scheme.ProEt.topology T) (RingHom.ulift.{u + 1, u + 1} φ)
  let W := Sheaf.derivedRestrictScalars
    (Scheme.ProEt.topology T) (RingHom.ulift.{u + 1, u + 1} φ)
  let k : GB.inverse ⋙ V ⋙ GA.functor ≅ W :=
    Functor.isoWhiskerLeft GB.inverse (scalarFixedDerivedRestriction φ EA EB) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight GB.counitIso W ≪≫ Functor.leftUnitor W
  ((GA.symm.toAdjunction.comp
    (CategoryTheory.ConstantScalarRealization.derivedAdjunction
      (Scheme.ProEt.topology T) (RingHom.ulift.{u + 1, u + 1} φ))).comp
        GB.toAdjunction).ofNatIsoRight k

/-- The unique unit-preserving identification with the chosen fixed restriction adjoint.
Source: Stacks 06YY (blueprint: def-sf-finite-condensed-scalar-coordinates). -/
def scalarFixedTensorIso
    (φ : A →+* B) {T : Scheme.{u}} (EA : Encoding A T) (EB : Encoding B T) :
    scalarFixedTensor φ EA EB ≅ CoefficientScalarRepresentatives.extension
      (Scheme.ProEt.topology T) (RingHom.ulift.{u + 1, u + 1} φ) :=
  (scalarFixedTensorAdjunction φ EA EB).leftAdjointUniq
    (CoefficientScalarRepresentatives.adjunction
      (Scheme.ProEt.topology T) (RingHom.ulift.{u + 1, u + 1} φ))

/-- Scalar coordinates consist of the restriction comparison, required to act as the
identity on every additive section. This normalization excludes arbitrary scalar twists.
Source: finite-stage coefficient identification, current blueprint first paragraph
(blueprint: def-sf-finite-condensed-scalar-coordinates). -/
structure FiniteInputScalarCoordinates
    (φ : A →+* B)
    (a : (⟨coefficient A⟩ : CondensedRing.ScalarSixRing.{u}) ⟶ ⟨coefficient B⟩)
    (T : Scheme.{u}) (EA : Encoding A T) (EB : Encoding B T) where
  restriction :
    Mod.comap (coefficientMap (Λ := coefficient A) (Λ' := coefficient B) a.hom.hom T) ⋙
        (EA.ordinary.functor ⋙ EA.fixed.functor) ≅
      (EB.ordinary.functor ⋙ EB.fixed.functor) ⋙
        Sheaf.restrictScalars (Scheme.ProEt.topology T) (RingHom.ulift.{u + 1, u + 1} φ)
  normalized : ∀ (N : Internal B T) (U : T.ProEtᵒᵖ) (x : N.X.obj.obj U),
    (((Sheaf.restrictScalars (Scheme.ProEt.topology T)
        (RingHom.ulift.{u + 1, u + 1} φ)).map
          ((finiteInputHeartPresentation EB).hom.app N)).hom.app U
      ((restriction.hom.app N).hom.app U
        (((finiteInputHeartPresentation EA).inv.app
          ((Mod.comap (coefficientMap (Λ := coefficient A) (Λ' := coefficient B)
            a.hom.hom T)).obj N)).hom.app U x))) = x

/-- The restriction comparison descended through the actual exact termwise functors.
Source: the coefficient identification in the cited blueprint paragraph
(blueprint: def-sf-finite-condensed-scalar-coordinates). -/
def FiniteInputScalarCoordinates.derivedRestriction
    {φ : A →+* B}
    {a : (⟨coefficient A⟩ : CondensedRing.ScalarSixRing.{u}) ⟶ ⟨coefficient B⟩}
    {T : Scheme.{u}} {EA : Encoding A T} {EB : Encoding B T}
    (s : FiniteInputScalarCoordinates φ a T EA EB) :
    (Mod.comap (coefficientMap (Λ := coefficient A) (Λ' := coefficient B)
      a.hom.hom T)).mapDerivedCategory ⋙
        EA.fixedDerived.functor ≅
      EB.fixedDerived.functor ⋙ Sheaf.derivedRestrictScalars (Scheme.ProEt.topology T)
        (RingHom.ulift.{u + 1, u + 1} φ) := by
  letI : (EA.ordinary.trans EA.fixed).functor.Additive :=
    inferInstanceAs (EA.ordinary.functor ⋙ EA.fixed.functor).Additive
  letI : (EB.ordinary.trans EB.fixed).functor.Additive :=
    inferInstanceAs (EB.ordinary.functor ⋙ EB.fixed.functor).Additive
  letI : (EA.ordinary.functor ⋙ EA.fixed.functor).Additive :=
    inferInstanceAs (EA.ordinary.trans EA.fixed).functor.Additive
  letI : (EB.ordinary.functor ⋙ EB.fixed.functor).Additive :=
    inferInstanceAs (EB.ordinary.trans EB.fixed).functor.Additive
  exact (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso s.restriction ≪≫
      Functor.mapDerivedCategoryCompIso _ _

/-- The unique adjoint comparison for scalar extension. It is formed from the normalized
restriction comparison and the two given scalar adjunctions, not an endpoint isomorphism.
Source: the coefficient identification in the cited blueprint paragraph
(blueprint: def-sf-finite-condensed-scalar-coordinates). -/
def FiniteInputScalarCoordinates.extension
    {φ : A →+* B}
    {a : (⟨coefficient A⟩ : CondensedRing.ScalarSixRing.{u}) ⟶ ⟨coefficient B⟩}
    {T : Scheme.{u}} {EA : Encoding A T} {EB : Encoding B T}
    (s : FiniteInputScalarCoordinates φ a T EA EB) :
    CondensedRing.scalarSixChange a T ⋙ EB.fixedDerived.functor ≅
      EA.fixedDerived.functor ⋙ scalarFixedTensor φ EA EB := by
  let V := (Mod.comap (D := Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
    (A := condensedRingObj (coefficient A) T)
    (B := condensedRingObj (coefficient B) T)
    (coefficientMap (Λ := coefficient A) (Λ' := coefficient B) a.hom.hom T)).mapDerivedCategory
  let W := Sheaf.derivedRestrictScalars (Scheme.ProEt.topology T)
    (RingHom.ulift.{u + 1, u + 1} φ)
  let k : (EB.fixedDerived.inverse ⋙ V) ⋙ EA.fixedDerived.functor ≅ W :=
    Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft EB.fixedDerived.inverse s.derivedRestriction ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight EB.fixedDerived.counitIso W ≪≫ Functor.leftUnitor W
  let r := Iso.isoCompInverse (H := EA.fixedDerived) k
  let adj := (Mod.derivedExtendMapDerivedCategoryAdjunction
    (coefficientMap (Λ := coefficient A) (Λ' := coefficient B) a.hom.hom T)).comp
      EB.fixedDerived.toAdjunction
  exact adj.leftAdjointUniq
    ((EA.fixedDerived.toAdjunction.comp (scalarFixedTensorAdjunction φ EA EB)).ofNatIsoRight r.symm)

/-- The same unit-compatible comparison in the fixed chosen-adjoint coordinates.
Source: Stacks 06YY (blueprint: def-sf-finite-condensed-scalar-coordinates). -/
def FiniteInputScalarCoordinates.fixedExtension
    {φ : A →+* B}
    {a : (⟨coefficient A⟩ : CondensedRing.ScalarSixRing.{u}) ⟶ ⟨coefficient B⟩}
    {T : Scheme.{u}} {EA : Encoding A T} {EB : Encoding B T}
    (s : FiniteInputScalarCoordinates φ a T EA EB) :
    CondensedRing.scalarSixChange a T ⋙ EB.fixedDerived.functor ≅
      EA.fixedDerived.functor ⋙ CoefficientScalarRepresentatives.extension
        (Scheme.ProEt.topology T) (RingHom.ulift.{u + 1, u + 1} φ) :=
  s.extension ≪≫ Functor.isoWhiskerLeft EA.fixedDerived.functor
    (scalarFixedTensorIso φ EA EB)

end AlgebraicGeometry.ProEtale.FiniteDiscreteOrdinary
