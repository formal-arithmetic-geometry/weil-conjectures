/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinaryEncodingSupplement
public import WeilConjectures.SixFunctors.ScalarSixDefinitions
public import WeilConjectures.AlgebraicGeometry.WitnessCompatibility
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
def scalarHeartPresentation {T : Scheme.{u}} (E : Encoding A T) :
    E.ordinary.functor ⋙ E.fixed.functor ≅
      sectionEncoding A T E.ringIso ⋙ fixedRestriction A T :=
  eqToIso (congrArg₂ Functor.comp E.ordinary_functor E.fixed_functor)

/-- Scalar coordinates consist of the restriction comparison, required to act as the
identity on every additive section. This normalization excludes arbitrary scalar twists.
Source: finite-stage coefficient identification, current blueprint first paragraph
(blueprint: def-sf-finite-condensed-scalar-coordinates). -/
structure FiniteCondensedScalarCoordinates
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
          ((scalarHeartPresentation EB).hom.app N)).hom.app U
      ((restriction.hom.app N).hom.app U
        (((scalarHeartPresentation EA).inv.app
          ((Mod.comap (coefficientMap (Λ := coefficient A) (Λ' := coefficient B)
            a.hom.hom T)).obj N)).hom.app U x))) = x

/-- The restriction comparison descended through the actual exact termwise functors.
Source: the coefficient identification in the cited blueprint paragraph
(blueprint: def-sf-finite-condensed-scalar-coordinates). -/
def FiniteCondensedScalarCoordinates.derivedRestriction
    {φ : A →+* B}
    {a : (⟨coefficient A⟩ : CondensedRing.ScalarSixRing.{u}) ⟶ ⟨coefficient B⟩}
    {T : Scheme.{u}} {EA : Encoding A T} {EB : Encoding B T}
    (s : FiniteCondensedScalarCoordinates φ a T EA EB) :
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
def FiniteCondensedScalarCoordinates.extension
    {φ : A →+* B}
    {a : (⟨coefficient A⟩ : CondensedRing.ScalarSixRing.{u}) ⟶ ⟨coefficient B⟩}
    {T : Scheme.{u}} {EA : Encoding A T} {EB : Encoding B T}
    (s : FiniteCondensedScalarCoordinates φ a T EA EB) :
    CondensedRing.scalarSixChange a T ⋙ EB.fixedDerived.functor ≅
      EA.fixedDerived.functor ⋙ pbcFixedScalarExtension
        (Scheme.ProEt.topology T) (RingHom.ulift.{u + 1, u + 1} φ) := by
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
    ((EA.fixedDerived.toAdjunction.comp (Adjunction.ofIsRightAdjoint W)).ofNatIsoRight r.symm)

end AlgebraicGeometry.ProEtale.FiniteDiscreteOrdinary
