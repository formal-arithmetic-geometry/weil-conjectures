/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.TateTwist.ProEtale
import WeilConjectures.AlgebraicGeometry.Integral.IntegralTateBasis
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.DiagonalFlatScalarEndpoint
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LocallyFreeDualizable
import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalarsMonoidal
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Braided
import Mathlib.CategoryTheory.Shift.Adjunction

/-! # Scalar extension of the actual inverse Tate line

Source: the Tate construction and step 8 of the constant projective-line calculation.
(blueprint: lem-pur-condensed-inverse-tate-scalar-comparison)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
attribute [local irreducible] CategoryTheory.Functor.leftDerivedFunctor
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.CondensedRing

set_option maxHeartbeats 1000000 in
-- Concrete internal module and derived comparison endpoints require large conversions.
/-- Derived scalar extension takes the shifted integral internal dual to the stipulated
negative condensed Tate twist.

Source: current blueprint, sk-def-sp-tate-twist, integral limit and coefficient extension;
step 8 of lem-pur-condensed-p1-constant-decomposition.
(blueprint: lem-pur-condensed-inverse-tate-scalar-comparison).

Proof: the compatible-root cover trivializes the actual integral Tate module, including
its zero level. It is locally free of rank one, hence dualizable. Its internal dual is
therefore flat. Strong monoidal scalar extension preserves a chosen exact dual pairing.
Uniqueness of right adjoints identifies each internal dual with that chosen right dual,
so scalar extension of the internal dual is the internal dual of scalar extension.
The latter positive line is tateTwistOne by definition. The left unitor removes the
initial tensor unit in tateTwistNat 1. The flat single-object scalar comparison and
commutation with shifts give the assertion. No flatness of the coefficient map is
needed for this calculation on a flat source object. -/
theorem exists_condensed_inverse_tate_scalar_comparison
    (ℓ : ℕ) [Fact ℓ.Prime] (S : Scheme.{u}) (hℓ : IsUnit (ℓ : Γ(S, ⊤))) :
    let C := Profinite.continuousMapRingObj.{u} ℤ_[ℓ]
    let M := Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1}) (condensedRingObj C S)
    let F := (Mod.extendScalars
      (coefficientMap (Profinite.padicIntRingObjToPadicAlgCl ℓ) S)).leftDerivedFunctor
    let L := (DerivedCategory.singleFunctor M 0).obj ((ihom (tateModule S ℓ)).obj (𝟙_ M))
    Nonempty (F.obj ((shiftFunctor _ (-2 : ℤ)).obj L) ≅
      (shiftFunctor _ (-2 : ℤ)).obj (tateTwistDerived S ℓ (-1))) := by
  let C := Profinite.continuousMapRingObj.{u} ℤ_[ℓ]
  let M := Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1}) (condensedRingObj C S)
  let T := tateModule S ℓ
  let E := Mod.extendScalars (coefficientMap (Profinite.padicIntRingObjToPadicAlgCl ℓ) S)
  let F := E.leftDerivedFunctor
  have : E.Monoidal := Mod.extendScalarsMonoidal _
  obtain ⟨𝒰, h𝒰⟩ := tateModule_locally_trivial S ℓ hℓ
  have hT : IsLocallyFree (condensedRingObj C S) T := by
    refine ⟨𝒰, fun i ↦ ?_⟩
    obtain ⟨e⟩ := h𝒰 i
    exact ⟨1, ⟨e ≪≫ (biproductUniqueIso (fun _ : Fin 1 ↦ 𝟙_ _)).symm⟩⟩
  let : HasRightDual T := hT.isDualizable.some
  let : ExactPairing (E.obj T) (E.obj Tᘁ) := ExactPairing.map E T Tᘁ
  let : HasRightDual (E.obj T) := ⟨E.obj Tᘁ⟩
  let ed : E.obj ((ihom T).obj (𝟙_ M)) ≅ (ihom (E.obj T)).obj (𝟙_ _) :=
    E.mapIso (ihomUnitIsoRightDual T) ≪≫ (ihomUnitIsoRightDual (E.obj T)).symm
  let en : E.obj ((ihom T).obj (𝟙_ M)) ≅ tateTwist S ℓ (-1) :=
    ed ≪≫ (MonoidalClosed.internalHom.mapIso (λ_ (E.obj T)).op).app (𝟙_ _)
  obtain ⟨i, _, _⟩ := DiagonalCoefficients.diagonal_flat_scalar_endpoint_iso
    (Profinite.padicIntRingObjToPadicAlgCl ℓ) S ((ihom T).obj (𝟙_ M))
      hT.isDualizable.ihom_unit.flat
  let ei : F.obj ((DerivedCategory.singleFunctor M 0).obj ((ihom T).obj (𝟙_ M))) ≅
      tateTwistDerived S ℓ (-1) :=
    i ≪≫ (DerivedCategory.singleFunctor _ 0).mapIso en
  let : F.CommShift ℤ :=
    (Mod.derivedExtendMapDerivedCategoryAdjunction
      (coefficientMap (Profinite.padicIntRingObjToPadicAlgCl ℓ) S)).leftAdjointCommShift ℤ
  exact ⟨(F.commShiftIso (-2 : ℤ)).app _ ≪≫ (shiftFunctor _ (-2 : ℤ)).mapIso ei⟩

end AlgebraicGeometry.ProEtale.CondensedRing
