/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalarsFlat

/-! # Derived scalar extension preserves a specified Tor interval

Source: Stacks Tags 06YY and 08FZ; the flat-representative step of regular quotient
restriction bounds (blueprint: lem-sf-condensed-scalar-extension-tor-amplitude). -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- Derived extension along a map of condensed coefficients preserves the input
Tor interval. No flatness of the coefficient map is assumed.

Source: Stacks Tags 06YY and 08FZ.
(blueprint: lem-sf-condensed-scalar-extension-tor-amplitude).

Proof: choose a flat complex P in the input interval representing K. It is K-flat,
so applying ordinary extension to P computes derived extension of K. Extension
preserves flat terms and zero terms. The extended P is therefore a flat model in
exactly the same interval, which proves the target Tor-amplitude condition. -/
theorem torAmplitudeIn_scalarExtension
    {Λ Γ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] [MonObj Γ] [IsCommMonObj Γ]
    (φ : Λ ⟶ Γ) [IsMonHom φ] (T : Scheme.{u})
    {a b : ℤ}
    {K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
      (condensedRingObj Λ T))}
    (hK : _root_.DerivedCategory.torAmplitudeIn _ a b K) :
    _root_.DerivedCategory.torAmplitudeIn _ a b
      ((Mod.extendScalars (coefficientMap φ T)).leftDerivedFunctor.obj K) := by
  let F := Mod.extendScalars (coefficientMap φ T)
  obtain ⟨P, hPa, hPb, hP, ⟨e⟩⟩ :=
    (_root_.DerivedCategory.torAmplitudeIn_iff_exists_iso_Q_obj_flat a b K).mp hK
  let := hPa
  let := hPb
  have hPk := CochainComplex.kFlat_of_isStrictlyLE_of_flat P b hP
  have : IsIso (F.leftDerivedFunctorCounit.app
      ((HomotopyCategory.quotient _ _).obj P)) :=
    F.isIso_leftDerivedFunctorCounit_app_of_kFlat P hPk
  let q := _root_.DerivedCategory.quotientCompQhIso
    (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ T))
  let q' := _root_.DerivedCategory.quotientCompQhIso
    (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Γ T))
  let e' :=
    F.leftDerivedFunctor.mapIso ((q.app P).symm ≪≫ e).symm ≪≫
      asIso (F.leftDerivedFunctorCounit.app ((HomotopyCategory.quotient _ _).obj P)) ≪≫
      q'.app ((F.mapHomologicalComplex (.up ℤ)).obj P)
  apply (_root_.DerivedCategory.torAmplitudeIn_iff_exists_iso_Q_obj_flat a b _).mpr
  exact ⟨(F.mapHomologicalComplex (.up ℤ)).obj P, inferInstance, inferInstance,
    fun i ↦ Functor.PreservesFlat.flat_obj (F := F) (hP i), ⟨e'.symm⟩⟩

end AlgebraicGeometry.ProEtale.CondensedRing
