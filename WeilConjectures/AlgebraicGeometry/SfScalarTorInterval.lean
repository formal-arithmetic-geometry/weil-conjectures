/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.CategoryTheory.DerivedCategory.TorAmplitude
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Defs
public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalarsFlat
import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
/-!
# Scalar extension preserves a fixed Tor interval

Source: current blueprint thm-sf-biduality-class, integral reduction paragraph.
This is the flat-representative tensor argument for the uniform input interval.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale
private local instance (X : Scheme.{u}) : EssentiallySmall.{u + 1} X.ProEt :=
  essentiallySmallSelf.{0, u, u + 1} _
/-- Derived scalar extension preserves the same Tor interval for every coefficient map.
No flatness of the ring map is required.

Source: thm-sf-biduality-class.proof.md, integral reductions and their common input
interval (blueprint: lem-sf-scalar-tor-interval).

Proof: choose a bounded flat representative in the specified interval. Its bounded
flatness makes it K-flat, so the derived extension is its termwise scalar extension.
Scalar extension preserves flat modules and the degrees in which the terms vanish.
The resulting bounded flat complex has the same Tor interval. Transport that
predicate along the derived counit and the chosen representative isomorphism.
This includes an empty interval, zero rings, and empty schemes. -/
theorem sfScalarTorInterval
    (X : Scheme.{u}) {R S : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}}
    [MonObj R] [IsCommMonObj R] [MonObj S] [IsCommMonObj S]
    (φ : R ⟶ S) [IsMonHom φ]
    {K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R)} {a b : ℤ}
    (h : DerivedCategory.torAmplitudeIn _ a b K) :
    DerivedCategory.torAmplitudeIn _ a b ((Mod.extendScalars φ).leftDerivedFunctor.obj K) := by
  obtain ⟨P, hge, hle, hp, ⟨e⟩⟩ := DerivedCategory.exists_iso_Q_obj_flat_of_torAmplitudeIn h
  let F := Mod.extendScalars φ
  have hP := CochainComplex.kFlat_of_bounded_of_flat P a b hp
  have := F.isIso_leftDerivedFunctorCounit_app_of_kFlat P hP
  let i : F.leftDerivedFunctor.obj (DerivedCategory.Q.obj P) ≅
      DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj P) :=
    asIso (F.leftDerivedFunctorCounit.app ((HomotopyCategory.quotient _ (.up ℤ)).obj P))
  apply (DerivedCategory.torAmplitudeIn _ a b).prop_of_iso (i.symm ≪≫
    F.leftDerivedFunctor.mapIso e)
  exact DerivedCategory.torAmplitudeIn_Q_obj_of_flat _ a b
    (fun n ↦ Functor.PreservesFlat.flat_obj (F := F) (hp n))
end AlgebraicGeometry.ProEtale
