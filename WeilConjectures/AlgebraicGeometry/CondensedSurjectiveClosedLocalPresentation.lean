/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import WeilConjectures.AlgebraicGeometry.ProEtaleSurjectiveClosedCoverRefinement
public import WeilConjectures.AlgebraicGeometry.ProEtaleAbelianClosedSupport
public import WeilConjectures.AlgebraicGeometry.LocallyFinitelyPresentedExtendScalars

/-! Local finite presentation under a surjective closed immersion. -/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

private lemma fp_map_family {X Y : Scheme.{u}}
    {R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}}
    {S : Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}} [MonObj R] [MonObj S]
    (F : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R ⥤
      Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) S)
    [F.Additive] [PreservesFiniteColimits F]
    (e : ∀ n : ℕ, F.obj (Mod.finiteFree R n) ≅ Mod.finiteFree S n)
    {M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R}
    (h : Mod.IsFinitelyPresented R M) : Mod.IsFinitelyPresented S (F.obj M) := by
  obtain ⟨n, m, f, ⟨i⟩⟩ := h
  let en := e
  let f' : Mod.finiteFree S m ⟶ Mod.finiteFree S n :=
    (en m).inv ≫ F.map f ≫ (en n).hom
  exact ⟨n, m, f', ⟨F.mapIso i ≪≫ PreservesCokernel.iso F f ≪≫
    cokernel.mapIso (F.map f) f' (en m) (en n) (by simp [f'])⟩⟩

private lemma fp_reflect {X Y : Scheme.{u}}
    {R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}}
    {S : Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}} [MonObj R] [MonObj S]
    (F : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R ⥤
      Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) S)
    [F.Additive] [F.IsEquivalence]
    (e : F.obj (Mod.regular R) ≅ Mod.regular S)
    {M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R}
    (h : Mod.IsFinitelyPresented S (F.obj M)) : Mod.IsFinitelyPresented R M := by
  let E := F.asEquivalence
  have : E.functor.Additive := by change F.Additive; infer_instance
  have : E.inverse.Additive := E.inverse_additive
  let er := E.inverse.mapIso e.symm ≪≫ E.unitIso.symm.app (Mod.regular R)
  let en : ∀ n : ℕ, E.inverse.obj (Mod.finiteFree S n) ≅ Mod.finiteFree R n :=
    fun n ↦ E.inverse.mapBiproduct (fun _ : Fin n ↦ Mod.regular S) ≪≫
      biproduct.mapIso (fun _ ↦ er)
  exact (fp_iff_of_iso (E.unitIso.symm.app M)).1 (fp_map_family E.inverse en h)

attribute [local irreducible] CondensedRing.upperStarComp
  CondensedRing.upperStarLowerStarAdjunction

end AlgebraicGeometry.ProEtale
