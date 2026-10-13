/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F3
-/
module

public import Sheaf.AlgebraicGeometry.Coherent
public import Sheaf.AlgebraicGeometry.IdealModuleProductStalk
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

/-! # The canonical annihilator of an ideal power

Source: Stacks Project, Properties, Tags 01PO and 01PQ.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

namespace AlgebraicGeometry.Scheme

/-- Sections locally annihilated by a module inclusion into the structure sheaf. -/
def idealAnnihilatorSections {X : Scheme.{u}} {P : X.Modules}
    (j : P ⟶ SheafOfModules.unit X.ringCatSheaf) (F : X.Modules)
    (W : X.Opens) : Submodule Γ(X, W) Γ(F, W) where
  carrier := {s | ∀ (V : X.Opens) (h : V ≤ W) (b : Γ(P, V)),
    (show Γ(X, V) from j.app V b) • F.presheaf.map (homOfLE h).op s = 0}
  zero_mem' := by simp
  add_mem' := by
    intro s t hs ht V h b
    simp only [map_add, smul_add, hs V h b, ht V h b, add_zero]
  smul_mem' := by
    intro r s hs V h b
    rw [F.map_smul, smul_comm, hs V h b, smul_zero]

/-- The local annihilation condition is stable under restriction. -/
def idealAnnihilatorPresheaf {X : Scheme.{u}} {P : X.Modules}
    (j : P ⟶ SheafOfModules.unit X.ringCatSheaf) (F : X.Modules) : F.val.Submodule where
  obj W := idealAnnihilatorSections j F W.unop
  map {W V} f := by
    intro s hs
    change ∀ (T : X.Opens) (h : T ≤ V.unop) (b : Γ(P, T)),
      (show Γ(X, T) from j.app T b) •
        F.presheaf.map (homOfLE h).op (F.presheaf.map f s) = 0
    intro T h b
    have hh := hs T (h.trans f.unop.le) b
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
    convert hh using 1
    congr 2

theorem idealAnnihilatorPresheaf_isSheaf {X : Scheme.{u}} {P : X.Modules}
    (j : P ⟶ SheafOfModules.unit X.ringCatSheaf) (F : X.Modules) :
    Presheaf.IsSheaf (Opens.grothendieckTopology X)
      (idealAnnihilatorPresheaf j F).toPresheafOfModules.presheaf := by
  apply (TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing _).mpr
  intro T W sf hsf
  let A : TopCat.Sheaf Ab X := ⟨F.presheaf, F.isSheaf⟩
  have hcompat : TopCat.Presheaf.IsCompatible F.presheaf W (fun i ↦ (sf i).val) := by
    intro i k
    exact congrArg Subtype.val (hsf i k)
  obtain ⟨s, hs, huniq⟩ := A.existsUnique_gluing W (fun i ↦ (sf i).val) hcompat
  change ∀ i, F.presheaf.map (Opens.leSupr W i).op s = (sf i).val at hs
  have hmem : s ∈ idealAnnihilatorSections j F (iSup W) := by
    intro V hV b
    apply A.eq_of_locally_eq' (fun i ↦ V ⊓ W i) V
      (fun i ↦ homOfLE inf_le_left) (by
        intro x hx
        obtain ⟨i, hi⟩ := Opens.mem_iSup.mp (hV hx)
        exact Opens.mem_iSup.mpr ⟨i, hx, hi⟩) _ 0
    intro i
    rw [map_zero, F.map_smul]
    have hh := (sf i).property (V ⊓ W i) inf_le_right
      (P.presheaf.map (homOfLE inf_le_left).op b)
    have hj : X.presheaf.map (homOfLE inf_le_left : V ⊓ W i ⟶ V).op
        (j.app V b) = j.app (V ⊓ W i) (P.presheaf.map (homOfLE inf_le_left).op b) := by
      exact (ConcreteCategory.congr_hom
        (j.mapPresheaf.naturality (homOfLE inf_le_left).op) b).symm
    have heq : F.presheaf.map (homOfLE inf_le_left : V ⊓ W i ⟶ V).op
        (F.presheaf.map (homOfLE hV).op s) =
        F.presheaf.map (homOfLE inf_le_right : V ⊓ W i ⟶ W i).op (sf i).val := by
      rw [← hs i]
      simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp]
      rfl
    rw [hj, heq]
    exact hh
  refine ⟨⟨s, hmem⟩, ?_, ?_⟩
  · intro i
    apply Subtype.ext
    exact hs i
  · intro t ht
    apply Subtype.ext
    apply huniq t.val
    intro i
    exact congrArg Subtype.val (ht i)

/-- The actual subsheaf of sections annihilated locally by the ideal inclusion. -/
noncomputable def idealAnnihilator {X : Scheme.{u}} {P : X.Modules}
    (j : P ⟶ SheafOfModules.unit X.ringCatSheaf) (F : X.Modules) : X.Modules :=
  ⟨(idealAnnihilatorPresheaf j F).toPresheafOfModules,
    idealAnnihilatorPresheaf_isSheaf j F⟩

/-- The inclusion of the canonical annihilator subsheaf. -/
noncomputable def idealAnnihilatorι {X : Scheme.{u}} {P : X.Modules}
    (j : P ⟶ SheafOfModules.unit X.ringCatSheaf) (F : X.Modules) :
    idealAnnihilator j F ⟶ F :=
  ⟨(idealAnnihilatorPresheaf j F).ι⟩

instance {X : Scheme.{u}} {P : X.Modules}
    (j : P ⟶ SheafOfModules.unit X.ringCatSheaf) (F : X.Modules) :
    Mono (idealAnnihilatorι j F) :=
  (Modules.toPresheafOfModules X).mono_of_mono_map (by
    change Mono (idealAnnihilatorPresheaf j F).ι
    infer_instance)

/-- The annihilator of each power of a finite-type quasi-coherent ideal is quasi-coherent.

Source: Stacks Project, Properties, Tag 01PO, proof of (1), applied to the powers
in the proof of Tag 01PQ.
(blueprint: lem-weil-pbc-ideal-power-annihilator-quasicoherent).

Proof: On an affine open Spec R identify I with a finitely generated ideal J and
F with the sheaf associated to an R-module M. The recursive image construction
of ideal powers gives J^n, which is finitely generated, including J^0 = R.
The canonical subsheaf has sections killed by J^n: annihilation on the affine
open implies annihilation on every smaller affine open by localization, and
these smaller affines cover any open. Put N = {m in M | J^n m = 0}. For a
principal open D(f), localization of N injects into M_f. If m/f^r is killed
by (J^n)_f, choose finite generators of J^n and clear a power of f in each
annihilation equation. Their maximum e gives f^e m in N, showing that
m/f^r belongs to N_f. With no generators, take e = 0. Thus the canonical
annihilator is the sheaf associated to N on every affine open; the inclusions
into F make these local identifications compatible. It is quasi-coherent.
-/
theorem ideal_power_annihilator_quasicoherent {X : Scheme.{u}} {I : X.Modules}
    (ι : I ⟶ SheafOfModules.unit X.ringCatSheaf) [Mono ι]
    [I.IsQuasicoherent] [I.IsFiniteType] (F : X.Modules) [F.IsQuasicoherent]
    (n : ℕ) : (idealAnnihilator (idealSheafPower ι n).2 F).IsQuasicoherent := by sorry

end AlgebraicGeometry.Scheme
