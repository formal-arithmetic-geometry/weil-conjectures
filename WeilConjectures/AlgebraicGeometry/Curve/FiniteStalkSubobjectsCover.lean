/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import WeilConjectures.AlgebraicGeometry.Sites.EtaleTorsion
import WeilConjectures.AlgebraicGeometry.EtaleSheafDiscreteContinuousRep
import WeilConjectures.AlgebraicGeometry.Curve.FiniteStalkSubobjectElement

/-!
# Finite-stalk subobjects cover a torsion sheaf over a field

Source: Stacks Project, Tags 04JQ and 03SA.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

/-- Finite-stalk subobjects of a torsion abelian sheaf over a field have supremum top.

Source: Stacks Project, Tag 04JQ (abelian sheaves on a field and discrete Galois
modules) and Tag 03SA (torsion sheaves and constructible approximation). -/
theorem torsion_finite_stalk_subobjects_iSup_eq_top
    (K : Type u) [Field K]
    (M : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u + 1})
    (hM : M.IsTorsion) :
    letI : HasColimitsOfSize.{u + 1, u + 1}
      (Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u + 1}) :=
        IsGrothendieckAbelian.hasColimits _
    letI : CompleteLattice (Subobject M) := Subobject.instCompleteLattice.{u + 1}
    let Φ := (pointSmallEtale
      (Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K))))).sheafFiber
        (A := AddCommGrpCat.{u + 1})
    (⨆ N : {N : Subobject M // Finite (Φ.obj (N :
        Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u + 1}))}, N.val) = ⊤ := by
  classical
  let : HasColimitsOfSize.{u + 1, u + 1}
      (Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u + 1}) :=
    IsGrothendieckAbelian.hasColimits _
  let : CompleteLattice (Subobject M) := Subobject.instCompleteLattice.{u + 1}
  let Φ := (pointSmallEtale
    (Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K))))).sheafFiber
      (A := AddCommGrpCat.{u + 1})
  let S : Subobject M := ⨆ N : {N : Subobject M // Finite (Φ.obj (N :
    Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u + 1}))}, N.val
  change S = ⊤
  have hsurj : Function.Surjective (Φ.map S.arrow) := by
    intro x
    obtain ⟨N, hN, y, hy⟩ := torsion_exists_finite_stalk_subobject_element K M hM x
    have hle : N ≤ S := le_iSup (fun N : {N : Subobject M // Finite (Φ.obj (N :
      Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u + 1}))} ↦ N.val) ⟨N, hN⟩
    refine ⟨Φ.map (Subobject.ofLE N S hle) y, ?_⟩
    rw [← ConcreteCategory.comp_apply, ← Φ.map_comp, Subobject.ofLE_arrow]
    exact hy
  have : AB5OfSize.{u, u} AddCommGrpCat.{u + 1} :=
    AB5OfSize_shrink.{u, u, u + 1, u + 1} _
  have : PreservesFiniteLimits Φ := inferInstance
  have : Mono (Φ.map S.arrow) := Φ.map_mono _
  have : Epi (Φ.map S.arrow) := (AddCommGrpCat.epi_iff_surjective _).mpr hsurj
  have : IsIso (Φ.map S.arrow) := isIso_of_mono_of_epi _
  let i := etaleSheafEquivDiscreteContinuousRepForgetIso
    K (SeparableClosure K) (AlgebraicClosure K)
  have : (Action.forget (ModuleCat.{u + 1} ℤ)
      (Gal(SeparableClosure K/K))).ReflectsIsomorphisms :=
    ⟨fun f hf ↦ by
      change IsIso f.hom at hf
      exact Action.isIso_of_hom_isIso f⟩
  have : Φ.ReflectsIsomorphisms := reflectsIsomorphisms_of_iso i
  have : IsIso S.arrow := isIso_of_reflects_iso S.arrow Φ
  exact (Subobject.isIso_arrow_iff_eq_top S).mp inferInstance

end AlgebraicGeometry.Scheme
