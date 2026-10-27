/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A4
-/
module

public import Sheaf.AlgebraicGeometry.OrbitTensorLineSections
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Sheaf.AlgebraicGeometry.FiniteTrivializeInvertibleUpstairs
import WeilConjectures.AlgebraicGeometry.Modules.PullbackFreeGenerator

/-! # Local orbit tensor frames above a finite morphism

Source: Stacks Project, Tags 0BUT, 01CD and 01CA.
(blueprint: lem-per-orbit-tensor-local-frames)
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u v

open CategoryTheory MonoidalCategory Opposite

namespace AlgebraicGeometry.Scheme.Modules

private theorem tensorPullbackSection_freeGenerator {X Y : Scheme.{u}} (b : X ⟶ Y)
    (L : Y.Modules) (U : Y.Opens) (s : Γ(L, U)) (hs : IsFreeGenerator s) :
    IsFreeGenerator (tensorPullbackSection b L U s) := by
  let adj := tensorPullbackSectionAdjunction b
  let cmp := adj.leftAdjointUniq (pullbackPushforwardAdjunction b)
  have hn : (adj.unit.app L).app U s = tensorPullbackSection b L U s :=
    (Classical.choose_spec (existsUnique_tensorPullbackSectionAdjunction b)).1 L U s
  have h : (cmp.app L).hom.app (b ⁻¹ᵁ U) (tensorPullbackSection b L U s) =
      ((pullbackPushforwardAdjunction b).unit.app L).app U s := by
    rw [← hn]
    exact congrArg (fun f ↦ f.app U s)
      (adj.unit_leftAdjointUniq_hom_app (pullbackPushforwardAdjunction b) L)
  have ht := (hs.pullback_unit_app b).app_hom (cmp.app L).symm
  rw [← h] at ht
  simpa only [Iso.symm_hom, inv_app_hom_app_apply_of_iso] using ht

private theorem orbitInvariantPullback_freeGenerator {X : Scheme.{u}} (b : X ⟶ X)
    (L : X.Modules) (U : X.Opens) (hU : b ⁻¹ᵁ U = U) (s : Γ(L, U))
    (hs : IsFreeGenerator s) : IsFreeGenerator (orbitInvariantPullback b L U hU s) := by
  exact (tensorPullbackSection_freeGenerator b L U s hs).map hU.symm.le

private theorem orbitUnit_freeGenerator {X : Scheme.{u}} (U : X.Opens) :
    IsFreeGenerator (unitSectionsEquiv U 1) := by
  intro W hW
  simpa only [presheaf_map_unitSectionsEquiv, map_one,
    ← unitSectionsEquiv_eq_smul_one] using (unitSectionsEquiv W).bijective

private theorem orbitTensorFrameList_freeGenerator {H : Type v} {X : Scheme.{u}}
    (a : H → (X ≅ X)) (L : X.Modules) (U : X.Opens)
    (hU : ∀ h : H, (a h).hom ⁻¹ᵁ U = U) (s : Γ(L, U)) (hs : IsFreeGenerator s)
    (l : List H) : IsFreeGenerator (orbitTensorFrameList a L U hU s l) := by
  induction l with
  | nil => exact orbitUnit_freeGenerator U
  | cons h l ih =>
    exact (orbitInvariantPullback_freeGenerator (a h).hom L U (hU h) s hs).tmulSection ih

private theorem orbitPowerSection_freeGenerator {X : Scheme.{u}} (F : X.Modules)
    (U : X.Opens) (n : Γ(F, U)) (hn : IsFreeGenerator n) (d : ℕ) :
    IsFreeGenerator (orbitPowerSection F U d (fun _ ↦ n)) := by
  induction d with
  | zero => exact orbitUnit_freeGenerator U
  | succ d ih => exact hn.tmulSection ih

/-- A finite morphism admits neighbourhoods downstairs on which the orbit tensor and
all its powers have the explicit orbit frames as free generators.

Source: Stacks Project, Tag 0BUT for a frame of L upstairs, and Tags 01CD and 01CA
for pullback and tensor products of frames (blueprint: lem-per-orbit-tensor-local-frames).

Proof: trivialize L over the inverse image of a neighbourhood of y by Tag 0BUT.
Read the trivialization as a free generator s. Every translate of s is again a
free generator, using the normalized pullback adjunction and transport along the
invariance equality of opens. Induct on the list of group elements, tensoring these
free generators, with the section 1 of the tensor unit as the empty-list case.
Induct once more on d for the powers. This also proves the case d = 0. -/
theorem exists_orbit_tensor_local_frames {H : Type v} [Finite H] {X Y : Scheme.{u}}
    (a : H → (X ≅ X)) (q : X ⟶ Y) [IsFinite q]
    (aq : ∀ h : H, (a h).hom ≫ q = q) (L : X.Modules) [L.IsInvertible] (y : Y) :
    ∃ (T : Y.Opens) (s : Γ(L, q ⁻¹ᵁ T)), y ∈ T ∧
      IsFreeGenerator (orbitTensorFrame a L (q ⁻¹ᵁ T)
        (fun h ↦ congrArg (fun k : X ⟶ Y ↦ k ⁻¹ᵁ T) (aq h)) s) ∧
      ∀ d : ℕ, IsFreeGenerator
        (orbitPowerSection (pencilOrbitBundle a L) (q ⁻¹ᵁ T) d
          (fun _ ↦ orbitTensorFrame a L (q ⁻¹ᵁ T)
            (fun h ↦ congrArg (fun k : X ⟶ Y ↦ k ⁻¹ᵁ T) (aq h)) s)) := by
  obtain ⟨T, hy, ⟨e⟩⟩ := exists_trivialization_over_preimage_of_isFinite q L y
  let U := q ⁻¹ᵁ T
  let e' : L.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U) :=
    (overEquiv U).unitIso.app _ ≪≫ (overEquiv U).inverse.mapIso
      ((overFunctorEquiv U).app L ≪≫ e ≪≫ overEquivFunctorObjUnitIso U) ≪≫
        (overEquiv U).unitIso.symm.app _
  obtain ⟨s, hs⟩ := exists_isFreeGenerator_of_iso e'
  have hn := orbitTensorFrameList_freeGenerator a L U
    (fun h ↦ congrArg (fun k : X ⟶ Y ↦ k ⁻¹ᵁ T) (aq h)) s hs (pencilGroupElements H)
  exact ⟨T, s, hy, hn, fun d ↦ orbitPowerSection_freeGenerator _ U _ hn d⟩

end AlgebraicGeometry.Scheme.Modules
