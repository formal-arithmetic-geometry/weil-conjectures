/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import Mathlib.AlgebraicGeometry.Modules.Presheaf
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import WeilConjectures.Mathlib.Topology.Category.TopCat.Opens

/-!
# Sections of a kernel of `𝒪_X`-modules, and the pullback of the structure sheaf

Limits in `X.Modules` are computed section-wise, because evaluation at an open subset
preserves finite limits (`SheafOfModules.Finite.evaluationPreservesFiniteLimits`). This file
records the resulting concrete description of the sections of a categorical kernel: over any
open `U`, the sections of `kernel f` are exactly the sections of the source that `f` kills.

This is the tool that turns a sheaf of modules defined as a kernel — as the ideal sheaf of a
`Scheme.IdealSheafData` is in `WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module` —
into a computable object.

The file also records that the pullback of the structure sheaf along any morphism of schemes
is the structure sheaf.

## Main results

- `AlgebraicGeometry.Scheme.Modules.range_map_kernelι`
- `AlgebraicGeometry.Scheme.Modules.pullbackObjUnitIso`: `f^* 𝒪_Y ≅ 𝒪_X`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} (U : X.Opens)
  {M N : SheafOfModules.{u} X.ringCatSheaf} (f : M ⟶ N)

/-- **The sections of a kernel are the kernel of the sections.** Over any open `U`, the image
of `kernel.ι f` on sections is the set of sections of `M` killed by `f`.

This is stated for `SheafOfModules X.ringCatSheaf` rather than for the definitionally equal
`X.Modules`, because instance search for `PreservesLimit` does not see through the latter. -/
lemma range_map_kernelι :
    Set.range ((SheafOfModules.evaluation X.ringCatSheaf (op U)).map (kernel.ι f)) =
      { x | (SheafOfModules.evaluation X.ringCatSheaf (op U)).map f x = 0 } := by
  set G := SheafOfModules.evaluation X.ringCatSheaf (op U) with hG
  have key : ((PreservesKernel.iso G f ≪≫ ModuleCat.kernelIsoKer (G.map f)).inv ≫
      G.map (kernel.ι f)) = ModuleCat.ofHom (LinearMap.ker (G.map f).hom).subtype := by
    simp [ModuleCat.kernelIsoKer_inv_kernel_ι]
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    change G.map f (G.map (kernel.ι f) y) = 0
    rw [← ConcreteCategory.comp_apply, ← G.map_comp, kernel.condition, G.map_zero]
    rfl
  · intro hx
    refine ⟨(PreservesKernel.iso G f ≪≫ ModuleCat.kernelIsoKer (G.map f)).inv ⟨x, hx⟩, ?_⟩
    have h2 := ConcreteCategory.congr_hom key ⟨x, hx⟩
    simp only [Iso.trans_inv, ConcreteCategory.comp_apply] at h2
    exact h2

lemma map_kernelι_eq :
    (SheafOfModules.evaluation X.ringCatSheaf (op U)).map (kernel.ι f) =
      (PreservesKernel.iso (SheafOfModules.evaluation X.ringCatSheaf (op U)) f).hom ≫
        kernel.ι _ := by
  rw [← PreservesKernel.iso_inv_ι]
  simp

instance : Mono ((SheafOfModules.evaluation X.ringCatSheaf (op U)).map (kernel.ι f)) := by
  rw [map_kernelι_eq]
  infer_instance

/-- `kernel.ι f` is injective on sections over any open, not merely a monomorphism. -/
lemma injective_map_kernelι :
    Function.Injective ((SheafOfModules.evaluation X.ringCatSheaf (op U)).map (kernel.ι f)) :=
  (ModuleCat.mono_iff_injective _).mp inferInstance

/-- The pullback of the structure sheaf along a morphism of schemes is the structure sheaf. -/
noncomputable def pullbackObjUnitIso {Y : Scheme.{u}} (g : X ⟶ Y) :
    (Modules.pullback g).obj (SheafOfModules.unit Y.ringCatSheaf) ≅
      SheafOfModules.unit X.ringCatSheaf :=
  -- The `IsIso` instance has to be introduced by hand: elaborating `asIso` directly leaves the
  -- universe metavariables of `pullbackObjUnitToUnit` undetermined when the instance is sought.
  haveI : IsIso (C := SheafOfModules.{u} X.ringCatSheaf)
      (SheafOfModules.pullbackObjUnitToUnit g.toRingCatSheafHom) := inferInstance
  asIso (SheafOfModules.pullbackObjUnitToUnit g.toRingCatSheafHom)

end AlgebraicGeometry.Scheme.Modules
