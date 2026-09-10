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
public import Mathlib.AlgebraicGeometry.Restrict
public import WeilConjectures.Mathlib.Topology.Category.TopCat.Opens

/-!
# Sections of a kernel of `𝒪_X`-modules, and pullback of `𝒪_X`-modules

The first half of this file describes the sections of a categorical kernel. Limits in
`X.Modules` are computed section-wise, because evaluation at an open subset preserves finite
limits (`SheafOfModules.Finite.evaluationPreservesFiniteLimits`): over any open `U`, the
sections of `kernel f` are exactly the sections of the source that `f` kills.

This is the tool that turns a sheaf of modules defined as a kernel — as the ideal sheaf of a
`Scheme.IdealSheafData` is in `WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module` —
into a computable object.

The second half provides the material needed to compare the pullback functor
`Scheme.Modules.pullback f` along `f : X ⟶ Y` with restriction to open subsets. The key point
is that the pullback of `𝒪_Y` is `𝒪_X`, and that the pullback commutes with restricting to an
open `U` of `Y` and to its preimage. These are packaged as a functor `Scheme.Modules.pullbackOver`
between the categories of modules over the restricted structure sheaves, which is what
quasi-coherence and finite type are formulated in terms of.

## Main results

- `AlgebraicGeometry.Scheme.Modules.range_map_kernelι`
- `AlgebraicGeometry.Scheme.Modules.pullbackUnitIso`
- `AlgebraicGeometry.Scheme.Modules.pullbackOver`
- `AlgebraicGeometry.Scheme.Modules.pullbackOverObjIso`
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite SheafOfModules TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

section Kernel

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

end Kernel

section Pullback

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens)

/-- The pullback of the structure sheaf `𝒪_Y` along a morphism of schemes `f : X ⟶ Y`
is the structure sheaf `𝒪_X`. -/
noncomputable def pullbackUnitIso :
    (pullback f).obj (SheafOfModules.unit.{u} Y.ringCatSheaf) ≅
      SheafOfModules.unit.{u} X.ringCatSheaf :=
  have : (SheafOfModules.pushforward f.toRingCatSheafHom).IsRightAdjoint :=
    inferInstanceAs (Modules.pushforward f).IsRightAdjoint
  have := SheafOfModules.instIsIsoPullbackObjUnitToUnitOfFinal (φ := f.toRingCatSheafHom)
  asIso (SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom)

set_option backward.isDefEq.respectTransparency false in
/-- **Base change for the pullback of sheaves of modules.** Restricting the pullback of `M`
along `f : X ⟶ Y` to `f ⁻¹ᵁ U` is the pullback of the restriction of `M` to `U` along the
induced morphism `f ⁻¹ᵁ U ⟶ U`. -/
noncomputable def restrictFunctorCompPullbackIso :
    restrictFunctor U.ι ⋙ pullback (f.resLE U (f ⁻¹ᵁ U) le_rfl) ≅
      pullback f ⋙ restrictFunctor (f ⁻¹ᵁ U).ι :=
  Functor.isoWhiskerRight (restrictFunctorIsoPullback U.ι) _ ≪≫
    pullbackComp _ _ ≪≫ pullbackCongr (f.resLE_comp_ι le_rfl) ≪≫ (pullbackComp _ _).symm ≪≫
    Functor.isoWhiskerLeft _ (restrictFunctorIsoPullback (f ⁻¹ᵁ U).ι).symm

/-- The pullback functor on the level of the slices: it takes a sheaf of modules over
`𝒪_Y` restricted to `U` to a sheaf of modules over `𝒪_X` restricted to `f ⁻¹ᵁ U`. -/
noncomputable def pullbackOver :
    SheafOfModules.{u} (Y.ringCatSheaf.over U) ⥤
      SheafOfModules.{u} (X.ringCatSheaf.over (f ⁻¹ᵁ U)) :=
  (overEquiv U).functor ⋙ pullback (f.resLE U (f ⁻¹ᵁ U) le_rfl) ⋙
    (overEquiv (f ⁻¹ᵁ U)).inverse

instance : PreservesColimitsOfSize.{u, u} (pullbackOver f U) := by
  unfold pullbackOver
  infer_instance

/-- `Scheme.Modules.pullbackOver` sends the structure sheaf to the structure sheaf. -/
noncomputable def pullbackOverUnitIso :
    SheafOfModules.unit.{u} (X.ringCatSheaf.over (f ⁻¹ᵁ U)) ≅
      (pullbackOver f U).obj (SheafOfModules.unit.{u} (Y.ringCatSheaf.over U)) :=
  ((f ⁻¹ᵁ U).sheafOfModulesEquivOverInverseUnit X.ringCatSheaf).symm ≪≫
    (overEquiv (f ⁻¹ᵁ U)).inverse.mapIso
      ((pullbackUnitIso (f.resLE U (f ⁻¹ᵁ U) le_rfl)).symm ≪≫
        (pullback (f.resLE U (f ⁻¹ᵁ U) le_rfl)).mapIso
          (U.sheafOfModulesEquivOverUnit Y.ringCatSheaf).symm)

/-- `Scheme.Modules.pullbackOver` computes the restriction to `f ⁻¹ᵁ U` of the pullback
of `M` in terms of the restriction of `M` to `U`. -/
noncomputable def pullbackOverObjIso (M : Y.Modules) :
    (pullbackOver f U).obj (M.over U) ≅ ((pullback f).obj M).over (f ⁻¹ᵁ U) :=
  (overEquiv (f ⁻¹ᵁ U)).inverse.mapIso
      ((pullback (f.resLE U (f ⁻¹ᵁ U) le_rfl)).mapIso ((overFunctorEquiv U).app M) ≪≫
        (restrictFunctorCompPullbackIso f U).app M ≪≫
        ((overFunctorEquiv (f ⁻¹ᵁ U)).app ((pullback f).obj M)).symm) ≪≫
    ((overEquiv (f ⁻¹ᵁ U)).unitIso.app (((pullback f).obj M).over (f ⁻¹ᵁ U))).symm

end Pullback

end AlgebraicGeometry.Scheme.Modules
