/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.AlgebraicGeometry.Modules.Presheaf
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Restrict

/-!
# Sections of a kernel of `𝒪_X`-modules, and pushforward of `𝒪_X`-modules

The first half of this file describes the sections of a categorical kernel.
Limits in `X.Modules` are computed section-wise, because evaluation at an open subset
preserves finite limits (`SheafOfModules.Finite.evaluationPreservesFiniteLimits`). This file
records the resulting concrete description of the sections of a categorical kernel: over any
open `U`, the sections of `kernel f` are exactly the sections of the source that `f` kills.

This is the tool that turns a sheaf of modules defined as a kernel — as the ideal sheaf of a
`Scheme.IdealSheafData` is in `WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module` —
into a computable object.

The second half compares the pushforward functor `Scheme.Modules.pushforward f` along
`f : X ⟶ Y` with restriction to open subsets: restricting `f _* M` to an open `U` of `Y` is the
pushforward of the restriction of `M` to `f ⁻¹ᵁ U` along `f ∣_ U`. It also records the
dictionary between sheaves of modules over `𝒪_X` restricted to the site of opens contained in
`U` — which is what quasi-coherence and finite type are formulated in terms of — and sheaves of
`𝒪_X|_U`-modules on the scheme `U`.

## Main results

- `AlgebraicGeometry.Scheme.Modules.range_map_kernelι`
- `AlgebraicGeometry.Scheme.Modules.pushforwardCompRestrictFunctorIso`
- `AlgebraicGeometry.Scheme.Modules.overEquivInverseRestrictIso`
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

noncomputable section Pushforward

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens)

/-- **Base change for the pushforward of sheaves of modules.** Restricting the pushforward of
`M` along `f : X ⟶ Y` to an open `U` of `Y` is the pushforward of the restriction of `M` to
`f ⁻¹ᵁ U` along the induced morphism `f ∣_ U`. -/
def pushforwardCompRestrictFunctorIso :
    pushforward f ⋙ restrictFunctor U.ι ≅
      restrictFunctor (f ⁻¹ᵁ U).ι ⋙ pushforward (f ∣_ U) :=
  SheafOfModules.pushforwardComp _ _ ≪≫
    SheafOfModules.pushforwardCongr₂ _
      (NatIso.ofComponents (fun W ↦ eqToIso (image_morphismRestrict_preimage f U W))
        fun _ ↦ Subsingleton.elim _ _)
      (by
        ext W r
        have : (U.ι.appIso W.unop).inv ≫ f.app (U.ι ''ᵁ W.unop) ≫
              X.presheaf.map (eqToHom (image_morphismRestrict_preimage f U W.unop)).op =
            (f ∣_ U).app W.unop ≫ ((f ⁻¹ᵁ U).ι.appIso ((f ∣_ U) ⁻¹ᵁ W.unop)).inv := by
          rw [morphismRestrict_app]
          simp
          rfl
        exact congr($this r)) ≪≫
    (SheafOfModules.pushforwardComp _ _).symm

variable {f} in
/-- Restricting along an isomorphism of schemes and then along its inverse is the identity. -/
def restrictFunctorCompInvIso [IsIso f] :
    restrictFunctor f ⋙ restrictFunctor (inv f) ≅ 𝟭 Y.Modules :=
  (restrictFunctorComp (inv f) f).symm ≪≫ restrictFunctorCongr (by simp) ≪≫ restrictFunctorId

end Pushforward

noncomputable section Over

variable {X : Scheme.{u}} (U : X.Opens) (M : X.Modules)

/-- The sheaf of `𝒪_X`-modules `M` restricted to the site of opens contained in `U`
corresponds to the sheaf of `𝒪_X|_U`-modules `M.restrict U.ι` on the scheme `U`. -/
def overEquivInverseRestrictIso : (overEquiv U).inverse.obj (M.restrict U.ι) ≅ M.over U :=
  (overEquiv U).inverse.mapIso ((overFunctorEquiv U).app M).symm ≪≫
    ((overEquiv U).unitIso.app (M.over U)).symm

/-- `(Scheme.Modules.overEquiv U).inverse` sends `𝒪_X|_U` to the structure sheaf of the site of
opens contained in `U`. -/
def overEquivInverseUnitIso :
    SheafOfModules.unit.{u} (X.ringCatSheaf.over U) ≅
      (overEquiv U).inverse.obj (SheafOfModules.unit.{u} U.toScheme.ringCatSheaf) :=
  (U.sheafOfModulesEquivOverInverseUnit X.ringCatSheaf).symm

end Over

end AlgebraicGeometry.Scheme.Modules
