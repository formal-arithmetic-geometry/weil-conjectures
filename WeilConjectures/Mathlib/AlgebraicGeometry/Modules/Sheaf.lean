/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import Mathlib.Algebra.Category.ModuleCat.Stalk
public import Mathlib.AlgebraicGeometry.Modules.Presheaf
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Restrict
public import WeilConjectures.Mathlib.Topology.Category.TopCat.Opens

/-!
# Sections, stalks and restrictions of `𝒪_X`-modules

This file collects three groups of results about sheaves of modules over a scheme.

The first is a concrete description of the sections of a categorical kernel. Limits in
`X.Modules` are computed section-wise, because evaluation at an open subset preserves finite
limits (`SheafOfModules.Finite.evaluationPreservesFiniteLimits`): over any open `U`, the sections
of `kernel f` are exactly the sections of the source that `f` kills. This is the tool that turns
a sheaf of modules defined as a kernel — as the ideal sheaf of a `Scheme.IdealSheafData` is in
`WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module` — into a computable object.

The second transports the module structure on the stalk of a presheaf of modules
(`PresheafOfModules.instModule`) to `X.Modules`: the stalk `F_x` of a sheaf of `𝒪_X`-modules is a
module over the local ring `𝒪_{X, x}`, and, for `x` in an open `U`, over `Γ(X, U)` by restriction
of scalars along the germ map.

The third compares the pushforward and pullback functors along `f : X ⟶ Y` with restriction to
open subsets: restricting `f _* M` to an open `U` of `Y` is the pushforward of the restriction of
`M` to `f ⁻¹ᵁ U` along `f ∣_ U`, the pullback of `𝒪_Y` is `𝒪_X`, and the pullback commutes with
restricting to an open `U` of `Y` and to its preimage. The latter is packaged as a functor
`Scheme.Modules.pullbackOver` between the categories of modules over the restricted structure
sheaves, which is what quasi-coherence and finite type are formulated in terms of. This group
also records the dictionary between sheaves of modules over `𝒪_X` restricted to the site of opens
contained in `U` and sheaves of `𝒪_X|_U`-modules on the scheme `U`.

## Main results

- `AlgebraicGeometry.Scheme.Modules.range_map_kernelι`
- `AlgebraicGeometry.Scheme.Modules.germₗ`: the germ map `Γ(F, U) →ₗ[Γ(X, U)] F_x`.
- `AlgebraicGeometry.Scheme.Modules.pushforwardCompRestrictFunctorIso`
- `AlgebraicGeometry.Scheme.Modules.restrictFunctorCompMorphismRestrictIso`
- `AlgebraicGeometry.Scheme.Modules.overEquivInverseRestrictIso`
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

section Stalk

variable {U} (F : X.Modules)

/-- The stalk of a sheaf of `𝒪_X`-modules at `x` is a module over the local ring `𝒪_{X, x}`. -/
noncomputable instance moduleStalk (x : X) : Module (X.presheaf.stalk x) (F.presheaf.stalk x) :=
  letI M : _root_.PresheafOfModules.{u} (X.presheaf ⋙ forget₂ CommRingCat RingCat) := F.val
  inferInstanceAs (Module (X.presheaf.stalk x) (TopCat.Presheaf.stalk (C := Ab.{u}) M.presheaf x))

lemma germ_smul (x : X) (hx : x ∈ U) (r : Γ(X, U)) (m : Γ(F, U)) :
    F.presheaf.germ U x hx (r • m) = X.presheaf.germ U x hx r • F.presheaf.germ U x hx m :=
  PresheafOfModules.germ_smul (R := X.presheaf) (M := F.val) x U hx r m

/-- The stalk of a sheaf of `𝒪_X`-modules at a point of `U` is a module over `Γ(X, U)`,
by restriction of scalars along the germ map. -/
noncomputable instance module_section_stalk (x : U) : Module Γ(X, U) (F.presheaf.stalk x.1) :=
  Module.compHom _ (X.presheaf.germ U x.1 x.2).hom

lemma smul_stalk_def (x : U) (r : Γ(X, U)) (m : F.presheaf.stalk x.1) :
    r • m = X.presheaf.germ U x.1 x.2 r • m :=
  rfl

instance isScalarTower_section_stalk (x : U) :
    IsScalarTower Γ(X, U) (X.presheaf.stalk x.1) (F.presheaf.stalk x.1) :=
  .of_algebraMap_smul fun _ _ ↦ rfl

/-- The germ map on sections, as a `Γ(X, U)`-linear map. -/
noncomputable def germₗ (x : U) : Γ(F, U) →ₗ[Γ(X, U)] F.presheaf.stalk x.1 where
  toFun := F.presheaf.germ U x.1 x.2
  map_add' := map_add _
  map_smul' r m := by
    change F.presheaf.germ U x.1 x.2 (r • m) = _
    rw [germ_smul]
    rfl

@[simp]
lemma germₗ_apply (x : U) (m : Γ(F, U)) :
    germₗ F x m = F.presheaf.germ U x.1 x.2 m := rfl

end Stalk
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

/-- Restricting along the inverse of an isomorphism of schemes and then along the isomorphism
itself is the identity. -/
def restrictFunctorInvCompIso (e : X ≅ Y) :
    restrictFunctor e.inv ⋙ restrictFunctor e.hom ≅ 𝟭 X.Modules :=
  (restrictFunctorComp e.hom e.inv).symm ≪≫ restrictFunctorCongr e.hom_inv_id ≪≫
    restrictFunctorId

/-- **Base change for the restriction of sheaves of modules to an open subscheme.** Restricting
`M` to an open `U` of `Y` and then along an open immersion `f : X ⟶ Y` is the same as restricting
`M` along `f` and then to `f ⁻¹ᵁ U`. -/
def restrictFunctorCompMorphismRestrictIso [IsOpenImmersion f] :
    restrictFunctor U.ι ⋙ restrictFunctor (f ∣_ U) ≅
      restrictFunctor f ⋙ restrictFunctor (f ⁻¹ᵁ U).ι :=
  (restrictFunctorComp (f ∣_ U) U.ι).symm ≪≫
    restrictFunctorCongr (morphismRestrict_ι f U) ≪≫ restrictFunctorComp (f ⁻¹ᵁ U).ι f

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
