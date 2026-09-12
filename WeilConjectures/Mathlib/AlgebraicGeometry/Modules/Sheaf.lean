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
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.AlgebraicGeometry.Restrict
public import WeilConjectures.Mathlib.AlgebraicGeometry.Fiber
public import WeilConjectures.Mathlib.AlgebraicGeometry.Scheme
public import WeilConjectures.Mathlib.Topology.Category.TopCat.Opens

/-!
# Sections, stalks, restrictions and fibres of `𝒪_X`-modules

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

The fourth is the **fibre `F(x)` of a sheaf of modules at a point**, as a vector space over the
residue field `κ(x)`, together with the **restriction `F_y` of a sheaf of modules to a fibre of a
morphism**. Since Mathlib has no module structure on the stalk of a sheaf of modules, the fibre is
defined not as `F_x ⊗_{𝒪_{X,x}} κ(x)` but by pullback: `F(x)` is the module of global sections
of the pullback of `F` along `Spec κ(x) ⟶ X`. The two agree for quasi-coherent `F`. It is built on
a base change section, comparing global sections on `Spec S` with global sections on `Spec R`
after restriction of scalars along `φ : R ⟶ S`.

## Main definitions

- `AlgebraicGeometry.Scheme.Modules.fiberFunctor`, `AlgebraicGeometry.Scheme.Modules.fiber`: the
  fibre `F(x)` of a sheaf of `𝒪_X`-modules at a point `x`, as a `κ(x)`-vector space, and its
  functoriality `AlgebraicGeometry.Scheme.Modules.fiberMap` in `F`.
- `AlgebraicGeometry.Scheme.Modules.restrictToFiber`: the restriction `F ↦ F_y` of sheaves of
  modules to the scheme-theoretic fibre of a morphism over a point.

## Main results

- `AlgebraicGeometry.Scheme.Modules.range_map_kernelι`
- `AlgebraicGeometry.Scheme.Modules.germₗ`: the germ map `Γ(F, U) →ₗ[Γ(X, U)] F_x`.
- `AlgebraicGeometry.Scheme.Modules.pushforwardCompRestrictFunctorIso`
- `AlgebraicGeometry.Scheme.Modules.restrictFunctorCompMorphismRestrictIso`
- `AlgebraicGeometry.Scheme.Modules.overEquivInverseRestrictIso`
- `AlgebraicGeometry.Scheme.Modules.pullbackUnitIso`
- `AlgebraicGeometry.Scheme.Modules.pullbackOver`
- `AlgebraicGeometry.Scheme.Modules.pullbackOverObjIso`
- `AlgebraicGeometry.Scheme.Modules.pullbackTriangle`: the pullback functors along a commuting
  triangle `h ≫ v = u`, namely `v^* ⋙ h^* ≅ u^*`, together with its compatibility
  `AlgebraicGeometry.Scheme.Modules.pullbackTriangle_hom_app_sectionsPullback` with the pullback
  of global sections.
- `AlgebraicGeometry.Scheme.Modules.moduleSpecΓPushforwardIso`,
  `AlgebraicGeometry.Scheme.Modules.moduleSpecΓPullbackIso`: base change of the global sections
  of a sheaf of modules on `Spec S` along `φ : R ⟶ S`.
- `AlgebraicGeometry.Scheme.Modules.fiberFunctorPullbackIso`,
  `AlgebraicGeometry.Scheme.Modules.fiberPullbackIso`: compatibility of the fibre with pullback,
  for a morphism `u` inducing an isomorphism on residue fields at the point in question.
- `AlgebraicGeometry.Scheme.Modules.fiberRestrictToFiberIso`: the fibre of `F_y` at a point `x`
  of the fibre is the fibre of `F` at `f.fiberι y x`.

## Blueprint

The fibre and the restriction to a fibre are notion **(N2)** of `sec:cube-cost`, the formalisation
count of the theorem-of-the-cube chapter. Deferred to later issues, because they need the monoidal
structure on sheaves of modules and the notion of an invertible sheaf, neither of which is
available: the compatibility of the fibre with tensor products and with inverses of line bundles,
and the one-dimensionality of the fibre of a locally free sheaf of rank one.
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

/-!
## Pulling back sections along a morphism of schemes
-/

noncomputable section PushforwardPullback

variable {X Y Z : Scheme.{u}} (a : X ⟶ Y) (b : Y ⟶ Z) (M : Z.Modules)

/-- The canonical morphism `b_* b^* M ⟶ (a ≫ b)_* (a ≫ b)^* M`, obtained by applying `b_*`
to the unit of the adjunction `a^* ⊣ a_*`. -/
noncomputable def pushforwardPullbackComp :
    (pushforward b).obj ((pullback b).obj M) ⟶
      (pushforward (a ≫ b)).obj ((pullback (a ≫ b)).obj M) :=
  (pushforward b).map ((pullbackPushforwardAdjunction a).unit.app ((pullback b).obj M)) ≫
    (pushforwardComp a b).hom.app ((pullback a).obj ((pullback b).obj M)) ≫
      (pushforward (a ≫ b)).map ((pullbackComp a b).hom.app M)

/-- The morphism `b_* b^* M ⟶ (a ≫ b)_* (a ≫ b)^* M` is compatible with the units of the
adjunctions, so that the section `s` of `M` over an open subset has the same image in
`Γ((a ≫ b)^* M, _)` whether it is pulled back in one step or in two. -/
@[reassoc (attr := simp)]
lemma unit_pushforwardPullbackComp :
    (pullbackPushforwardAdjunction b).unit.app M ≫ pushforwardPullbackComp a b M =
      (pullbackPushforwardAdjunction (a ≫ b)).unit.app M := by
  have h := unit_conjugateEquiv ((pullbackPushforwardAdjunction b).comp
    (pullbackPushforwardAdjunction a)) (pullbackPushforwardAdjunction (a ≫ b))
    (pullbackComp a b).inv M
  rw [conjugateEquiv_pullbackComp_inv, Adjunction.comp_unit_app] at h
  simp only [Functor.comp_obj] at h
  rw [pushforwardPullbackComp, ← Category.assoc, ← Category.assoc, h, Category.assoc,
    ← Functor.map_comp]
  simp

lemma pushforward_smul {X Y : Scheme.{u}} (a : X ⟶ Y) (N : X.Modules) (U : Y.Opens)
    (r : Γ(Y, U)) :
    ((pushforward a).obj N).smul (U := U) r = N.smul (a.app U r) := rfl

lemma eqToHom_pushforward_smul {X' Y' : Scheme.{u}} (a : X' ⟶ Y') (N : X'.Modules) (U : Y'.Opens)
    (r : Γ(Y', U)) (y : Γ((pushforward a).obj N, U)) :
    eqToHom (pushforward_obj_obj a N U) (r • y) =
      a.app U r • eqToHom (pushforward_obj_obj a N U) y := rfl

/-- The restriction map `Γ(X', a ⁻¹ᵁ ⊤) ⟶ Γ(X', ⊤)` is the identity, so that restricting
the pullback of a global function gives the pullback of functions on global sections. -/
lemma map_le_top_app_top {X' Y' : Scheme.{u}} (a : X' ⟶ Y') (r : Γ(Y', ⊤)) :
    X'.presheaf.map (homOfLE (by simp : (⊤ : X'.Opens) ≤ a ⁻¹ᵁ ⊤)).op (a.app ⊤ r) =
      a.appTop r := by
  exact (ConcreteCategory.congr_hom
    (Scheme.presheaf_map_homOfLE_preimage_top_eq_id X'.presheaf a) _).trans rfl

/-- The pullback of global sections along a morphism of schemes: the image of a global section
of `N` under the unit `N ⟶ a_* a^* N`, read as a global section of `a^* N`. -/
noncomputable def sectionsPullback {X' Y' : Scheme.{u}} (a : X' ⟶ Y') (N : Y'.Modules) :
    Γ(N, ⊤) ⟶ Γ((pullback a).obj N, ⊤) :=
  ((pullbackPushforwardAdjunction a).unit.app N).app ⊤ ≫
    eqToHom (pushforward_obj_obj a ((pullback a).obj N) ⊤) ≫
    ((pullback a).obj N).presheaf.map (homOfLE (by simp : (⊤ : X'.Opens) ≤ a ⁻¹ᵁ ⊤)).op

/-- The pullback of global sections is semilinear over the pullback of functions. -/
lemma sectionsPullback_smul {X' Y' : Scheme.{u}} (a : X' ⟶ Y') (N : Y'.Modules)
    (r : Γ(Y', ⊤)) (s : Γ(N, ⊤)) :
    sectionsPullback a N (r • s) = a.appTop r • sectionsPullback a N s := by
  rw [sectionsPullback]
  simp only [ConcreteCategory.comp_apply, Functor.id_obj, Functor.comp_obj, Hom.app_smul,
    eqToHom_pushforward_smul, map_smul]
  rw [map_le_top_app_top]

lemma pushforwardPullbackComp_app (V : Z.Opens) :
    (pushforwardPullbackComp a b M).app V =
      ((pullbackPushforwardAdjunction a).unit.app ((pullback b).obj M)).app (b ⁻¹ᵁ V) ≫
        ((pullbackComp a b).hom.app M).app ((a ≫ b) ⁻¹ᵁ V) := by
  simp [pushforwardPullbackComp]

/-- Pulling back a global section in two steps, along `a` and then along `b`, agrees with
pulling it back in one step along `a ≫ b`, under the identification `a^* b^* M ≅ (a ≫ b)^* M`:

```
                 sectionsPullback b
         Γ(M, ⊤) ───────────────────→ Γ(b^* M, ⊤)
            │                              │
            │ sectionsPullback (a ≫ b)     │ sectionsPullback a
            ↓                              ↓
  Γ((a ≫ b)^* M, ⊤) ←──────────────── Γ(a^* b^* M, ⊤)
                      (pullbackComp a b).hom
```
-/
@[simp]
lemma pullbackComp_hom_app_sectionsPullback (s : Γ(M, ⊤)) :
    Hom.app ((pullbackComp a b).hom.app M) ⊤
        (sectionsPullback a ((pullback b).obj M) (sectionsPullback b M s)) =
      sectionsPullback (a ≫ b) M s := by
  have key := congrArg (fun ψ ↦ Hom.app ψ ⊤ s) (unit_pushforwardPullbackComp a b M)
  simp only [Hom.comp_app, pushforwardPullbackComp_app] at key
  simp only [sectionsPullback, ConcreteCategory.comp_apply,
    Scheme.presheaf_map_homOfLE_preimage_top_eq_id]
  exact key

/-- Pulling back a global section along equal morphisms gives the same section, under the
identification `c^* M ≅ d^* M`:

```
                  sectionsPullback c
          Γ(N, ⊤) ──────────────────→ Γ(c^* N, ⊤)
              ╲                            │
               ╲ sectionsPullback d        │ (pullbackCongr h).hom
                ↘                          ↓
                             Γ(d^* N, ⊤)
```
-/
@[simp]
lemma pullbackCongr_hom_app_sectionsPullback {c d : X ⟶ Y} (h : c = d) (N : Y.Modules)
    (s : Γ(N, ⊤)) :
    Hom.app ((pullbackCongr h).hom.app N) ⊤ (sectionsPullback c N s) = sectionsPullback d N s := by
  subst h
  rfl

end PushforwardPullback

noncomputable section Triangle

/-! ### The pullback functors along a commuting triangle -/

variable {X Y Z : Scheme.{u}} {h : X ⟶ Y} {v : Y ⟶ Z} {u : X ⟶ Z}

/-- **The pullback functors along a commuting triangle**: for `h ≫ v = u`, that is, for

```
          h
    X ─────────→ Y
      ╲          │
       ╲ u       │ v
        ↘        ↓
                 Z
```

commuting, pulling back along `v` and then along `h` is pulling back along `u`. -/
def pullbackTriangle (w : h ≫ v = u) : pullback v ⋙ pullback h ≅ pullback u :=
  pullbackComp h v ≪≫ pullbackCongr w

/-- Under the identification `h^* v^* M ≅ u^* M` of `Scheme.Modules.pullbackTriangle`, pulling
a global section back along `v` and then along `h` agrees with pulling it back along `u`. -/
@[simp]
lemma pullbackTriangle_hom_app_sectionsPullback (w : h ≫ v = u) (M : Z.Modules) (s : Γ(M, ⊤)) :
    Hom.app ((pullbackTriangle w).hom.app M) ⊤
        (sectionsPullback h ((pullback v).obj M) (sectionsPullback v M s)) =
      sectionsPullback u M s := by
  simp only [pullbackTriangle, Iso.trans_hom, NatTrans.comp_app, Hom.comp_app,
    ConcreteCategory.comp_apply, pullbackComp_hom_app_sectionsPullback,
    pullbackCongr_hom_app_sectionsPullback]

end Triangle

section BaseChange

variable {R S : CommRingCat.{u}}

/-- Taking global sections of a sheaf of modules on `Spec S` and restricting scalars along
`φ : R ⟶ S` is the same as pushing forward along `Spec φ` and taking global sections there. -/
noncomputable def moduleSpecΓPushforwardIso (φ : R ⟶ S) :
    Modules.pushforward (Spec.map φ) ⋙ moduleSpecΓFunctor (R := R) ≅
      moduleSpecΓFunctor (R := S) ⋙ ModuleCat.restrictScalars φ.hom :=
  NatIso.ofComponents (fun N ↦
    { hom := ModuleCat.homEquiv.symm
        { toFun := id
          map_add' := fun _ _ ↦ rfl
          map_smul' := by
            intro r x
            obtain ⟨y, rfl⟩ : ∃ y : Γ(N, ⊤), y = x := ⟨x, rfl⟩
            change ((Spec.map φ).appTop ((Scheme.ΓSpecIso R).inv r)) • y =
              ((Scheme.ΓSpecIso S).inv (φ r)) • y
            have h := congr($(Scheme.ΓSpecIso_inv_naturality φ) r)
            simp only [CommRingCat.comp_apply] at h
            rw [← h] }
      inv := ModuleCat.homEquiv.symm
        { toFun := id
          map_add' := fun _ _ ↦ rfl
          map_smul' := by
            intro r x
            obtain ⟨y, rfl⟩ : ∃ y : Γ(N, ⊤), y = x := ⟨x, rfl⟩
            change ((Scheme.ΓSpecIso S).inv (φ r)) • y =
              ((Spec.map φ).appTop ((Scheme.ΓSpecIso R).inv r)) • y
            have h := congr($(Scheme.ΓSpecIso_inv_naturality φ) r)
            simp only [CommRingCat.comp_apply] at h
            rw [h] }
      hom_inv_id := rfl
      inv_hom_id := rfl }) (fun _ ↦ rfl)

variable {X Y : Scheme.{u}}

/-- The pullback of sheaves of modules along an isomorphism is the pushforward along its
inverse. -/
noncomputable def pullbackIsoPushforwardInv (f : X ⟶ Y) [IsIso f] :
    Modules.pullback f ≅ Modules.pushforward (inv f) :=
  Adjunction.rightAdjointUniq
    (CategoryTheory.Equivalence.mk (Modules.pullback f) (Modules.pullback (inv f))
      (pullbackComp (inv f) f ≪≫ pullbackCongr (by simp) ≪≫ pullbackId Y).symm
      (pullbackComp f (inv f) ≪≫ pullbackCongr (by simp) ≪≫ pullbackId X)).symm.toAdjunction
    (pullbackPushforwardAdjunction (inv f))

/-- **Base change of global sections along an isomorphism of rings.** For `φ : R ⟶ S` an
isomorphism, pulling a sheaf of modules on `Spec R` back along `Spec φ` and taking global
sections is restricting the scalars of its global sections along `φ⁻¹`. -/
noncomputable def moduleSpecΓPullbackIso (φ : R ⟶ S) [IsIso φ] :
    Modules.pullback (Spec.map φ) ⋙ moduleSpecΓFunctor (R := S) ≅
      moduleSpecΓFunctor (R := R) ⋙ ModuleCat.restrictScalars (inv φ).hom :=
  Functor.isoWhiskerRight (pullbackIsoPushforwardInv (Spec.map φ)) _ ≪≫
    Functor.isoWhiskerRight (pushforwardCongr (Spec.map_inv φ).symm) _ ≪≫
    moduleSpecΓPushforwardIso (inv φ)

end BaseChange

section Fiber

variable {X Y : Scheme.{u}}

/-- The fibre functor at a point `x` of a scheme `X`: it sends a sheaf of `𝒪_X`-modules `F` to
the `κ(x)`-vector space `F(x)`, obtained by pulling `F` back along `Spec κ(x) ⟶ X` and taking
global sections. -/
noncomputable def fiberFunctor (X : Scheme.{u}) (x : X) :
    X.Modules ⥤ ModuleCat (X.residueField x) :=
  Modules.pullback (X.fromSpecResidueField x) ⋙ moduleSpecΓFunctor (R := X.residueField x)

/-- The fibre `F(x)` of a sheaf of `𝒪_X`-modules at a point `x`, as a `κ(x)`-vector space. -/
noncomputable abbrev fiber (F : X.Modules) (x : X) : ModuleCat (X.residueField x) :=
  (fiberFunctor X x).obj F

/-- The `κ(x)`-linear map `φ(x) : F(x) ⟶ G(x)` induced by a morphism `φ : F ⟶ G` of sheaves of
`𝒪_X`-modules. -/
noncomputable abbrev fiberMap {F G : X.Modules} (φ : F ⟶ G) (x : X) : F.fiber x ⟶ G.fiber x :=
  (fiberFunctor X x).map φ

@[simp]
lemma fiberMap_id (F : X.Modules) (x : X) : fiberMap (𝟙 F) x = 𝟙 (F.fiber x) :=
  (fiberFunctor X x).map_id F

@[simp]
lemma fiberMap_comp {F G H : X.Modules} (φ : F ⟶ G) (ψ : G ⟶ H) (x : X) :
    fiberMap (φ ≫ ψ) x = fiberMap φ x ≫ fiberMap ψ x :=
  (fiberFunctor X x).map_comp φ ψ

/-- The restriction `F ↦ F_y` of sheaves of modules to the scheme-theoretic fibre of
`f : X ⟶ Y` over a point `y : Y`, that is, the pullback along `f.fiberι y`. -/
noncomputable abbrev restrictToFiber (f : X ⟶ Y) (y : Y) : X.Modules ⥤ (f.fiber y).Modules :=
  Modules.pullback (f.fiberι y)

/-- **The fibre of a pullback.** If `u : X ⟶ Y` induces an isomorphism `κ(u x) ≅ κ(x)` on
residue fields, then the fibre of `u^* F` at `x` is the fibre of `F` at `u x`, viewed as a
`κ(x)`-vector space along `κ(u x) ≅ κ(x)`. -/
noncomputable def fiberFunctorPullbackIso (u : X ⟶ Y) (x : X) [IsIso (u.residueFieldMap x)] :
    Modules.pullback u ⋙ fiberFunctor X x ≅
      fiberFunctor Y (u x) ⋙ ModuleCat.restrictScalars (inv (u.residueFieldMap x)).hom :=
  Functor.isoWhiskerRight (pullbackComp (X.fromSpecResidueField x) u)
      (moduleSpecΓFunctor (R := X.residueField x)) ≪≫
    Functor.isoWhiskerRight (pullbackCongr (u.SpecMap_residueFieldMap_fromSpecResidueField x).symm)
      (moduleSpecΓFunctor (R := X.residueField x)) ≪≫
    Functor.isoWhiskerRight
      (pullbackComp (Spec.map (u.residueFieldMap x)) (Y.fromSpecResidueField (u x))).symm
      (moduleSpecΓFunctor (R := X.residueField x)) ≪≫
    Functor.isoWhiskerLeft (Modules.pullback (Y.fromSpecResidueField (u x)))
      (moduleSpecΓPullbackIso (u.residueFieldMap x))

/-- The fibre of `u^* F` at `x`, for `u` inducing an isomorphism on the residue field at `x`. -/
noncomputable def fiberPullbackIso (u : X ⟶ Y) (F : Y.Modules) (x : X)
    [IsIso (u.residueFieldMap x)] :
    ((Modules.pullback u).obj F).fiber x ≅
      (ModuleCat.restrictScalars (inv (u.residueFieldMap x)).hom).obj (F.fiber (u x)) :=
  (fiberFunctorPullbackIso u x).app F

/-- **The fibre of a restriction to a fibre.** The fibre of `F_y` at a point `x` of the
scheme-theoretic fibre of `f` over `y` is the fibre of `F` at `f.fiberι y x`; the residue fields
`κ(f.fiberι y x)` and `κ(x)` agree because `f.fiberι y` is a preimmersion. -/
noncomputable def fiberRestrictToFiberIso (f : X ⟶ Y) (y : Y) (F : X.Modules) (x : f.fiber y) :
    ((restrictToFiber f y).obj F).fiber x ≅
      (ModuleCat.restrictScalars (inv ((f.fiberι y).residueFieldMap x)).hom).obj
        (F.fiber (f.fiberι y x)) :=
  fiberPullbackIso (f.fiberι y) F x

end Fiber

end AlgebraicGeometry.Scheme.Modules
