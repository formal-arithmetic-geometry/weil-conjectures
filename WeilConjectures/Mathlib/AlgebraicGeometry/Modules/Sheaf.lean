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
public import Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import WeilConjectures.Mathlib.AlgebraicGeometry.Fiber
public import WeilConjectures.Mathlib.AlgebraicGeometry.Scheme
public import WeilConjectures.Mathlib.Topology.Category.TopCat.Opens
public import WeilConjectures.Mathlib.Topology.Sheaves.Stalks

/-!
# Sections, stalks, restrictions and fibres of `𝒪_X`-modules

This file collects six groups of results about sheaves of modules over a scheme.

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
morphism** and the **global sections `Γ(X_y, F_y)` on a fibre**. Since Mathlib has no module
structure on the stalk of a sheaf of modules, the fibre is
defined not as `F_x ⊗_{𝒪_{X,x}} κ(x)` but by pullback: `F(x)` is the module of global sections
of the pullback of `F` along `Spec κ(x) ⟶ X`. The two agree for quasi-coherent `F`. It is built on
a base change section, comparing global sections on `Spec S` with global sections on `Spec R`
after restriction of scalars along `φ : R ⟶ S`.

The fifth is **base change for the direct image**: for a commutative square `v ≫ f = g ≫ u` of
schemes, the pullbacks along the two sides are compared by an isomorphism `g^* u^* ≅ v^* f^*`,
and the mate of that comparison is the base change transformation `u^* f_* ⟶ g_* v^*`. Applied
to the fibre square of `f : X ⟶ Y` over `y : Y` and evaluated on global sections, this is the
base change map `(f_* F)(y) ⟶ Γ(X_y, F_y)`.

The sixth concerns a scheme `X` **with at most one point**, such as the spectrum of a field. The
only open subsets of such an `X` are `⊥` and `⊤`, and all sections over `⊥` vanish, so a morphism
of `𝒪ₓ`-modules is an isomorphism as soon as it is one on global sections. In particular a global
section `m` of `M` such that `r ↦ r • m` is bijective trivialises `M`.

## Main definitions

- `AlgebraicGeometry.Scheme.structureModules`: the structure sheaf of a scheme, as a sheaf of
  modules over itself.
- `AlgebraicGeometry.Scheme.Modules.fiberFunctor`, `AlgebraicGeometry.Scheme.Modules.fiber`: the
  fibre `F(x)` of a sheaf of `𝒪_X`-modules at a point `x`, as a `κ(x)`-vector space, and its
  functoriality `AlgebraicGeometry.Scheme.Modules.fiberMap` in `F`.
- `AlgebraicGeometry.Scheme.Modules.restrictToFiber`: the restriction `F ↦ F_y` of sheaves of
  modules to the scheme-theoretic fibre of a morphism over a point.
- `AlgebraicGeometry.Scheme.Modules.fiberSectionsFunctor`,
  `AlgebraicGeometry.Scheme.Modules.fiberSections`: the global sections `Γ(X_y, F_y)` on the
  scheme-theoretic fibre, as a `κ(y)`-vector space.
- `AlgebraicGeometry.Scheme.Modules.moduleStalkBase`: the module structure on a stalk of a sheaf
  of `𝒪_X`-modules over the local ring of the base of a morphism `f : X ⟶ Y`.
- `AlgebraicGeometry.Scheme.Modules.pullbackTwoSquare`,
  `AlgebraicGeometry.Scheme.Modules.baseChange`: the comparison of pullbacks around a commutative
  square of schemes, and its mate, the base change transformation `u^* f_* ⟶ g_* v^*`.
- `AlgebraicGeometry.Scheme.Modules.fiberBaseChangeMap`: **the base change map**
  `(f_* F)(y) ⟶ Γ(X_y, F_y)`, the specialisation of `baseChange` to a fibre square, on global
  sections.
- `AlgebraicGeometry.Scheme.Modules.homOfSectionTop`: the morphism `𝒪ₓ ⟶ M` determined by a global
  section of `M`.

## Main results

- `AlgebraicGeometry.Scheme.Modules.range_map_kernelι`
- `AlgebraicGeometry.Scheme.Modules.germₗ`: the germ map `Γ(F, U) →ₗ[Γ(X, U)] F_x`.
- `AlgebraicGeometry.Scheme.Modules.pushforwardCompRestrictFunctorIso`
- `AlgebraicGeometry.Scheme.Modules.restrictFunctorCompMorphismRestrictIso`
- `AlgebraicGeometry.Scheme.Modules.overEquivInverseRestrictIso`
- `AlgebraicGeometry.Scheme.Modules.pullbackUnitIso`
- `AlgebraicGeometry.Scheme.Modules.pullbackOver`
- `AlgebraicGeometry.Scheme.Modules.pullbackOverObjIso`
- `AlgebraicGeometry.Scheme.Modules.Hom.naturality`: a morphism of sheaves of modules commutes
  with the restriction maps.
- `AlgebraicGeometry.Scheme.Modules.sectionsPullback_naturality`: the pullback
  `Γ(N, ⊤) ⟶ Γ(a^* N, ⊤)` of global sections along `a : X ⟶ Y` is natural in `N`.
- `AlgebraicGeometry.Scheme.Modules.pullbackTriangle`: the pullback functors along a commuting
  triangle `h ≫ v = u`, namely `v^* ⋙ h^* ≅ u^*`, together with its compatibility
  `AlgebraicGeometry.Scheme.Modules.pullbackTriangle_hom_app_sectionsPullback` with the pullback
  of global sections and its compatibility
  `AlgebraicGeometry.Scheme.Modules.pullbackTriangle_comp_hom` with stacking two triangles.
- `AlgebraicGeometry.Scheme.Modules.moduleSpecΓPushforwardIso`,
  `AlgebraicGeometry.Scheme.Modules.moduleSpecΓPullbackIso`: base change of the global sections
  of a sheaf of modules on `Spec S` along `φ : R ⟶ S`.
- `AlgebraicGeometry.Scheme.Modules.fiberFunctorPullbackIso`,
  `AlgebraicGeometry.Scheme.Modules.fiberPullbackIso`: compatibility of the fibre with pullback,
  for a morphism `u` inducing an isomorphism on residue fields at the point in question.
- `AlgebraicGeometry.Scheme.Modules.fiberRestrictToFiberIso`: the fibre of `F_y` at a point `x`
  of the fibre is the fibre of `F` at `f.fiberι y x`.
- `AlgebraicGeometry.Scheme.Modules.map_baseChange_comp_counit`: the mate identity satisfied by
  the base change transformation.
- `AlgebraicGeometry.Scheme.Modules.fiberBaseChangeMap_naturality`: naturality of the base change
  map in the sheaf.
- `AlgebraicGeometry.Scheme.Modules.isIso_of_isIso_app_top`,
  `AlgebraicGeometry.Scheme.Modules.isIso_homOfSectionTop`: on a scheme with at most one point, a
  morphism of `𝒪ₓ`-modules which is an isomorphism on global sections is an isomorphism, and a
  generating global section trivialises the module.

## Blueprint

The fibre and the restriction to a fibre are notion **(N2)** of `sec:cube-cost`, the formalisation
count of the theorem-of-the-cube chapter. The remaining half of (N2) — the compatibility of the
fibre with tensor products and with inverses of line bundles, and the one-dimensionality of the
fibre of an invertible sheaf — is in `WeilConjectures.AlgebraicGeometry.Modules.Fiber`: it needs
the monoidal structure on sheaves of modules and the notion of an invertible sheaf, which a file
under `WeilConjectures/Mathlib/` may not import.
-/
@[expose] public section

universe u

open CategoryTheory Limits Opposite SheafOfModules TopologicalSpace

namespace AlgebraicGeometry

/-- The structure sheaf `𝒪_X` of a scheme `X`, as a sheaf of modules over itself: the tensor
unit of `X.Modules`.

The abbreviation is needed because dot notation on `SheafOfModules.unit X.ringCatSheaf`
resolves in `SheafOfModules _` rather than in `X.Modules`. -/
noncomputable abbrev Scheme.structureModules (X : Scheme.{u}) : X.Modules :=
  SheafOfModules.unit X.ringCatSheaf

namespace Scheme.Modules

section Restriction

variable {X : Scheme.{u}} {M N : X.Modules}

/-- A morphism of sheaves of modules commutes with the restriction maps: for `i : U ⟶ V`,

```
Γ(M, V) --- φ.app V ---> Γ(N, V)
   |                        |
  res                      res
   v                        v
Γ(M, U) --- φ.app U ---> Γ(N, U)
```
-/
@[reassoc (attr := simp)]
lemma Hom.naturality (φ : M ⟶ N) {U V : X.Opens} (i : U ⟶ V) :
    M.presheaf.map i.op ≫ φ.app U = φ.app V ≫ N.presheaf.map i.op :=
  φ.mapPresheaf.naturality i.op

/-- Elementwise version of `AlgebraicGeometry.Scheme.Modules.Hom.naturality`: applying a
morphism of sheaves of modules commutes with restricting a section. -/
lemma Hom.naturality_apply (φ : M ⟶ N) {U V : X.Opens} (i : U ⟶ V) (s : Γ(M, V)) :
    φ.app U (M.presheaf.map i.op s) = N.presheaf.map i.op (φ.app V s) :=
  ConcreteCategory.congr_hom (φ.naturality i) s

end Restriction

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

noncomputable section StalkDesc

variable {X : Scheme.{u}} (G : X.Modules) (x : X) (A : Ab.{u})
  (c : ∀ U : X.Opens, x ∈ U → (Γ(G, U) ⟶ A))
  (hc : ∀ (U V : X.Opens) (hU : x ∈ U) (hV : x ∈ V) (i : op U ⟶ op V),
    G.presheaf.map i ≫ c V hV = c U hU)
  {S : CommRingCat.{u}} (φ : X.presheaf.stalk x ⟶ S) [Module S A]
  (hφ : ∀ (U : X.Opens) (hU : x ∈ U) (r : Γ(X, U)) (s : Γ(G, U)),
    c U hU (r • s) = φ (X.presheaf.germ U x hU r) • c U hU s)

include hφ in
/-- The map out of the stalk of `G` at `x` given by a family of maps which is semilinear over a
ring map `φ : 𝒪_{X, x} ⟶ S` is itself semilinear over `φ`. -/
lemma stalkDesc_smul (r : X.presheaf.stalk x) (z : G.presheaf.stalk x) :
    G.presheaf.stalkDesc x A c hc (r • z) = φ r • G.presheaf.stalkDesc x A c hc z := by
  obtain ⟨U, hU, s, rfl⟩ := G.presheaf.exists_germ_eq z
  obtain ⟨V, hV, r₀, rfl⟩ := X.presheaf.exists_germ_eq r
  rw [← X.presheaf.germ_res_apply (homOfLE inf_le_right : U ⊓ V ⟶ V) x ⟨hU, hV⟩ r₀,
    ← G.presheaf.germ_res_apply (homOfLE inf_le_left : U ⊓ V ⟶ U) x ⟨hU, hV⟩ s,
    ← germ_smul, TopCat.Presheaf.stalkDesc_germ, TopCat.Presheaf.stalkDesc_germ, hφ]

/-- The `𝒪_{X, x}`-linear map out of the stalk of `G` at `x` induced by a compatible family of
maps out of the sections of `G` over the open neighbourhoods of `x` which is semilinear over a
ring map `φ : 𝒪_{X, x} ⟶ S`. -/
def stalkDescₗ :
    G.presheaf.stalk x →ₗ[X.presheaf.stalk x]
      (ModuleCat.restrictScalars φ.hom).obj (ModuleCat.of S A) where
  toFun := G.presheaf.stalkDesc x A c hc
  map_add' := map_add _
  map_smul' := stalkDesc_smul G x A c hc φ hφ

@[simp]
lemma stalkDescₗ_apply (z : G.presheaf.stalk x) :
    stalkDescₗ G x A c hc φ hφ z = G.presheaf.stalkDesc x A c hc z := rfl

include hφ in
/-- Composing the linear map out of the stalk with a semilinear map of the targets is the linear
map out of the stalk for the composed family.

This is stated for a variable `G` so that it can be instantiated at a concrete sheaf of modules
without the kernel having to redo the argument by `TopCat.Presheaf.stalk_hom_ext` there. -/
lemma ofSemilinear_comp_stalkDescₗ {S' : CommRingCat.{u}} (ψ : X.presheaf.stalk x ⟶ S')
    (A' : Ab.{u}) [Module S' A'] (c' : ∀ U : X.Opens, x ∈ U → (Γ(G, U) ⟶ A'))
    (hc' : ∀ (U V : X.Opens) (hU : x ∈ U) (hV : x ∈ V) (i : op U ⟶ op V),
      G.presheaf.map i ≫ c' V hV = c' U hU)
    (hψ : ∀ (U : X.Opens) (hU : x ∈ U) (r : Γ(X, U)) (s : Γ(G, U)),
      c' U hU (r • s) = ψ (X.presheaf.germ U x hU r) • c' U hU s)
    (g : A ⟶ A') (hg : ∀ (r : X.presheaf.stalk x) (a : A), g (φ r • a) = ψ r • g a)
    (hgc : ∀ (U : X.Opens) (hU : x ∈ U), c U hU ≫ g = c' U hU) :
    (ModuleCat.ofSemilinear φ ψ g hg).hom.comp (stalkDescₗ G x A c hc φ hφ) =
      stalkDescₗ G x A' c' hc' ψ hψ := by
  have hcomp : G.presheaf.stalkDesc x A c hc ≫ g = G.presheaf.stalkDesc x A' c' hc' :=
    TopCat.Presheaf.stalk_hom_ext _ fun U hU ↦ by
      rw [← Category.assoc, TopCat.Presheaf.germ_comp_stalkDesc,
        TopCat.Presheaf.germ_comp_stalkDesc, hgc]
  exact LinearMap.ext fun z ↦ (ModuleCat.ofSemilinear_apply _ _ g hg _).trans
    ((ConcreteCategory.comp_apply (G.presheaf.stalkDesc x A c hc) g z).symm.trans
      (ConcreteCategory.congr_hom hcomp z))

end StalkDesc
section StalkBase

variable {X Y : Scheme.{u}}

/-- The module structure on the stalk `F_x` of a sheaf of `𝒪_X`-modules over the local ring
`𝒪_{Y, f x}` of the base of `f : X ⟶ Y`, by restriction of scalars along `f.stalkMap x`.

This is the companion of `AlgebraicGeometry.Scheme.Modules.moduleStalk`, which is the case of
the identity morphism: there the scalars are the local ring of `X` itself. -/
@[instance_reducible]
noncomputable def moduleStalkBase (F : X.Modules) (f : X ⟶ Y) (x : X) :
    Module (Y.presheaf.stalk (f.base x)) (F.presheaf.stalk x) :=
  Module.compHom _ (f.stalkMap x).hom

end StalkBase

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
    (pullback f).obj Y.structureModules ≅ X.structureModules :=
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

variable {X Y Z : Scheme.{u}} (a : X ⟶ Y) (b : Y ⟶ Z) (N : Y.Modules) (M : Z.Modules)

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

lemma pushforwardPullbackComp_app (V : Z.Opens) :
    (pushforwardPullbackComp a b M).app V =
      ((pullbackPushforwardAdjunction a).unit.app ((pullback b).obj M)).app (b ⁻¹ᵁ V) ≫
        ((pullbackComp a b).hom.app M).app ((a ≫ b) ⁻¹ᵁ V) := by
  simp [pushforwardPullbackComp]

/-- The unit of the adjunction `(𝟙 X)^* ⊣ (𝟙 X)_*` is the identification of `N` with
`(𝟙 X)_* (𝟙 X)^* N`. -/
@[reassoc (attr := simp)]
lemma unit_pushforwardId :
    (pullbackPushforwardAdjunction (𝟙 Y)).unit.app N ≫
        (pushforward (𝟙 Y)).map ((pullbackId Y).hom.app N) = (pushforwardId Y).inv.app N := by
  have h := unit_conjugateEquiv .id (pullbackPushforwardAdjunction (𝟙 Y)) (pullbackId Y).hom N
  rw [conjugateEquiv_pullbackId_hom] at h
  simpa using h.symm

/-- The sections of `a_* M` over `U` are the sections of `M` over `a ⁻¹ᵁ U` by definition, so
the identification of the two is the identity.

It is nevertheless spelled out in `AlgebraicGeometry.Scheme.Modules.sectionsPullbackLE`: letting
the two be identified silently makes elaboration unfold the scheme `a ⁻¹ᵁ U` is an open subset
of, which is expensive when that scheme is a pullback. -/
lemma eqToHom_pushforward_obj_obj (P : X.Modules) (U : Y.Opens) :
    eqToHom (pushforward_obj_obj a P U) = 𝟙 Γ((pushforward a).obj P, U) := rfl

/-- The identification of `Γ(a_* P, U)` with `Γ(P, a ⁻¹ᵁ U)` is compatible with restriction; see
`AlgebraicGeometry.Scheme.Modules.eqToHom_pushforward_obj_obj` for why it is spelled out. -/
lemma eqToHom_pushforward_map (P : X.Modules) {U U' : Y.Opens} (i : op U' ⟶ op U) :
    ((pushforward a).obj P).presheaf.map i ≫ eqToHom (pushforward_obj_obj a P U) =
      eqToHom (pushforward_obj_obj a P U') ≫
        P.presheaf.map ((Opens.map a.base).map i.unop).op := rfl

/-- The pullback of sections along `a : X ⟶ Y`, from an open `U` of `Y` to an open `V` of `X`
contained in `a ⁻¹ᵁ U`: the image of a section under the unit `N ⟶ a_* a^* N`, read as a section
of `a^* N` over `a ⁻¹ᵁ U` and restricted to `V`. -/
def sectionsPullbackLE {U : Y.Opens} {V : X.Opens} (h : V ≤ a ⁻¹ᵁ U) :
    Γ(N, U) ⟶ Γ((pullback a).obj N, V) :=
  ((pullbackPushforwardAdjunction a).unit.app N).app U ≫
    eqToHom (pushforward_obj_obj a ((pullback a).obj N) U) ≫
    ((pullback a).obj N).presheaf.map (homOfLE h).op

/-- Restricting further after pulling back is pulling back to the smaller open:

```
                  sectionsPullbackLE a N h
  Γ(N, U) ------------------------------------> Γ(a^* N, V)
         ╲                                            |
          ╲  sectionsPullbackLE a N (h' : V' ≤ V ≤ ..)| (a^* N).presheaf.map i
           ╲                                          v
            ────────────────────────────────> Γ(a^* N, V')
```
-/
@[reassoc]
lemma sectionsPullbackLE_map {U : Y.Opens} {V V' : X.Opens} (h : V ≤ a ⁻¹ᵁ U) (i : op V ⟶ op V') :
    sectionsPullbackLE a N h ≫ ((pullback a).obj N).presheaf.map i =
      sectionsPullbackLE a N (i.unop.le.trans h) := by
  rw [sectionsPullbackLE, sectionsPullbackLE, Category.assoc, Category.assoc,
    ← Functor.map_comp]
  congr 1

/-- Pulling back the restriction of a section is the pullback of the section:

```
  Γ(N, U) --- sectionsPullbackLE a N h ---> Γ(a^* N, V)
     |                                            ^
     | N.presheaf.map i                          ╱
     v                                          ╱ sectionsPullbackLE a N h'
  Γ(N, U') ────────────────────────────────────
```
-/
@[reassoc]
lemma map_sectionsPullbackLE {U U' : Y.Opens} {V : X.Opens} (h : V ≤ a ⁻¹ᵁ U) (i : op U' ⟶ op U) :
    N.presheaf.map i ≫ sectionsPullbackLE a N h =
      sectionsPullbackLE a N (h.trans ((Opens.map a.base).map i.unop).le) := by
  have hnat := ((pullbackPushforwardAdjunction a).unit.app N).mapPresheaf.naturality i
  simp only [mapPresheaf_app, Functor.id_obj, Functor.comp_obj] at hnat
  rw [sectionsPullbackLE, sectionsPullbackLE, ← Category.assoc, ← Category.assoc, hnat,
    Category.assoc, Category.assoc]
  congr 1
  rw [← Category.assoc, eqToHom_pushforward_map, Category.assoc, ← Functor.map_comp]
  congr 1

/-- The pullback of sections is semilinear over `AlgebraicGeometry.Scheme.Hom.appLE`. -/
lemma sectionsPullbackLE_smul {U : Y.Opens} {V : X.Opens} (h : V ≤ a ⁻¹ᵁ U)
    (r : Γ(Y, U)) (r' : Γ(X, V)) (hr : a.appLE U V h r = r') (s : Γ(N, U)) :
    sectionsPullbackLE a N h (r • s) = r' • sectionsPullbackLE a N h s := by
  subst hr
  rw [Scheme.Hom.appLE, ConcreteCategory.comp_apply, sectionsPullbackLE]
  simp only [ConcreteCategory.comp_apply, Functor.id_obj, Functor.comp_obj, Hom.app_smul,
    eqToHom_pushforward_smul, map_smul]

/-- Pulling a section back along the identity is restricting it:

```
                  sectionsPullbackLE (𝟙 Y) N h
  Γ(N, U) ---------------------------------------> Γ((𝟙 Y)^* N, V)
         ╲                                                |
          ╲  N.presheaf.map (homOfLE h').op               | (pullbackId Y).hom.app N at V
           ╲                                              v
            ──────────────────────────────────────> Γ(N, V)
```
-/
@[reassoc]
lemma sectionsPullbackLE_id {U V : Y.Opens} (h : V ≤ (𝟙 Y) ⁻¹ᵁ U) (h' : V ≤ U) :
    sectionsPullbackLE (𝟙 Y) N h ≫ ((pullbackId Y).hom.app N).app V =
      N.presheaf.map (homOfLE h').op := by
  have hu := congrArg (fun φ ↦ Hom.app φ U) (unit_pushforwardId N)
  simp only [Hom.comp_app, pushforwardId_inv_app_app] at hu
  simp only [pushforward_map_app] at hu
  have hu' : (Hom.app ((pullbackPushforwardAdjunction (𝟙 Y)).unit.app N) U ≫
      eqToHom (pushforward_obj_obj (𝟙 Y) ((pullback (𝟙 Y)).obj N) U)) ≫
      Hom.app ((pullbackId Y).hom.app N) (𝟙 Y ⁻¹ᵁ U) = 𝟙 Γ(N, U) := hu
  rw [sectionsPullbackLE, Category.assoc, Category.assoc, Hom.naturality, ← Category.assoc,
    ← Category.assoc, hu', Category.id_comp]
  exact congrArg N.presheaf.map (Subsingleton.elim _ _)

/-- Pulling a section back to the full preimage in two steps agrees with pulling it back in
one:

```
             sectionsPullbackLE b M le_rfl
  Γ(M, U) ---------------------------------> Γ(b^* M, b ⁻¹ᵁ U)
         ╲                                          |
          ╲                                         | sectionsPullbackLE a (b^* M) le_rfl
           ╲ sectionsPullbackLE (a ≫ b) M le_rfl    v
            ╲                       Γ(a^* (b^* M), a ⁻¹ᵁ b ⁻¹ᵁ U)
             ╲                                      |
              ╲                                     | (pullbackComp a b).hom.app M
               ─────────────────────────> Γ((a ≫ b)^* M, (a ≫ b) ⁻¹ᵁ U)
```
-/
@[reassoc]
lemma sectionsPullbackLE_comp_pullbackComp_app (U : Z.Opens) :
    sectionsPullbackLE b M (le_refl (b ⁻¹ᵁ U)) ≫
        sectionsPullbackLE a ((pullback b).obj M) (le_refl (a ⁻¹ᵁ (b ⁻¹ᵁ U))) ≫
          ((pullbackComp a b).hom.app M).app (a ⁻¹ᵁ (b ⁻¹ᵁ U)) =
      sectionsPullbackLE (a ≫ b) M (le_refl ((a ≫ b) ⁻¹ᵁ U)) := by
  have h := congrArg (fun φ ↦ Hom.app φ U) (unit_pushforwardPullbackComp a b M)
  simp only [Hom.comp_app, pushforwardPullbackComp_app] at h
  simp only [sectionsPullbackLE, homOfLE_refl, op_id, CategoryTheory.Functor.map_id,
    Category.comp_id]
  rw [eqToHom_pushforward_obj_obj b ((pullback b).obj M) U,
    eqToHom_pushforward_obj_obj a ((pullback a).obj ((pullback b).obj M)) (b ⁻¹ᵁ U),
    eqToHom_pushforward_obj_obj (a ≫ b) ((pullback (a ≫ b)).obj M) U]
  simpa using h

/-- Pulling a section back in two steps agrees with pulling it back in one:

```
                sectionsPullbackLE b M h₁
  Γ(M, U) ---------------------------------> Γ(b^* M, V)
         ╲                                         |
          ╲                                        | sectionsPullbackLE a (b^* M) h₂
           ╲ sectionsPullbackLE (a ≫ b) M h₃       v
            ╲                                Γ(a^* (b^* M), V')
             ╲                                     |
              ╲                                    | (pullbackComp a b).hom.app M at V'
               ────────────────────────────> Γ((a ≫ b)^* M, V')
```
-/
@[reassoc]
lemma sectionsPullbackLE_comp {U : Z.Opens} {V : Y.Opens} {V' : X.Opens}
    (h₁ : V ≤ b ⁻¹ᵁ U) (h₂ : V' ≤ a ⁻¹ᵁ V) (h₃ : V' ≤ (a ≫ b) ⁻¹ᵁ U) :
    sectionsPullbackLE b M h₁ ≫ sectionsPullbackLE a ((pullback b).obj M) h₂ ≫
        ((pullbackComp a b).hom.app M).app V' =
      sectionsPullbackLE (a ≫ b) M h₃ := by
  rw [← sectionsPullbackLE_map b M (le_refl (b ⁻¹ᵁ U)) (homOfLE h₁).op, Category.assoc,
    map_sectionsPullbackLE_assoc,
    ← sectionsPullbackLE_map a ((pullback b).obj M) (le_refl (a ⁻¹ᵁ (b ⁻¹ᵁ U)))
      (homOfLE (h₂.trans ((Opens.map a.base).map (homOfLE h₁)).le)).op,
    Category.assoc, Hom.naturality, sectionsPullbackLE_comp_pullbackComp_app_assoc,
    sectionsPullbackLE_map]

/-- Pulling back sections along equal morphisms:

```
                sectionsPullbackLE c N hc
  Γ(N, U) ---------------------------------> Γ(c^* N, V)
         ╲                                         |
          ╲  sectionsPullbackLE d N hd             | (pullbackCongr hcd).hom.app N at V
           ╲                                       v
            ───────────────────────────────> Γ(d^* N, V)
```
-/
lemma sectionsPullbackLE_congr {c d : X ⟶ Y} (hcd : c = d) {U : Y.Opens} {V : X.Opens}
    (hc : V ≤ c ⁻¹ᵁ U) (hd : V ≤ d ⁻¹ᵁ U) :
    sectionsPullbackLE c N hc ≫ ((pullbackCongr hcd).hom.app N).app V =
      sectionsPullbackLE d N hd := by
  subst hcd
  simp [pullbackCongr]

/-- The pullback of global sections along a morphism of schemes: the image of a global section
of `N` under the unit `N ⟶ a_* a^* N`, read as a global section of `a^* N`. -/
def sectionsPullback : Γ(N, ⊤) ⟶ Γ((pullback a).obj N, ⊤) :=
  sectionsPullbackLE a N (by simp : (⊤ : X.Opens) ≤ a ⁻¹ᵁ ⊤)

/-- The pullback of global sections is semilinear over the pullback of functions. -/
lemma sectionsPullback_smul (r : Γ(Y, ⊤)) (s : Γ(N, ⊤)) :
    sectionsPullback a N (r • s) = a.appTop r • sectionsPullback a N s :=
  sectionsPullbackLE_smul a N _ r _ (Scheme.Hom.appLE_eq_appTop a _ ▸ rfl) s

/-- The pullback of a global section is the image of the section under the unit of the
adjunction, restricted from `a ⁻¹ᵁ ⊤` to `⊤`. -/
lemma sectionsPullback_apply {X' Y' : Scheme.{u}} (a : X' ⟶ Y') (N : Y'.Modules) (s : Γ(N, ⊤))
    (i : (⊤ : X'.Opens) ⟶ a ⁻¹ᵁ ⊤) :
    sectionsPullback a N s =
      ((pullback a).obj N).presheaf.map i.op
        (((pullbackPushforwardAdjunction a).unit.app N).app ⊤ s) :=
  rfl

/-- **The pullback of global sections is natural in the sheaf of modules.** For `a : X' ⟶ Y'`
and `φ : N ⟶ N'`, the square

```
    Γ(N, ⊤)  ------------- φ.app ⊤ ------------->  Γ(N', ⊤)
       |                                              |
sectionsPullback a N                       sectionsPullback a N'
       v                                              v
Γ(a ^* N, ⊤) -- ((pullback a).map φ).app ⊤ --> Γ(a ^* N', ⊤)
```

commutes. -/
@[reassoc]
lemma sectionsPullback_naturality {X' Y' : Scheme.{u}} (a : X' ⟶ Y') {N N' : Y'.Modules}
    (φ : N ⟶ N') :
    sectionsPullback a N ≫ ((pullback a).map φ).app ⊤ = φ.app ⊤ ≫ sectionsPullback a N' := by
  ext s
  have h := ConcreteCategory.congr_hom
    congr(Hom.app $(((pullbackPushforwardAdjunction a).unit.naturality φ).symm) ⊤) s
  simp only [Functor.comp_map, Functor.id_map, Hom.comp_app, ConcreteCategory.comp_apply,
    pushforward_map_app] at h
  simp only [ConcreteCategory.comp_apply,
    sectionsPullback_apply a N s (homOfLE (by simp)),
    sectionsPullback_apply a N' _ (homOfLE (by simp)), Hom.naturality_apply]
  exact congrArg _ h

/-- Elementwise version of
`AlgebraicGeometry.Scheme.Modules.sectionsPullback_naturality`. -/
lemma sectionsPullback_naturality_apply {X' Y' : Scheme.{u}} (a : X' ⟶ Y') {N N' : Y'.Modules}
    (φ : N ⟶ N') (s : Γ(N, ⊤)) :
    ((pullback a).map φ).app ⊤ (sectionsPullback a N s) = sectionsPullback a N' (φ.app ⊤ s) :=
  ConcreteCategory.congr_hom (sectionsPullback_naturality a φ) s

/-- The pullback of sections is natural in the sheaf of modules:

```
  Γ(N, U) --- sectionsPullbackLE a N h ---> Γ(a^* N, V)
     |                                            |
     | ψ.app U                                    | ((pullback a).map ψ).app V
     v                                            v
  Γ(N', U) --- sectionsPullbackLE a N' h --> Γ(a^* N', V)
```
-/
@[reassoc]
lemma sectionsPullbackLE_naturality {N' : Y.Modules} (ψ : N ⟶ N') {U : Y.Opens} {V : X.Opens}
    (h : V ≤ a ⁻¹ᵁ U) :
    ψ.app U ≫ sectionsPullbackLE a N' h =
      sectionsPullbackLE a N h ≫ ((pullback a).map ψ).app V := by
  have hnat := congrArg (fun φ ↦ Hom.app φ U) ((pullbackPushforwardAdjunction a).unit.naturality ψ)
  simp only [Hom.comp_app, Functor.id_map, Functor.comp_map, pushforward_map_app] at hnat
  rw [sectionsPullbackLE, sectionsPullbackLE, ← Category.assoc, ← Category.assoc, hnat]
  simp only [Category.assoc]
  rw [Hom.naturality]
  rfl

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
  simp only [sectionsPullback, sectionsPullbackLE, ConcreteCategory.comp_apply,
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

/-!
## Pulling back sections along a morphism over a base
-/

noncomputable section PullbackOver

variable {X X' X'' W : Scheme.{u}}

/-- The pullback of global sections along a morphism `u : X ⟶ X'` over a fixed base `W`: a
global section of the pullback of `F` to `X'` gives a global section of the pullback of `F` to
`X`, using that `u ≫ p' = p`.

This is the form in which the pullback of sections is functorial, by
`AlgebraicGeometry.Scheme.Modules.sectionsPullbackOver_id` and
`AlgebraicGeometry.Scheme.Modules.sectionsPullbackOver_comp`. -/
def sectionsPullbackOver (u : X ⟶ X') {p : X ⟶ W} {p' : X' ⟶ W}
    (hu : u ≫ p' = p) (F : W.Modules) :
    Γ((pullback p').obj F, ⊤) ⟶ Γ((pullback p).obj F, ⊤) :=
  sectionsPullback u ((pullback p').obj F) ≫
    ((pullbackComp u p').hom.app F).app ⊤ ≫ ((pullbackCongr hu).hom.app F).app ⊤

/-- The pullback of global sections over a base is semilinear over
`AlgebraicGeometry.Scheme.Hom.appTop`.

This is stated for a variable `u` so that it can be instantiated at a concrete morphism without
the kernel having to redo the element-level rewriting there. -/
lemma sectionsPullbackOver_smul (u : X ⟶ X') {p : X ⟶ W} {p' : X' ⟶ W} (hu : u ≫ p' = p)
    (F : W.Modules) (r : Γ(X', ⊤)) (r' : Γ(X, ⊤)) (hr : u.appTop r = r')
    (s : Γ((pullback p').obj F, ⊤)) :
    sectionsPullbackOver u hu F (r • s) = r' • sectionsPullbackOver u hu F s := by
  simp only [sectionsPullbackOver, ConcreteCategory.comp_apply, sectionsPullback_smul, hr,
    Functor.comp_obj, Hom.app_smul]

/-- Pulling back sections along the identity is the identity. -/
@[simp]
lemma sectionsPullbackOver_id {p : X ⟶ W} (hu : 𝟙 X ≫ p = p) (F : W.Modules) :
    sectionsPullbackOver (𝟙 X) hu F = 𝟙 _ := by
  have key : ((pullbackComp (𝟙 X) p).hom.app F) ≫ ((pullbackCongr hu).hom.app F)
      = (pullbackId X).hom.app ((pullback p).obj F) := by
    have h := pseudofunctor_right_unitality (f := p)
    rw [Iso.inv_comp_eq] at h
    have h2 := congrArg (fun φ ↦ NatTrans.app φ F) h
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.rightUnitor_hom_app] at h2
    rw [pullbackCongr]
    simpa using h2.symm
  rw [sectionsPullbackOver, ← Hom.comp_app, key, sectionsPullback,
    sectionsPullbackLE_id _ _ le_rfl]
  simp

/-- Pulling back sections over a base in two steps agrees with pulling them back in one:

```
                     sectionsPullbackOver u' hu' F
  Γ(p''^* F, ⊤) -----------------------------------> Γ(p'^* F, ⊤)
               ╲                                            |
                ╲  sectionsPullbackOver (u ≫ u') _ F        | sectionsPullbackOver u hu F
                 ╲                                          v
                  ────────────────────────────────> Γ(p^* F, ⊤)
```
-/
lemma sectionsPullbackOver_comp (u : X ⟶ X') (u' : X' ⟶ X'') {p : X ⟶ W} {p' : X' ⟶ W}
    {p'' : X'' ⟶ W} (hu : u ≫ p' = p) (hu' : u' ≫ p'' = p') (F : W.Modules) :
    sectionsPullbackOver u' hu' F ≫ sectionsPullbackOver u hu F =
      sectionsPullbackOver (u ≫ u') (by rw [Category.assoc, hu', hu]) F := by
  subst hu'
  subst hu
  simp only [sectionsPullbackOver, sectionsPullback, pullbackCongr, eqToIso_refl, Iso.refl_hom,
    NatTrans.id_app, Hom.id_app, Category.comp_id, Category.assoc]
  rw [← sectionsPullbackLE_comp u u' ((pullback p'').obj F)
      (by simp : (⊤ : X'.Opens) ≤ u' ⁻¹ᵁ ⊤) (by simp : (⊤ : X.Opens) ≤ u ⁻¹ᵁ ⊤) (by simp),
    sectionsPullbackLE_naturality_assoc]
  have key := congrArg (fun φ ↦ NatTrans.app φ F)
    (pseudofunctor_associativity (f := u) (g := u') (h := p''))
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Category.id_comp, eqToHom_refl] at key
  have hZ := congrArg ((pullbackComp u (u' ≫ p'')).hom.app F ≫ ·) key
  simp only [← Category.assoc, ← NatTrans.comp_app, Iso.hom_inv_id, NatTrans.id_app,
    Category.id_comp, Category.comp_id] at hZ
  have key2 : (pullback u).map ((pullbackComp u' p'').hom.app F) ≫
        (pullbackComp u (u' ≫ p'')).hom.app F =
      (pullbackComp u u').hom.app ((pullback p'').obj F) ≫
        (pullbackComp (u ≫ u') p'').hom.app F := by
    refine (congrArg ((pullback u).map ((pullbackComp u' p'').hom.app F) ≫ ·) hZ.symm).trans ?_
    simp
  simp only [Functor.comp_obj, Category.assoc, ← Hom.comp_app]
  rw [key2]

end PullbackOver

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

section Comp

variable {W : Scheme.{u}} {h₁ : W ⟶ X} {h₂ : X ⟶ Y} {u₂ : X ⟶ Z} {u₁ : W ⟶ Z}

/-- **Stacking two commuting triangles**: for `h₂ ≫ v = u₂` and `h₁ ≫ u₂ = u₁`, so that

```
            h₁            h₂
      W ─────────→ X ─────────→ Y
        ╲          │           ╱
      u₁ ╲      u₂ │          ╱ v
          ↘        ↓         ↙
                   Z
```

commutes, the isomorphism `h₁^* h₂^* v^* M ≅ u₁^* M` obtained from the two triangles agrees
with the one obtained from the outer triangle `(h₁ ≫ h₂) ≫ v = u₁`. This is the associativity
coherence `AlgebraicGeometry.Scheme.Modules.pseudofunctor_associativity` of the pullback
pseudofunctor. -/
lemma pullbackTriangle_comp_hom (w₂ : h₂ ≫ v = u₂) (w₁ : h₁ ≫ u₂ = u₁)
    (w : (h₁ ≫ h₂) ≫ v = u₁) :
    Functor.whiskerRight (pullbackTriangle w₂).hom (pullback h₁) ≫ (pullbackTriangle w₁).hom =
      (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft (pullback v) (pullbackComp h₁ h₂).hom ≫
          (pullbackTriangle w).hom := by
  subst w₂
  subst w₁
  have key := pseudofunctor_associativity (f := h₁) (g := h₂) (h := v)
  rw [Iso.inv_comp_eq, ← Functor.isoWhiskerRight_inv, Iso.inv_comp_eq] at key
  simp only [pullbackTriangle, Iso.trans_hom, pullbackCongr, eqToIso.hom, eqToHom_refl,
    Category.comp_id]
  rw [key]
  simp

/-- `Scheme.Modules.pullbackTriangle_comp_hom` evaluated at a single sheaf of modules `M`, and
for an arbitrary factorisation `k = h₁ ≫ h₂` of the composite: the two ways of identifying
`h₁^* h₂^* v^* M` with `u₁^* M` agree. -/
@[reassoc]
lemma pullbackTriangle_comp_hom_app {k : W ⟶ Y} (e : k = h₁ ≫ h₂) (w₂ : h₂ ≫ v = u₂)
    (w₁ : h₁ ≫ u₂ = u₁) (w : k ≫ v = u₁) (M : Z.Modules) :
    (pullback h₁).map ((pullbackTriangle w₂).hom.app M) ≫ (pullbackTriangle w₁).hom.app M =
      (pullbackComp h₁ h₂).hom.app ((pullback v).obj M) ≫
        (pullbackCongr e.symm).hom.app ((pullback v).obj M) ≫
          (pullbackTriangle w).hom.app M := by
  subst e
  simp only [pullbackCongr, eqToIso.hom, eqToHom_refl]
  simpa using NatTrans.congr_app (pullbackTriangle_comp_hom w₂ w₁ w) M

end Comp

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

/-- The global sections of a sheaf of modules on the scheme-theoretic fibre `X_y` of
`f : X ⟶ Y` over `y : Y`, as a functor to `κ(y)`-vector spaces: the fibre is a scheme over
`Spec κ(y)`, and this is the direct image along that structure morphism, evaluated at the top
open. -/
noncomputable def fiberSectionsFunctor (f : X ⟶ Y) (y : Y) :
    (f.fiber y).Modules ⥤ ModuleCat (Y.residueField y) :=
  pushforward (f.fiberToSpecResidueField y) ⋙ moduleSpecΓFunctor (R := Y.residueField y)

/-- The `κ(y)`-vector space `Γ(X_y, F_y)` of global sections of the restriction of a sheaf of
`𝒪_X`-modules `F` to the fibre of `f : X ⟶ Y` over `y : Y`. -/
noncomputable abbrev fiberSections (f : X ⟶ Y) (F : X.Modules) (y : Y) :
    ModuleCat (Y.residueField y) :=
  (fiberSectionsFunctor f y).obj ((restrictToFiber f y).obj F)

end Fiber

section BaseChangeSquare

variable {X Y S T : Scheme.{u}} {v : X ⟶ Y} {f : Y ⟶ T} {g : X ⟶ S} {u : S ⟶ T}

/-- **The comparison of pullbacks around a commutative square** `v ≫ f = g ≫ u` of schemes:
pulling back along `u` and then along `g` is pulling back along `f` and then along `v`.

```
            v
      X ─────────→ Y                X.Modules ←─── v^* ─── Y.Modules
      │            │                    ↑                      ↑
    g │            │ f              g^* │          ⟸           │ f^*
      ↓            ↓                    │                      │
      S ─────────→ T                S.Modules ←─── u^* ─── T.Modules
            u
```

It is an isomorphism (`AlgebraicGeometry.Scheme.Modules.isIso_natTrans_pullbackTwoSquare`), but
it is packaged as a 2-square so that the base change transformation
`AlgebraicGeometry.Scheme.Modules.baseChange` can be obtained as its mate. -/
noncomputable def pullbackTwoSquare (w : v ≫ f = g ≫ u) :
    TwoSquare (Modules.pullback u) (Modules.pullback f) (Modules.pullback g)
      (Modules.pullback v) :=
  TwoSquare.mk _ _ _ _
    ((pullbackComp g u).hom ≫ (pullbackCongr w.symm).hom ≫ (pullbackComp v f).inv)

/-- The comparison of pullbacks around a commutative square is an isomorphism: it is a composite
of isomorphisms. -/
instance isIso_natTrans_pullbackTwoSquare (w : v ≫ f = g ≫ u) :
    IsIso (pullbackTwoSquare w).natTrans :=
  inferInstanceAs (IsIso ((pullbackComp g u).hom ≫ (pullbackCongr w.symm).hom ≫
    (pullbackComp v f).inv))

/-- **The base change transformation** `u^* ∘ f_* ⟶ g_* ∘ v^*` attached to a commutative square
`v ≫ f = g ≫ u` of schemes: the mate of the comparison of pullbacks
`AlgebraicGeometry.Scheme.Modules.pullbackTwoSquare`.

```
   Y.Modules ─────── f_* ──────→ T.Modules
       │                             │
   v^* │              ⟹              │ u^*
       ↓                             ↓
   X.Modules ─────── g_* ──────→ S.Modules
```
-/
noncomputable def baseChange (w : v ≫ f = g ≫ u) :
    TwoSquare (pushforward f) (Modules.pullback v) (Modules.pullback u) (pushforward g) :=
  mateEquiv (pullbackPushforwardAdjunction f) (pullbackPushforwardAdjunction g)
    (pullbackTwoSquare w)

/-- **The mate identity for the base change transformation**: the base change map, pulled back
along `g` and followed by the counit of `g^* ⊣ g_*`, is the comparison of pullbacks followed by
the pullback along `v` of the counit of `f^* ⊣ f_*`.

```
   g^* u^* f_* M ─── g^*(bc) ───→ g^* g_* v^* M
         │                              │
         │ comparison                   │ ε_g
         ↓                              ↓
   v^* f^* f_* M ─── v^*(ε_f) ──→     v^* M
```
-/
@[reassoc]
lemma map_baseChange_comp_counit (w : v ≫ f = g ≫ u) (M : Y.Modules) :
    (Modules.pullback g).map ((baseChange w).natTrans.app M) ≫
        (pullbackPushforwardAdjunction g).counit.app ((Modules.pullback v).obj M) =
      (pullbackTwoSquare w).natTrans.app ((pushforward f).obj M) ≫
        (Modules.pullback v).map ((pullbackPushforwardAdjunction f).counit.app M) :=
  mateEquiv_counit _ _ _ M

end BaseChangeSquare

section FiberBaseChange

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (F : X.Modules) (y : Y)

/-- **The base change transformation for a scheme-theoretic fibre**: the specialisation of
`AlgebraicGeometry.Scheme.Modules.baseChange` to the fibre square of `f : X ⟶ Y` over `y : Y`.

```
   X.Modules ────────── f_* ─────────→ Y.Modules
       │                                   │
   v^* │                ⟹                  │ u^*
       ↓                                   ↓
 (X_y).Modules ─── g_* ───→ (Spec κ(y)).Modules
```

Here `v = f.fiberι y`, `u = Y.fromSpecResidueField y` and `g = f.fiberToSpecResidueField y`. -/
noncomputable abbrev fiberBaseChange :
    TwoSquare (pushforward f) (restrictToFiber f y)
      (Modules.pullback (Y.fromSpecResidueField y))
      (pushforward (f.fiberToSpecResidueField y)) :=
  baseChange (f.fiber_fac y)

/-- **The base change map for a fibre, as a natural transformation** from the fibre at `y` of
the direct image to the global sections on the fibre `X_y`: the global sections on `Spec κ(y)`
of `AlgebraicGeometry.Scheme.Modules.fiberBaseChange`.

```
   X.Modules ────────── f_* ⋙ (–)(y) ─────────→ ModuleCat κ(y)
       │                                              ║
   F ↦ F_y │                    ⟹                     ║
       ↓                                              ║
 (X_y).Modules ────── Γ(X_y, –) ────────────→ ModuleCat κ(y)
```
-/
noncomputable def fiberBaseChangeNatTrans :
    pushforward f ⋙ fiberFunctor Y y ⟶ restrictToFiber f y ⋙ fiberSectionsFunctor f y :=
  Functor.whiskerRight (fiberBaseChange f y).natTrans
    (moduleSpecΓFunctor (R := Y.residueField y))

/-- **The base change map** `(f_* F)(y) ⟶ Γ(X_y, F_y)`, from the fibre at `y` of the direct
image of `F` along `f : X ⟶ Y` to the global sections of the restriction of `F` to the fibre
`X_y`. It is a `κ(y)`-linear map, and it is natural in `F` by
`AlgebraicGeometry.Scheme.Modules.fiberBaseChangeMap_naturality`. -/
noncomputable def fiberBaseChangeMap :
    ((pushforward f).obj F).fiber y ⟶ fiberSections f F y :=
  (fiberBaseChangeNatTrans f y).app F

/-- The base change map is the image of the base change transformation under global sections
on `Spec κ(y)`. -/
lemma fiberBaseChangeMap_eq :
    fiberBaseChangeMap f F y =
      (moduleSpecΓFunctor (R := Y.residueField y)).map ((fiberBaseChange f y).natTrans.app F) :=
  rfl

variable {F} in
/-- **The base change map is natural in `F`.** -/
@[reassoc]
lemma fiberBaseChangeMap_naturality {G : X.Modules} (φ : F ⟶ G) :
    fiberMap ((pushforward f).map φ) y ≫ fiberBaseChangeMap f G y =
      fiberBaseChangeMap f F y ≫ (fiberSectionsFunctor f y).map ((restrictToFiber f y).map φ) :=
  (fiberBaseChangeNatTrans f y).naturality φ

end FiberBaseChange

section Subsingleton

variable {X : Scheme.{u}}

instance subsingleton_sections_bot (M : X.Modules) : Subsingleton Γ(M, ⊥) :=
  Module.subsingleton Γ(X, ⊥) Γ(M, ⊥)

instance subsingleton_sections_top_of_isEmpty [IsEmpty X] (M : X.Modules) :
    Subsingleton Γ(M, ⊤) := by
  have h : (⊤ : X.Opens) = ⊥ := by ext x; exact (IsEmpty.false x).elim
  rw [h]
  infer_instance

/-- On a scheme with at most one point, a morphism of `𝒪ₓ`-modules is an isomorphism as soon as
it is one on sections over `⊤`. -/
theorem isIso_of_isIso_app_top [Subsingleton X] {M N : X.Modules} (φ : M ⟶ N)
    (h : IsIso (φ.app ⊤)) : IsIso φ := by
  rw [Hom.isIso_iff_isIso_app]
  intro U
  -- the only open subsets of `X` are `⊥` and `⊤`, and all sections over `⊥` vanish
  rcases U.eq_bot_or_top with rfl | rfl
  · rw [ConcreteCategory.isIso_iff_bijective]
    exact ⟨fun _ _ _ ↦ Subsingleton.elim _ _, fun _ ↦ ⟨0, Subsingleton.elim _ _⟩⟩
  · exact h

/-- The compatible family of sections of an `𝒪ₓ`-module cut out by a single global section, by
restriction to the various open subsets. -/
noncomputable def sectionsMkTop (M : X.Modules) (m : Γ(M, ⊤)) : M.sections :=
  PresheafOfModules.sectionsMk (fun _ ↦ M.val.map (homOfLE le_top).op m) (fun _ _ _ ↦ by
    rw [← PresheafOfModules.map_comp_apply]
    exact M.val.congr_map_apply (Subsingleton.elim _ _) m)

/-- The morphism `𝒪ₓ ⟶ M` of `𝒪ₓ`-modules determined by a global section `m` of `M`; it sends
a section `r` of the structure sheaf to `r • m`, see
`AlgebraicGeometry.Scheme.Modules.homOfSectionTop_app_top`. -/
noncomputable def homOfSectionTop (M : X.Modules) (m : Γ(M, ⊤)) :
    SheafOfModules.unit X.ringCatSheaf ⟶ M :=
  M.unitHomEquiv.symm (sectionsMkTop M m)

@[simp]
theorem homOfSectionTop_app_top (M : X.Modules) (m : Γ(M, ⊤)) (r : Γ(X, ⊤)) :
    Hom.app (homOfSectionTop M m) ⊤ r = r • m := by
  have h₀ := SheafOfModules.unitHomEquiv_apply_coe M (homOfSectionTop M m) (.op ⊤)
  simp only [homOfSectionTop, Equiv.apply_symm_apply] at h₀
  have h : Hom.app (homOfSectionTop M m) ⊤ (1 : Γ(X, ⊤)) = m :=
    h₀.symm.trans (by simp [sectionsMkTop])
  calc Hom.app (homOfSectionTop M m) ⊤ r
      = Hom.app (homOfSectionTop M m) ⊤ (r • (1 : Γ(X, ⊤))) := by rw [smul_eq_mul, mul_one]
    _ = r • m := by rw [Hom.app_smul, h]

/-- **On a scheme with at most one point, a global section that generates the global sections
trivialises the module**: if `r ↦ r • m` is bijective on global sections, then the morphism
`𝒪ₓ ⟶ M` determined by `m` is an isomorphism. -/
theorem isIso_homOfSectionTop [Subsingleton X] {M : X.Modules} (m : Γ(M, ⊤))
    (hm : Function.Bijective fun r : Γ(X, ⊤) ↦ r • m) : IsIso (homOfSectionTop M m) := by
  refine isIso_of_isIso_app_top _ ?_
  rw [ConcreteCategory.isIso_iff_bijective, funext (homOfSectionTop_app_top M m)]
  exact hm

end Subsingleton

end Scheme.Modules

end AlgebraicGeometry
