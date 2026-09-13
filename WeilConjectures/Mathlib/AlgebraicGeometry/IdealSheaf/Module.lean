/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf

/-!
# The ideal sheaf of a `Scheme.IdealSheafData` as a sheaf of modules

Mathlib's `AlgebraicGeometry.Scheme.IdealSheafData` is deliberately *not* a subsheaf of
`𝒪_X`: it records an ideal `I(U) ≤ Γ(X, U)` for every **affine** open `U`, together with the
compatibility `I(D(f)) = I(U)_f`, and nothing else. That is enough to determine an ideal
sheaf, and the file that introduces it says explicitly that turning it into an actual
subsheaf is left for later. Nothing in Mathlib does so: `Mathlib/AlgebraicGeometry/Modules/`
never mentions `IdealSheafData`, and conversely the `IdealSheaf/` directory never mentions
`SheafOfModules`.

This file supplies the missing bridge. The construction goes through the closed subscheme
rather than through the sections: `J.subschemeι : V(J) ⟶ X` is a closed immersion with
`𝒪_{V(J)} = 𝒪_X/J`, so the ideal sheaf is the kernel of `𝒪_X ⟶ (ι_J)_* 𝒪_{V(J)}` in the
abelian category `X.Modules`. This costs nothing: `Scheme.IdealSheafData.subscheme` and
`ker_subschemeι_app` are already in Mathlib, and `X.Modules` is already abelian.

The alternative — extending `J.ideal` to all opens by
`⨅ V affine, V ≤ U, (J.ideal V).comap (res)`, packaging it as a
`PresheafOfModules.Submodule` and then proving the sheaf condition by hand — needs a genuine
sheaf-condition argument that the kernel description gets for free.

## Main definitions

- `AlgebraicGeometry.Scheme.IdealSheafData.toModules` — the ideal sheaf as an `𝒪_X`-module.
- `AlgebraicGeometry.Scheme.IdealSheafData.toModulesι` — its inclusion into `𝒪_X`.
- `AlgebraicGeometry.Scheme.IdealSheafData.idealOfOpens` — the ideal cut out on an arbitrary
  open subset, extending `J.ideal` off the affine opens.

## Main results

- `AlgebraicGeometry.Scheme.IdealSheafData.range_toModulesι_app` — over an affine open `U`,
  the sections of `J.toModules` are exactly `J.ideal U`, which is what makes the definition
  the right one.
- `AlgebraicGeometry.Scheme.IdealSheafData.injective_toModulesι_app` — the inclusion is
  injective on sections over every open, affine or not.
- `AlgebraicGeometry.Scheme.IdealSheafData.comapModulesMap` — the comparison morphism
  `g^* I ⟶ I'` for a morphism `g` pulling the ideal `I` into the ideal `I'`, together with
  `comapModulesMap_toModulesι`, which determines it.

## TODO

Local freeness of rank one for an invertible ideal sheaf. What is missing is a criterion for
a morphism in `X.Modules` to be an isomorphism that can be checked on a basis of opens or on
stalks: `Scheme.Modules.Hom.isIso_iff_isIso_app` quantifies over *all* opens, which is not
usable directly, and Mathlib has no stalkwise criterion phrased for `X.Modules` (only
`Scheme.Modules.restrictStalkNatIso`). Note also that Mathlib's
`SheafOfModules.IsLocallyFree` carries no rank information, so "rank one" has to be spelled
out separately.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X : Scheme.{u}} (J : X.IdealSheafData)

/-- The comparison morphism `𝒪_X ⟶ (ι_J)_* 𝒪_{V(J)}` of `𝒪_X`-modules attached to the closed
immersion `J.subschemeι` of the closed subscheme cut out by `J`. Its kernel is the ideal
sheaf; see `AlgebraicGeometry.Scheme.IdealSheafData.toModules`. -/
noncomputable def toPushforwardSubscheme :
    X.structureModules ⟶
      (SheafOfModules.pushforward J.subschemeι.toRingCatSheafHom).obj
        J.subscheme.structureModules :=
  SheafOfModules.unitToPushforwardObjUnit _

@[simp]
lemma map_toPushforwardSubscheme (U : X.Opens)
    (x : Γ(X.structureModules, U)) :
    (SheafOfModules.evaluation X.ringCatSheaf (op U)).map J.toPushforwardSubscheme x =
      J.subschemeι.app U x :=
  rfl

/-- **The ideal sheaf attached to a `Scheme.IdealSheafData`**, as a sheaf of `𝒪_X`-modules:
the kernel of `𝒪_X ⟶ (ι_J)_* 𝒪_{V(J)}`.

Over an affine open `U` its sections are `J.ideal U`
(`AlgebraicGeometry.Scheme.IdealSheafData.range_toModulesι_app`). -/
noncomputable def toModules : X.Modules := kernel J.toPushforwardSubscheme

/-- The inclusion of the ideal sheaf into the structure sheaf. -/
noncomputable def toModulesι :
    J.toModules ⟶ X.structureModules :=
  kernel.ι _

lemma map_kernelι_eq_toModulesι_app (U : X.Opens) (x : Γ(J.toModules, U)) :
    (SheafOfModules.evaluation X.ringCatSheaf (op U)).map (kernel.ι J.toPushforwardSubscheme) x =
      J.toModulesι.app U x :=
  rfl

/-- The ideal cut out by `J` on an **arbitrary** open subset, not just an affine one: the
kernel of the restriction map to the closed subscheme.

`Scheme.IdealSheafData` itself only records ideals on affine opens, so this is the extension
of `J.ideal` to all of `X.Opens`, and `idealOfOpens_eq_ideal` says the extension is
compatible. -/
noncomputable def idealOfOpens (U : X.Opens) : Ideal Γ(X, U) :=
  RingHom.ker (J.subschemeι.app U).hom

@[simp]
lemma idealOfOpens_eq_ideal (U : X.affineOpens) : J.idealOfOpens U.1 = J.ideal U :=
  J.ker_subschemeι_app U

lemma mem_idealOfOpens_iff {U : X.Opens} {x : Γ(X, U)} :
    x ∈ J.idealOfOpens U ↔ J.subschemeι.app U x = 0 :=
  RingHom.mem_ker

/-- Over any open subset, the sections of the ideal sheaf are exactly the sections of `𝒪_X`
killed by the restriction to the closed subscheme cut out by `J`. -/
lemma range_toModulesι_app_eq (U : X.Opens) :
    Set.range (J.toModulesι.app U) = { x | J.subschemeι.app U x = 0 } :=
  Scheme.Modules.range_map_kernelι U J.toPushforwardSubscheme

lemma range_toModulesι_app_eq_idealOfOpens (U : X.Opens) :
    Set.range (J.toModulesι.app U) = (J.idealOfOpens U : Set Γ(X, U)) :=
  J.range_toModulesι_app_eq U

/-- **Over an affine open the sections of the ideal sheaf are the given ideal.** This is what
identifies `J.toModules` with the ideal sheaf that `J` is intended to describe: `J` only
records `J.ideal U` for affine `U`, and that is exactly what `J.toModules` gives back. -/
lemma range_toModulesι_app (U : X.affineOpens) :
    Set.range (J.toModulesι.app U.1) = (J.ideal U : Set Γ(X, U.1)) := by
  rw [range_toModulesι_app_eq_idealOfOpens, idealOfOpens_eq_ideal]

instance : Mono J.toModulesι := by
  unfold toModulesι
  infer_instance

/-- The ideal sheaf really is a subsheaf of `𝒪_X`: the inclusion is injective on sections
over every open subset, not merely a categorical monomorphism. -/
lemma injective_toModulesι_app (U : X.Opens) : Function.Injective (J.toModulesι.app U) :=
  Scheme.Modules.injective_map_kernelι U J.toPushforwardSubscheme

/-! ### The comparison morphism of ideal sheaves attached to a morphism of thickenings -/

variable {W W' : Scheme.{u}} (I : W.IdealSheafData) (I' : W'.IdealSheafData) (g : W' ⟶ W)

set_option backward.isDefEq.respectTransparency false in
/-- If `g : W' ⟶ W` pulls the ideal `I` into the ideal `I'`, then the composite
`g^* I ⟶ g^* 𝒪_W ≅ 𝒪_{W'}` dies in `(i')_* 𝒪_{V(I')}`, hence factors through `I'`. -/
lemma pullback_toModulesι_comp_toPushforwardSubscheme (hg : I.comap g ≤ I') :
    ((Modules.pullback g).map I.toModulesι ≫ (Modules.pullbackUnitIso g).hom) ≫
      I'.toPushforwardSubscheme = 0 := by
  set adj := Modules.pullbackPushforwardAdjunction g with hadj
  apply (adj.homEquiv _ _).injective
  have hnat : adj.unit.app I.toModules ≫
      (Modules.pushforward g).map ((Modules.pullback g).map I.toModulesι) =
      I.toModulesι ≫ adj.unit.app W.structureModules :=
    (adj.unit.naturality I.toModulesι).symm
  simp only [Adjunction.homEquiv_unit, Functor.map_zero, Limits.comp_zero, Functor.map_comp,
    ← Category.assoc, hnat]
  simp only [Category.assoc]
  have hu : adj.unit.app W.structureModules ≫
      (Modules.pushforward g).map (Modules.pullbackUnitIso g).hom =
      SheafOfModules.unitToPushforwardObjUnit g.toRingCatSheafHom :=
    SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit _
  rw [← Category.assoc (adj.unit.app W.structureModules), hu]
  ext U x
  simp only [Modules.pushforward_obj_obj, Functor.id_obj, Modules.Hom.comp_app,
    Modules.pushforward_map_app, AddCommGrpCat.hom_comp, AddMonoidHom.coe_comp,
    Function.comp_apply, Modules.Hom.zero_app, AddCommGrpCat.hom_zero, AddMonoidHom.zero_apply]
  set a := Modules.Hom.app I.toModulesι U x with ha'
  change I'.subschemeι.app (g ⁻¹ᵁ U) (g.app U a) = 0
  have ha : I.subschemeι.app U a = 0 := by
    have hmem : a ∈ Set.range (Modules.Hom.app I.toModulesι U) := ⟨x, rfl⟩
    rw [I.range_toModulesι_app_eq U] at hmem
    exact hmem
  have hcongr := ConcreteCategory.congr_hom (Scheme.Hom.congr_app
    (subschemeMapOfComapLe_subschemeι I I' g hg).symm U) a
  rw [Scheme.Hom.comp_app, Scheme.Hom.comp_app] at hcongr
  simp only [CommRingCat.comp_apply] at hcongr
  rw [ha, map_zero, map_zero] at hcongr
  simpa using hcongr

/-- **The comparison morphism `g^* I ⟶ I'` of ideal sheaves** attached to a morphism
`g : W' ⟶ W` pulling the ideal `I` into the ideal `I'`: the factorisation of
`g^* I ⟶ g^* 𝒪_W ≅ 𝒪_{W'}` through the kernel `I' = ker(𝒪_{W'} ⟶ (i')_* 𝒪_{V(I')})`.

This is the morphism `φ` that the naturality statements of
`AlgebraicGeometry.Scheme.IdealSheafData.unitsToH1_naturality` and `h1ToPic_naturality` take
as a parameter; `AlgebraicGeometry.Scheme.IdealSheafData.comapModulesMap_toModulesι` is the
hypothesis `hφ` those statements require, and it determines `φ` uniquely because
`I'.toModulesι` is a monomorphism. -/
noncomputable def comapModulesMap (hg : I.comap g ≤ I') :
    (Modules.pullback g).obj I.toModules ⟶ I'.toModules :=
  kernel.lift I'.toPushforwardSubscheme
    ((Modules.pullback g).map I.toModulesι ≫ (Modules.pullbackUnitIso g).hom)
    (pullback_toModulesι_comp_toPushforwardSubscheme I I' g hg)

@[reassoc (attr := simp)]
lemma comapModulesMap_toModulesι (hg : I.comap g ≤ I') :
    comapModulesMap I I' g hg ≫ I'.toModulesι =
      (Modules.pullback g).map I.toModulesι ≫ (Modules.pullbackUnitIso g).hom :=
  kernel.lift_ι _ _ _

end AlgebraicGeometry.Scheme.IdealSheafData
