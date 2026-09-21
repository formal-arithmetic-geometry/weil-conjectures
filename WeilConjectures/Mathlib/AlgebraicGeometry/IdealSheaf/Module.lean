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
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

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
- `AlgebraicGeometry.Scheme.IdealSheafData.pushforwardStructureDesc` and
  `AlgebraicGeometry.Scheme.IdealSheafData.pushforwardFreeDesc` — the morphisms
  `g_* 𝒪_Y ⟶ J` and `g_* (𝒪_Y^ι) ⟶ J` given by multiplication by a global section of `J`,
  respectively by a family of them, when `g.ker * J = 0`.

## Main results

- `AlgebraicGeometry.Scheme.IdealSheafData.range_toModulesι_app` — over an affine open `U`,
  the sections of `J.toModules` are exactly `J.ideal U`, which is what makes the definition
  the right one.
- `AlgebraicGeometry.Scheme.IdealSheafData.toModulesι_app_injective` — the inclusion is
  injective on sections over every open, affine or not.
- `AlgebraicGeometry.Scheme.IdealSheafData.smul_eq_zero_of_mul_eq_zero` — **an ideal sheaf
  `I` with `I * J = 0` annihilates the sections of `J`**, over an arbitrary open subset.
- `AlgebraicGeometry.Scheme.IdealSheafData.range_stalkMap_toModulesι` and
  `AlgebraicGeometry.Scheme.IdealSheafData.mem_range_stalkMap_toModulesι_iff` — the stalk of
  the ideal sheaf is the set of germs killed by the restriction to the closed subscheme, that
  is, the set of germs of sections lying in the ideal, and
  `AlgebraicGeometry.Scheme.IdealSheafData.stalkMap_toModulesι_injective` — the inclusion is
  injective on stalks.
- `AlgebraicGeometry.Scheme.IdealSheafData.shortExact_toModulesι_toPushforwardSubscheme` —
  **`0 ⟶ J.toModules ⟶ 𝒪_X ⟶ (ι_J)_* 𝒪_{V(J)} ⟶ 0` is a short exact sequence**, so that
  `(ι_J)_* 𝒪_{V(J)}` is the quotient of `𝒪_X` by the ideal sheaf and a morphism out of `𝒪_X`
  killing the ideal sheaf descends to it through
  `AlgebraicGeometry.Scheme.Hom.descPushforwardStructure`.
- `AlgebraicGeometry.Scheme.IdealSheafData.isIso_pushforwardFreeDesc` — **the stalkwise
  criterion for `g_* (𝒪_Y^ι) ⟶ J` to be an isomorphism**: it suffices that at every point `x`
  the germs of the `m j` generate the ideal `J_x` of `𝒪_{X, x}` and that their only relations
  have coefficients in the stalk of `g.ker`. The variant
  `AlgebraicGeometry.Scheme.IdealSheafData.isIso_pushforwardFreeDesc_of_germ` phrases the two
  hypotheses in terms of the stalk of `J` as a sheaf of modules, and
  `AlgebraicGeometry.Scheme.IdealSheafData.stalkMap_pushforwardFreeDesc` computes the
  comparison morphism on a stalk.
- `AlgebraicGeometry.Scheme.IdealSheafData.range_stalkIdealι` — the stalk of the ideal sheaf
  sits in the local ring `𝒪_{X, x}` as the ideal
  `AlgebraicGeometry.Scheme.IdealSheafData.stalkIdeal`.
- `AlgebraicGeometry.Scheme.IdealSheafData.comapModulesMap` — the comparison morphism
  `g^* I ⟶ I'` for a morphism `g` pulling the ideal `I` into the ideal `I'`, together with
  `comapModulesMap_toModulesι` and `eq_comapModulesMap`, which determine it.
- `AlgebraicGeometry.Scheme.IdealSheafData.pullback_map_pushforwardFreeDesc_comp_comapModulesMap`
  — **the comparison morphism attached to a family of global sections commutes with base
  change**, provided the two families correspond under the pullback of functions; with its
  one-section form `pullback_map_pushforwardStructureDesc_comp_comapModulesMap`.

## TODO

Local freeness of rank one for an invertible ideal sheaf. Several halves of the criterion this
needs are now available. `Scheme.Modules.Hom.isIso_iff_isIso_app` quantifies over *all* opens,
which is not usable directly, but `Scheme.Modules.Hom.isIso_of_isIso_stalkMap` checks a *given*
morphism `𝒪_U ⟶ I|_U` on stalks, `mem_range_stalkMap_toModulesι_iff` below describes the stalk
it has to hit, and the local forms `Scheme.Modules.isIso_of_forall_exists_isIso_app` (invertible
on every open small enough) and `Scheme.Modules.isIso_of_isOpenCover_restrict` (invertible after
restriction to each member of an open cover) are there too. What is still missing is the
criterion on a basis of opens, whose proof has to go through separatedness and gluing because a
basis is not closed under intersection with an arbitrary open; the production of the open `U` and
the morphism, that is, a generator of the stalk `I_x` together with a section over some `U`
extending it; and the transport of `isIso_of_isIso_stalkMap` along
`Scheme.Modules.restrictFunctor` to `U` viewed as a scheme. Note also that Mathlib's
`SheafOfModules.IsLocallyFree` carries no rank information, so "rank one" has to be spelled out
separately.
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
    X.structureModules ⟶ (Modules.pushforward J.subschemeι).obj J.subscheme.structureModules :=
  J.subschemeι.toPushforwardStructure

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
lemma toModulesι_app_injective (U : X.Opens) : Function.Injective (J.toModulesι.app U) :=
  Scheme.Modules.map_kernelι_injective U J.toPushforwardSubscheme

/-- **A function lying in an ideal sheaf `I` annihilates the sections of an ideal sheaf `J`
with `I * J = 0`.** This is the section-level form of the vanishing `I * J = 0`, which is
recorded on affine opens only. -/
lemma smul_eq_zero_of_mul_eq_zero {I J : X.IdealSheafData} (hIJ : I * J = 0) {U : X.Opens}
    {r : Γ(X, U)} (hr : r ∈ I.idealOfOpens U) (m : Γ(J.toModules, U)) : r • m = 0 := by
  refine J.toModulesι_app_injective U ?_
  rw [Modules.Hom.app_smul, map_zero]
  exact mul_eq_zero_of_mem_idealOfOpens hIJ hr
    ((J.range_toModulesι_app_eq_idealOfOpens U).le ⟨m, rfl⟩)

/-! ### The pushforward of the structure sheaf of the closed subscheme is the quotient -/

section ShortExact

@[reassoc (attr := simp)]
lemma toModulesι_comp_toPushforwardSubscheme :
    J.toModulesι ≫ J.toPushforwardSubscheme = 0 :=
  kernel.condition _

/-- **`(ι_J)_* 𝒪_{V(J)}` is the quotient of `𝒪_X` by the ideal sheaf of `J`**: the sequence
```
0 ⟶ J.toModules ⟶ 𝒪_X ⟶ (ι_J)_* 𝒪_{V(J)} ⟶ 0
```
is a short exact sequence of sheaves of `𝒪_X`-modules. The ideal sheaf is the kernel of the
comparison morphism by definition, and the comparison morphism is an epimorphism because
`J.subschemeι` is a closed immersion. -/
lemma shortExact_toModulesι_toPushforwardSubscheme :
    (ShortComplex.mk J.toModulesι J.toPushforwardSubscheme
      J.toModulesι_comp_toPushforwardSubscheme).ShortExact :=
  J.subschemeι.shortExact_kernelSequence_toPushforwardStructure

end ShortExact

/-! ### The stalks of the ideal sheaf -/

section Stalk

variable (x : X)

/-- **The ideal sheaf is a subsheaf of `𝒪_X` on stalks too**: its inclusion into the structure
sheaf is injective on every stalk. -/
lemma stalkMap_toModulesι_injective : Function.Injective (J.toModulesι.stalkMap x) :=
  Modules.stalkMap_kernelι_injective J.toPushforwardSubscheme x

/-- **The stalk of the ideal sheaf** is the set of germs killed by the restriction to the closed
subscheme cut out by `J`:

```
0 ⟶ (J.toModules)_x --- ι ---> (𝒪_X)_x --- res ---> ((ι_J)_* 𝒪_{V(J)})_x
```
-/
lemma range_stalkMap_toModulesι :
    Set.range (J.toModulesι.stalkMap x) = { z | J.toPushforwardSubscheme.stalkMap x z = 0 } :=
  Modules.range_stalkMap_kernelι J.toPushforwardSubscheme x

/-- **The stalk of the ideal sheaf consists exactly of the germs of the sections of `𝒪_X` lying
in the ideal.** This is the stalkwise counterpart of
`AlgebraicGeometry.Scheme.IdealSheafData.range_toModulesι_app_eq_idealOfOpens`. The right hand
side still ranges over all opens `U` containing `x`; identifying the stalk with a localisation
of `J.ideal U` for a single affine `U` is a further step. -/
lemma mem_range_stalkMap_toModulesι_iff (z : X.structureModules.presheaf.stalk x) :
    z ∈ Set.range (J.toModulesι.stalkMap x) ↔
      ∃ (U : X.Opens) (hx : x ∈ U), ∃ s ∈ J.idealOfOpens U,
        X.structureModules.presheaf.germ U x hx s = z := by
  rw [Modules.Hom.range_stalkMap]
  simp only [J.range_toModulesι_app_eq_idealOfOpens, Set.mem_iUnion, Set.mem_image,
    SetLike.mem_coe]
  rfl

/-- **The stalk of the ideal sheaf, as a submodule of the local ring `𝒪_{X, x}`**: the
inclusion `J.toModulesι` on the stalk at `x`, read through the identification
`AlgebraicGeometry.Scheme.Modules.stalkStructureModulesLinearEquiv` of the stalk of `𝒪_X`
viewed as a sheaf of modules with the local ring. Its range is
`AlgebraicGeometry.Scheme.IdealSheafData.stalkIdeal`. -/
noncomputable def stalkIdealι :
    J.toModules.presheaf.stalk x →ₗ[X.presheaf.stalk x] X.presheaf.stalk x :=
  (Modules.stalkStructureModulesLinearEquiv X x).toLinearMap ∘ₗ
    ((Modules.stalkFunctor X x).map J.toModulesι).hom

lemma stalkIdealι_apply (v : J.toModules.presheaf.stalk x) :
    J.stalkIdealι x v =
      Modules.stalkStructureModulesLinearEquiv X x (J.toModulesι.stalkMap x v) :=
  rfl

@[simp]
lemma stalkIdealι_germ {U : X.Opens} (hx : x ∈ U) (t : Γ(J.toModules, U)) :
    J.stalkIdealι x (J.toModules.presheaf.germ U x hx t) =
      X.presheaf.germ U x hx (J.toModulesι.app U t) := by
  rw [stalkIdealι_apply, Modules.Hom.germ_stalkMap_apply,
    Modules.stalkStructureModulesLinearEquiv_germ]

lemma stalkIdealι_injective : Function.Injective (J.stalkIdealι x) :=
  (Modules.stalkStructureModulesLinearEquiv X x).injective.comp
    (J.stalkMap_toModulesι_injective x)

/-- **The stalk of the ideal sheaf is the ideal of germs of sections lying in `J`.** -/
lemma range_stalkIdealι : LinearMap.range (J.stalkIdealι x) = J.stalkIdeal x := by
  ext r
  rw [LinearMap.mem_range]
  constructor
  · rintro ⟨v, rfl⟩
    obtain ⟨U, hx, t, rfl⟩ := J.toModules.presheaf.exists_germ_eq v
    rw [stalkIdealι_germ]
    exact J.germ_mem_stalkIdeal x hx ((J.range_toModulesι_app_eq_idealOfOpens U).le ⟨t, rfl⟩)
  · rintro ⟨U, hx, s, hs, rfl⟩
    obtain ⟨t, rfl⟩ := (J.range_toModulesι_app_eq_idealOfOpens U).ge hs
    exact ⟨J.toModules.presheaf.germ U x hx t, by rw [stalkIdealι_germ]⟩

/-- **The germs of global sections of the ideal sheaf generate no more than its stalk.** This is
the inclusion of `AlgebraicGeometry.Scheme.IdealSheafData.isIso_pushforwardFreeDesc`'s spanning
hypothesis that holds for free. -/
lemma span_germ_toModulesι_app_le_stalkIdeal {ι : Type*} (m : ι → Γ(J.toModules, ⊤)) :
    Ideal.span (Set.range fun j : ι ↦
        X.presheaf.germ ⊤ x trivial (J.toModulesι.app ⊤ (m j))) ≤ J.stalkIdeal x := by
  rw [Ideal.span_le]
  rintro _ ⟨j, rfl⟩
  exact J.germ_mem_stalkIdeal x (U := ⊤) trivial
    ((J.range_toModulesι_app_eq_idealOfOpens ⊤).le ⟨m j, rfl⟩)

/-- **`stalkIdealι` turns a linear combination of germs of global sections of `J` into the
corresponding linear combination in `𝒪_{X, x}`.** -/
lemma stalkIdealι_sum_smul_germ {ι : Type*} [Fintype ι] (m : ι → Γ(J.toModules, ⊤))
    (c : ι → X.presheaf.stalk x) :
    J.stalkIdealι x (∑ j : ι, c j • J.toModules.presheaf.germ ⊤ x trivial (m j)) =
      ∑ j : ι, c j * X.presheaf.germ ⊤ x trivial (J.toModulesι.app ⊤ (m j)) := by
  rw [map_sum]
  exact Finset.sum_congr rfl fun j _ ↦ by
    rw [LinearMap.map_smul, stalkIdealι_germ, smul_eq_mul]

end Stalk

/-! ### The comparison morphism of ideal sheaves attached to a morphism of thickenings -/

variable {W W' : Scheme.{u}} (I : W.IdealSheafData) (I' : W'.IdealSheafData) (g : W' ⟶ W)

/-- If `g : W' ⟶ W` pulls the ideal `I` into the ideal `I'`, then the composite
`g^* I ⟶ g^* 𝒪_W ≅ 𝒪_{W'}` dies in `(i')_* 𝒪_{V(I')}`, hence factors through `I'`.

```
  g^* I ──g^* ι──▶ g^* 𝒪_W ──≅──▶ 𝒪_{W'} ──▶ (i')_* 𝒪_{V(I')}
                                     ▲
                                     │ I'.toModulesι
                                     │
                                     I'
```
-/
lemma pullback_toModulesι_comp_toPushforwardSubscheme_eq_zero (hg : I.comap g ≤ I') :
    ((Modules.pullback g).map I.toModulesι ≫ (Modules.pullbackUnitIso g).hom) ≫
      I'.toPushforwardSubscheme = 0 := by
  set adj := Modules.pullbackPushforwardAdjunction g
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
  -- the section `a := ι(x)` of `𝒪_W` dies in `𝒪_{V(I)}`, hence so does `g^♯ a` in `𝒪_{V(I')}`
  have ha : I.subschemeι.app U (Modules.Hom.app I.toModulesι U x) = 0 :=
    (I.range_toModulesι_app_eq U).le ⟨x, rfl⟩
  have hcongr := ConcreteCategory.congr_hom (Scheme.Hom.congr_app
    (subschemeMapOfComapLe_subschemeι I I' g hg).symm U) (Modules.Hom.app I.toModulesι U x)
  simp only [Scheme.Hom.comp_app, CommRingCat.comp_apply, ha, map_zero] at hcongr
  simp only [Modules.Hom.comp_app, Modules.Hom.zero_app, AddCommGrpCat.hom_comp,
    AddMonoidHom.coe_comp, Function.comp_apply, AddCommGrpCat.hom_zero, AddMonoidHom.zero_apply]
  exact hcongr

/-- **The comparison morphism `g^* I ⟶ I'` of ideal sheaves** attached to a morphism
`g : W' ⟶ W` pulling the ideal `I` into the ideal `I'`: the factorisation of
`g^* I ⟶ g^* 𝒪_W ≅ 𝒪_{W'}` through the kernel `I' = ker(𝒪_{W'} ⟶ (i')_* 𝒪_{V(I')})`.

```
  g^* I ──g^* ι──▶ g^* 𝒪_W ──≅──▶ 𝒪_{W'} ──▶ (i')_* 𝒪_{V(I')}
     │                                ▲
     │ comapModulesMap                │ I'.toModulesι
     └───────────────▶ I' ────────────┘
```

This is the morphism `φ` that the naturality statements of
`AlgebraicGeometry.Scheme.IdealSheafData.unitsToH1_naturality` and `h1ToPic_naturality` take
as a parameter; `AlgebraicGeometry.Scheme.IdealSheafData.comapModulesMap_toModulesι` is the
hypothesis `hφ` those statements require, and it determines `φ` uniquely
(`AlgebraicGeometry.Scheme.IdealSheafData.eq_comapModulesMap`) because `I'.toModulesι` is a
monomorphism. -/
noncomputable def comapModulesMap (hg : I.comap g ≤ I') :
    (Modules.pullback g).obj I.toModules ⟶ I'.toModules :=
  kernel.lift I'.toPushforwardSubscheme
    ((Modules.pullback g).map I.toModulesι ≫ (Modules.pullbackUnitIso g).hom)
    (pullback_toModulesι_comp_toPushforwardSubscheme_eq_zero I I' g hg)

@[reassoc (attr := simp)]
lemma comapModulesMap_toModulesι (hg : I.comap g ≤ I') :
    comapModulesMap I I' g hg ≫ I'.toModulesι =
      (Modules.pullback g).map I.toModulesι ≫ (Modules.pullbackUnitIso g).hom :=
  kernel.lift_ι _ _ _

/-- **The comparison morphism is the only one compatible with the two inclusions into the
structure sheaves**, because `I'.toModulesι` is a monomorphism. -/
lemma eq_comapModulesMap (hg : I.comap g ≤ I')
    (φ : (Modules.pullback g).obj I.toModules ⟶ I'.toModules)
    (hφ : (Modules.pullback g).map I.toModulesι ≫ (Modules.pullbackUnitIso g).hom =
      φ ≫ I'.toModulesι) :
    φ = comapModulesMap I I' g hg :=
  (cancel_mono I'.toModulesι).mp (by rw [← hφ, comapModulesMap_toModulesι])

/-! ### Multiplication by a section of an ideal sheaf killed by the kernel of a morphism -/

section PushforwardDesc

variable {X Y : Scheme.{u}} (g : Y ⟶ X) [QuasiCompact g] [Epi g.toPushforwardStructure]
  {J : X.IdealSheafData}

omit [Epi g.toPushforwardStructure] in
/-- **Multiplication by a global section of an ideal sheaf `J` with `g.ker * J = 0` kills the
kernel of `𝒪_X ⟶ g_* 𝒪_Y`**, which is what makes it descend to `g_* 𝒪_Y`. -/
lemma kernelι_toPushforwardStructure_comp_homOfSectionTop_eq_zero (hJ : g.ker * J = 0)
    (m : Γ(J.toModules, ⊤)) :
    kernel.ι g.toPushforwardStructure ≫ Modules.homOfSectionTop J.toModules m = 0 :=
  (g.kernelι_toPushforwardStructure_comp_eq_zero_iff _).mpr fun U s hs ↦ by
    rw [Modules.Hom.app_homOfSectionTop]
    exact smul_eq_zero_of_mul_eq_zero hJ (g.mem_idealOfOpens_ker_iff.mpr hs) _

/-- **Multiplication by a global section `m` of an ideal sheaf `J` with `g.ker * J = 0`**, as a
morphism `g_* 𝒪_Y ⟶ J`.

Multiplication by `m` is a morphism `𝒪_X ⟶ J` to begin with, and `g.ker * J = 0` says that it
kills every function vanishing on `Y`, so it factors through the quotient `g_* 𝒪_Y` of `𝒪_X`.

```
  𝒪_X ──toPushforwardStructure──▶ g_* 𝒪_Y
      ╲                              │
   · m ╲                             │ pushforwardStructureDesc g hJ m
        ╲                            ▼
         ╲─────────────────────────▶ J
```
-/
noncomputable def pushforwardStructureDesc (hJ : g.ker * J = 0) (m : Γ(J.toModules, ⊤)) :
    (Modules.pushforward g).obj Y.structureModules ⟶ J.toModules :=
  g.descPushforwardStructure _
    (kernelι_toPushforwardStructure_comp_homOfSectionTop_eq_zero g hJ m)

/-- **The descended morphism is still multiplication by `m`**: the triangle

```
  𝒪_X ──toPushforwardStructure──▶ g_* 𝒪_Y
      ╲                              │
   · m ╲                             │ pushforwardStructureDesc g hJ m
        ╲                            ▼
         ╲─────────────────────────▶ J
```

commutes. -/
@[reassoc (attr := simp)]
lemma toPushforwardStructure_comp_pushforwardStructureDesc (hJ : g.ker * J = 0)
    (m : Γ(J.toModules, ⊤)) :
    g.toPushforwardStructure ≫ pushforwardStructureDesc g hJ m =
      Modules.homOfSectionTop J.toModules m :=
  Hom.toPushforwardStructure_descPushforwardStructure _ _ _

/-- **The factorisation is unique**, because `𝒪_X ⟶ g_* 𝒪_Y` is an epimorphism. -/
lemma eq_pushforwardStructureDesc (hJ : g.ker * J = 0) (m : Γ(J.toModules, ⊤))
    (χ : (Modules.pushforward g).obj Y.structureModules ⟶ J.toModules)
    (hχ : g.toPushforwardStructure ≫ χ = Modules.homOfSectionTop J.toModules m) :
    χ = pushforwardStructureDesc g hJ m :=
  Hom.eq_descPushforwardStructure _ _ _ _ hχ

/-- **The comparison morphism `g_* (𝒪_Y^ι) ⟶ J` attached to a family `m` of global sections of
an ideal sheaf `J` with `g.ker * J = 0`**: on the `j`-th summand it is multiplication by `m j`.

```
  g_* 𝒪_Y ──g_* (ιFree j)──▶ g_* (𝒪_Y^ι)
        ╲                         │
  · m j  ╲                        │ pushforwardFreeDesc g hJ m
          ╲                       ▼
           ╲────────────────────▶ J
```
-/
noncomputable def pushforwardFreeDesc {ι : Type u} [Finite ι] (hJ : g.ker * J = 0)
    (m : ι → Γ(J.toModules, ⊤)) :
    (Modules.pushforward g).obj (Y.freeModules ι) ⟶ J.toModules :=
  Modules.pushforwardFreeDesc g fun j ↦ pushforwardStructureDesc g hJ (m j)

/-- **On the `j`-th summand the comparison morphism is multiplication by `m j`.** -/
@[reassoc (attr := simp)]
lemma map_ιFree_comp_pushforwardFreeDesc {ι : Type u} [Finite ι] (hJ : g.ker * J = 0)
    (m : ι → Γ(J.toModules, ⊤)) (j : ι) :
    (Modules.pushforward g).map (SheafOfModules.ιFree j) ≫ pushforwardFreeDesc g hJ m =
      pushforwardStructureDesc g hJ (m j) :=
  Modules.map_ιFree_comp_pushforwardFreeDesc _ _ _

/-- **The comparison morphism is the only one that is multiplication by `m j` on the `j`-th
summand.** -/
lemma eq_pushforwardFreeDesc {ι : Type u} [Finite ι] (hJ : g.ker * J = 0)
    (m : ι → Γ(J.toModules, ⊤))
    (χ : (Modules.pushforward g).obj (Y.freeModules ι) ⟶ J.toModules)
    (hχ : ∀ j : ι, (Modules.pushforward g).map (SheafOfModules.ιFree j) ≫ χ =
      pushforwardStructureDesc g hJ (m j)) :
    χ = pushforwardFreeDesc g hJ m :=
  Modules.eq_pushforwardFreeDesc _ _ _ hχ

/-! #### The comparison morphism on stalks -/

omit [Epi g.toPushforwardStructure] in
/-- **The kernel of `𝒪_X ⟶ g_* 𝒪_Y` on the stalk at `x` is the stalk of the kernel ideal
sheaf of `g`.** -/
lemma stalkMap_toPushforwardStructure_eq_zero_iff (x : X)
    (z : X.structureModules.presheaf.stalk x) :
    Modules.Hom.stalkMap g.toPushforwardStructure x z = 0 ↔
      Modules.stalkStructureModulesLinearEquiv X x z ∈ g.ker.stalkIdeal x := by
  obtain ⟨U, hx, s, rfl⟩ := X.structureModules.presheaf.exists_germ_eq z
  rw [Modules.stalkStructureModulesLinearEquiv_germ]
  set P := (Modules.pushforward g).obj Y.structureModules
  constructor
  · rw [Modules.Hom.germ_stalkMap_apply]
    intro h
    rw [← map_zero (ConcreteCategory.hom (P.presheaf.germ ⊤ x trivial))] at h
    obtain ⟨W, hW, iWU, _, he⟩ := P.presheaf.germ_eq x hx _ _ _ h
    rw [map_zero, ← Modules.Hom.naturality_apply] at he
    rw [← X.presheaf.germ_res_apply iWU x hW s]
    exact germ_mem_stalkIdeal _ _ hW (g.mem_idealOfOpens_ker_iff.mpr he)
  · intro hmem
    obtain ⟨V, hV, t, ht, hvt⟩ := (mem_stalkIdeal_iff _ _ _).mp hmem
    obtain ⟨W, hW, iWV, iWU, he⟩ := X.presheaf.germ_eq x hV hx t s hvt
    have hzero : Modules.Hom.app g.toPushforwardStructure W
        (X.structureModules.presheaf.map iWU.op s) = 0 := by
      -- `X.structureModules` has the sections and the restriction maps of `𝒪_X`
      change Hom.app g W (X.presheaf.map iWU.op s) = 0
      rw [← he]
      exact g.mem_idealOfOpens_ker_iff.mp (map_mem_idealOfOpens _ iWV.le ht)
    rw [← X.structureModules.presheaf.germ_res_apply iWU x hW s,
      Modules.Hom.germ_stalkMap_apply, hzero, map_zero]

variable {ι : Type u} [Fintype ι]

omit [Fintype ι] in
/-- **The comparison morphism is multiplication by `m j` on the `j`-th component of a germ**:
the elementwise form of `map_ιFree_comp_pushforwardFreeDesc` composed with
`toPushforwardStructure_comp_pushforwardStructureDesc`. -/
lemma stalkMap_map_ιFree_pushforwardFreeDesc [Finite ι] (hJ : g.ker * J = 0)
    (m : ι → Γ(J.toModules, ⊤)) (x : X) (j : ι)
    (a : X.structureModules.presheaf.stalk x) :
    Modules.Hom.stalkMap (pushforwardFreeDesc g hJ m) x
        (Modules.Hom.stalkMap ((Modules.pushforward g).map (SheafOfModules.ιFree j)) x
          (Modules.Hom.stalkMap g.toPushforwardStructure x a)) =
      Modules.Hom.stalkMap (Modules.homOfSectionTop J.toModules (m j)) x a := by
  rw [← Modules.Hom.stalkMap_comp_apply, ← Modules.Hom.stalkMap_comp_apply,
    map_ιFree_comp_pushforwardFreeDesc g hJ m j,
    toPushforwardStructure_comp_pushforwardStructureDesc g hJ (m j)]

/-- **The comparison morphism `g_* (𝒪_Y^ι) ⟶ J` on a stalk is `c ↦ ∑ⱼ cⱼ · mⱼ`**, computed
through a lift `c` of the components of a germ along the surjection `𝒪_X ⟶ g_* 𝒪_Y` on
stalks: the triangle

```
  𝒪_X ──toPushforwardStructure──▶ g_* 𝒪_Y ──g_* (ιFree j)──▶ g_* (𝒪_Y^ι)
      ╲                                                           │
 · m j ╲                                                          │ pushforwardFreeDesc g hJ m
        ╲                                                         ▼
         ╲────────────────────────────────────────────────────────▶ J
```

commutes after applying `(-)ₓ`, and the germ `w` is the sum of its `ι` components. -/
lemma stalkMap_pushforwardFreeDesc (hJ : g.ker * J = 0) (m : ι → Γ(J.toModules, ⊤)) (x : X)
    (w : ((Modules.pushforward g).obj (Y.freeModules ι)).presheaf.stalk x)
    (c : ι → X.structureModules.presheaf.stalk x)
    (hc : ∀ j, Modules.Hom.stalkMap g.toPushforwardStructure x (c j) =
      Modules.Hom.stalkMap ((Modules.pushforward g).map (SheafOfModules.πFree j)) x w) :
    Modules.Hom.stalkMap (pushforwardFreeDesc g hJ m) x w =
      ∑ j : ι, Modules.Hom.stalkMap (Modules.homOfSectionTop J.toModules (m j)) x (c j) := by
  conv_lhs => rw [← Modules.sum_stalkMap_map_ιFree g x w]
  rw [map_sum (ConcreteCategory.hom
    (Modules.Hom.stalkMap (pushforwardFreeDesc g hJ m) x))]
  exact Finset.sum_congr rfl fun j _ ↦ by
    rw [← hc j, stalkMap_map_ιFree_pushforwardFreeDesc]

/-- The stalkwise criterion for `g_* (𝒪_Y^ι) ⟶ J` to be an isomorphism, with both hypotheses
phrased in the stalks of `𝒪_X` viewed as a sheaf of modules over itself. This is the internal
step of the proof; the two forms meant for callers are
`AlgebraicGeometry.Scheme.IdealSheafData.isIso_pushforwardFreeDesc_of_germ` and
`AlgebraicGeometry.Scheme.IdealSheafData.isIso_pushforwardFreeDesc`. -/
private theorem isIso_pushforwardFreeDesc_of_stalkMap (hJ : g.ker * J = 0)
    (m : ι → Γ(J.toModules, ⊤))
    (hker : ∀ (x : X) (c : ι → X.structureModules.presheaf.stalk x),
      ∑ j : ι, Modules.Hom.stalkMap (Modules.homOfSectionTop J.toModules (m j)) x (c j) = 0 →
        ∀ j, Modules.Hom.stalkMap g.toPushforwardStructure x (c j) = 0)
    (hspan : ∀ (x : X) (v : J.toModules.presheaf.stalk x),
      ∃ c : ι → X.structureModules.presheaf.stalk x,
        ∑ j : ι, Modules.Hom.stalkMap (Modules.homOfSectionTop J.toModules (m j)) x (c j) = v) :
    IsIso (pushforwardFreeDesc g hJ m) := by
  refine Modules.Hom.isIso_of_isIso_stalkMap _ fun x ↦ ?_
  rw [ConcreteCategory.isIso_iff_bijective]
  have hsurj : Function.Surjective (Modules.Hom.stalkMap g.toPushforwardStructure x) :=
    (Modules.epi_iff_surjective_stalkMap _).mp inferInstance x
  constructor
  · rw [injective_iff_map_eq_zero]
    intro w hw
    choose c hc using fun j : ι ↦ hsurj (Modules.Hom.stalkMap
      ((Modules.pushforward g).map (SheafOfModules.πFree j)) x w)
    have h0 := stalkMap_pushforwardFreeDesc g hJ m x w c hc
    rw [hw] at h0
    rw [← Modules.sum_stalkMap_map_ιFree g x w]
    exact Finset.sum_eq_zero fun j _ ↦ by rw [← hc j, hker x c h0.symm j, map_zero]
  · intro v
    obtain ⟨c, hc⟩ := hspan x v
    refine ⟨∑ j : ι, Modules.Hom.stalkMap ((Modules.pushforward g).map
      (SheafOfModules.ιFree j)) x
      (Modules.Hom.stalkMap g.toPushforwardStructure x (c j)), ?_⟩
    rw [map_sum, ← hc]
    exact Finset.sum_congr rfl fun j _ ↦ stalkMap_map_ιFree_pushforwardFreeDesc g hJ m x j (c j)

/-- **The comparison morphism `g_* (𝒪_Y^ι) ⟶ J` attached to a family `m` of global sections of
`J` is an isomorphism as soon as, at every point `x`, the germs of the `m j` generate the
stalk of `J` over `𝒪_{X, x}` and their only relations have coefficients in the stalk of the
kernel ideal sheaf of `g`.**

This is the form of `AlgebraicGeometry.Scheme.IdealSheafData.isIso_pushforwardFreeDesc` for
callers holding the stalk of `J` as a sheaf of modules rather than as an ideal of
`𝒪_{X, x}`. -/
theorem isIso_pushforwardFreeDesc_of_germ (hJ : g.ker * J = 0) (m : ι → Γ(J.toModules, ⊤))
    (hker : ∀ (x : X) (c : ι → X.presheaf.stalk x),
      ∑ j : ι, c j • J.toModules.presheaf.germ ⊤ x trivial (m j) = 0 →
        ∀ j, c j ∈ g.ker.stalkIdeal x)
    (hspan : ∀ (x : X) (v : J.toModules.presheaf.stalk x),
      ∃ c : ι → X.presheaf.stalk x,
        ∑ j : ι, c j • J.toModules.presheaf.germ ⊤ x trivial (m j) = v) :
    IsIso (pushforwardFreeDesc g hJ m) := by
  refine isIso_pushforwardFreeDesc_of_stalkMap g hJ m (fun x c hc j ↦ ?_) fun x v ↦ ?_
  · rw [stalkMap_toPushforwardStructure_eq_zero_iff]
    refine hker x (fun k ↦ Modules.stalkStructureModulesLinearEquiv X x (c k)) ?_ j
    simpa only [Modules.Hom.stalkMap_homOfSectionTop] using hc
  · obtain ⟨c, hc⟩ := hspan x v
    refine ⟨fun j ↦ (Modules.stalkStructureModulesLinearEquiv X x).symm (c j), ?_⟩
    simpa only [Modules.Hom.stalkMap_homOfSectionTop, LinearEquiv.apply_symm_apply] using hc

/-- **The comparison morphism `g_* (𝒪_Y^ι) ⟶ J` attached to a family `m` of global sections of
an ideal sheaf `J` with `g.ker * J = 0` is an isomorphism as soon as, at every point `x` of
`X`, the germs `aⱼ` of the `m j` generate the stalk `J_x ≤ 𝒪_{X, x}` and their only relations
`∑ⱼ cⱼ aⱼ = 0` have all their coefficients in the stalk of `g.ker`.**

The morphism being inverted is the one whose `j`-th leg is multiplication by `m j`:

```
  g_* 𝒪_Y ──g_* (ιFree j)──▶ g_* (𝒪_Y^ι)
        ╲                         │
  · m j  ╲                        │ pushforwardFreeDesc g hJ m
          ╲                       ▼
           ╲────────────────────▶ J
```

This is the geometric half of the identification of an ideal sheaf killed by `g.ker` with a
free module on the closed subscheme cut out by `g.ker`: both hypotheses are statements about
ideals of the single local ring `𝒪_{X, x}`, in the shape that the equational criterion of
flatness produces (`Ideal.ker_linearCombination_eq_pi` and
`Ideal.range_linearCombination_algebraMap`). Only the inclusion `≤` of the spanning hypothesis
has content: the reverse one is
`AlgebraicGeometry.Scheme.IdealSheafData.span_germ_toModulesι_app_le_stalkIdeal`. -/
theorem isIso_pushforwardFreeDesc (hJ : g.ker * J = 0) (m : ι → Γ(J.toModules, ⊤))
    (hker : ∀ (x : X) (c : ι → X.presheaf.stalk x),
      ∑ j : ι, c j * X.presheaf.germ ⊤ x trivial (J.toModulesι.app ⊤ (m j)) = 0 →
        ∀ j, c j ∈ g.ker.stalkIdeal x)
    (hspan : ∀ x : X, J.stalkIdeal x ≤
      Ideal.span (Set.range fun j : ι ↦
        X.presheaf.germ ⊤ x trivial (J.toModulesι.app ⊤ (m j)))) :
    IsIso (pushforwardFreeDesc g hJ m) := by
  refine isIso_pushforwardFreeDesc_of_germ g hJ m (fun x c hc j ↦ ?_) fun x v ↦ ?_
  · refine hker x c ?_ j
    rw [← J.stalkIdealι_sum_smul_germ x m c, hc, map_zero]
  · have hv : J.stalkIdealι x v ∈ Ideal.span (Set.range fun j : ι ↦
        X.presheaf.germ ⊤ x trivial (J.toModulesι.app ⊤ (m j))) := by
      refine hspan x ?_
      rw [← J.range_stalkIdealι x]
      exact LinearMap.mem_range_self _ v
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun _).mp hv
    refine ⟨c, J.stalkIdealι_injective x ?_⟩
    rw [J.stalkIdealι_sum_smul_germ x m c, ← hc]
    exact Finset.sum_congr rfl fun j _ ↦ (smul_eq_mul _ _).symm

end PushforwardDesc

/-! ### Base change for the comparison morphism -/

section BaseChange

variable {W₀ W₁ W'₀ W'₁ : Scheme.{u}} {i₀ : W₀ ⟶ W₁} {g : W'₁ ⟶ W₁} {g₀ : W'₀ ⟶ W₀}
  {i'₀ : W'₀ ⟶ W'₁} [QuasiCompact i₀] [Epi i₀.toPushforwardStructure] [QuasiCompact i'₀]
  [Epi i'₀.toPushforwardStructure] {J : W₁.IdealSheafData} {J' : W'₁.IdealSheafData}

/-- **Multiplication by a global section of an ideal sheaf commutes with base change.**

Let `g₀ ≫ i₀ = i'₀ ≫ g` be a commutative square, let `J` and `J'` be ideal sheaves killed by
the kernels of `i₀` and of `i'₀`, with `g` pulling `J` into `J'`, and let `s` and `s'` be global
sections of `J` and of `J'` that correspond under `g`. Then multiplication by `s` and
multiplication by `s'` agree across the square:

```
  g^*(i₀_* 𝒪_{W₀}) ──g^*(· s)──▶ g^* J ──comapModulesMap──▶ J'
          │                                                 ▲
          │ baseChange                                      │ · s'
          ▼                                                 │
  i'₀_*(g₀^* 𝒪_{W₀}) ───i'₀_* pullbackUnitIso───▶ i'₀_* 𝒪_{W'₀}
```

Both sides are computed by cancelling the epimorphism `g^*(𝒪_{W₁} ⟶ i₀_* 𝒪_{W₀})`, which turns
them into multiplication by the two sections read in the structure sheaves; there
`AlgebraicGeometry.Scheme.Modules.pullback_map_toPushforwardStructure_comp_baseChange` moves the
base change morphism out of the way. -/
lemma pullback_map_pushforwardStructureDesc_comp_comapModulesMap
    (hJ : i₀.ker * J = 0) (hJ' : i'₀.ker * J' = 0) (hg : J.comap g ≤ J') (w : g₀ ≫ i₀ = i'₀ ≫ g)
    (s : Γ(J.toModules, ⊤)) (s' : Γ(J'.toModules, ⊤))
    (hss' : g.appTop (Modules.Hom.app J.toModulesι ⊤ s) = Modules.Hom.app J'.toModulesι ⊤ s') :
    (Modules.pullback g).map (pushforwardStructureDesc i₀ hJ s) ≫ comapModulesMap J J' g hg =
      (Modules.baseChange w).natTrans.app W₀.structureModules ≫
        (Modules.pushforward i'₀).map (Modules.pullbackUnitIso g₀).hom ≫
          pushforwardStructureDesc i'₀ hJ' s' := by
  have hfinal : (Modules.pullback g).map
        (Modules.homOfSectionTop W₁.structureModules (Modules.Hom.app J.toModulesι ⊤ s)) ≫
        (Modules.pullbackUnitIso g).hom =
      (Modules.pullbackUnitIso g).hom ≫
        Modules.homOfSectionTop W'₁.structureModules (Modules.Hom.app J'.toModulesι ⊤ s') := by
    refine ((Modules.pullbackUnitIso g).inv_comp_eq).mp ?_
    rw [← Category.assoc, Modules.map_homOfSectionTop, Modules.homOfSectionTop_comp]
    exact congrArg (Modules.homOfSectionTop W'₁.structureModules)
      ((Modules.app_pullbackUnitIso_hom_sectionsPullback g
        (Modules.Hom.app J.toModulesι ⊤ s)).trans hss')
  rw [← cancel_epi ((Modules.pullback g).map i₀.toPushforwardStructure),
    ← Category.assoc ((Modules.pullback g).map i₀.toPushforwardStructure), ← Functor.map_comp,
    toPushforwardStructure_comp_pushforwardStructureDesc,
    reassoc_of% (Modules.pullback_map_toPushforwardStructure_comp_baseChange w),
    toPushforwardStructure_comp_pushforwardStructureDesc,
    ← cancel_mono J'.toModulesι, Category.assoc, Category.assoc, comapModulesMap_toModulesι,
    Modules.homOfSectionTop_comp, ← Category.assoc, ← Functor.map_comp,
    Modules.homOfSectionTop_comp, hfinal]

/-- **The comparison morphism attached to a family of global sections of an ideal sheaf commutes
with base change**: the free version of
`IdealSheafData.pullback_map_pushforwardStructureDesc_comp_comapModulesMap`, obtained from it
summand by summand.

```
  g^*(i₀_*(𝒪_{W₀}^ι)) ──g^* Φ──▶ g^* J ──comapModulesMap──▶ J'
            │                                               ▲
            │ baseChange                                    │ Φ'
            ▼                                               │
  i'₀_*(g₀^*(𝒪_{W₀}^ι)) ──i'₀_* pullbackFreeIso──▶ i'₀_*(𝒪_{W'₀}^ι)
```
-/
lemma pullback_map_pushforwardFreeDesc_comp_comapModulesMap {ι : Type u} [Finite ι]
    (hJ : i₀.ker * J = 0) (hJ' : i'₀.ker * J' = 0) (hg : J.comap g ≤ J') (w : g₀ ≫ i₀ = i'₀ ≫ g)
    (m : ι → Γ(J.toModules, ⊤)) (m' : ι → Γ(J'.toModules, ⊤))
    (hmm' : ∀ j, g.appTop (Modules.Hom.app J.toModulesι ⊤ (m j)) =
      Modules.Hom.app J'.toModulesι ⊤ (m' j)) :
    (Modules.pullback g).map (pushforwardFreeDesc i₀ hJ m) ≫ comapModulesMap J J' g hg =
      (Modules.baseChange w).natTrans.app (W₀.freeModules ι) ≫
        (Modules.pushforward i'₀).map (Modules.pullbackFreeIso g₀ ι).hom ≫
          pushforwardFreeDesc i'₀ hJ' m' := by
  refine Modules.pullback_pushforwardFree_hom_ext i₀ g fun j ↦ ?_
  have key : (Modules.pullback g).map ((Modules.pushforward i₀).map
        (SheafOfModules.ιFree (R := W₀.ringCatSheaf) (I := ι) j)) ≫
      (Modules.baseChange w).natTrans.app (W₀.freeModules ι) =
      (Modules.baseChange w).natTrans.app W₀.structureModules ≫
        (Modules.pushforward i'₀).map ((Modules.pullback g₀).map (SheafOfModules.ιFree j)) :=
    (Modules.baseChange w).natTrans.naturality _
  rw [← Category.assoc ((Modules.pullback g).map ((Modules.pushforward i₀).map
      (SheafOfModules.ιFree j))), ← Functor.map_comp, map_ιFree_comp_pushforwardFreeDesc,
    reassoc_of% key, ← Functor.map_comp_assoc,
    Modules.pullback_map_ιFree_comp_pullbackFreeIso_hom, Functor.map_comp_assoc,
    map_ιFree_comp_pushforwardFreeDesc]
  exact pullback_map_pushforwardStructureDesc_comp_comapModulesMap hJ hJ' hg w (m j) (m' j)
    (hmm' j)

end BaseChange

end AlgebraicGeometry.Scheme.IdealSheafData
