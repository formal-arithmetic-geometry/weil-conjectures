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
- `AlgebraicGeometry.Scheme.IdealSheafData.idealOfOpens` — the ideal cut out on an arbitrary
  open subset, extending `J.ideal` off the affine opens.
- `AlgebraicGeometry.Scheme.IdealSheafData.sectionOfMem` — the section of the ideal sheaf
  lying over a section of `𝒪_X` that belongs to the ideal.

## Main results

- `AlgebraicGeometry.Scheme.IdealSheafData.range_toModulesι_app` — over an affine open `U`,
  the sections of `J.toModules` are exactly `J.ideal U`, which is what makes the definition
  the right one.
- `AlgebraicGeometry.Scheme.IdealSheafData.injective_toModulesι_app` — the inclusion is
  injective on sections over every open, affine or not.
- `AlgebraicGeometry.Scheme.IdealSheafData.mem_idealOfOpens_iff_forall_affineOpens` — the
  ideal cut out on an arbitrary open subset is detected on the affine opens it contains, and
  `AlgebraicGeometry.Scheme.IdealSheafData.map_mem_idealOfOpens` — it is stable under
  restriction.
- `AlgebraicGeometry.Scheme.IdealSheafData.mul_eq_zero_of_mem_idealOfOpens` — **two ideal
  sheaves whose product vanishes annihilate each other on sections**, over an arbitrary open
  subset; together with `AlgebraicGeometry.Scheme.Hom.mem_idealOfOpens_ker`, which says that a
  section killed by a quasi-compact morphism lies in its kernel ideal sheaf.
- `AlgebraicGeometry.Scheme.IdealSheafData.range_stalkMap_toModulesι` and
  `AlgebraicGeometry.Scheme.IdealSheafData.mem_range_stalkMap_toModulesι_iff` — the stalk of
  the ideal sheaf is the set of germs killed by the restriction to the closed subscheme, that
  is, the set of germs of sections lying in the ideal, and
  `AlgebraicGeometry.Scheme.IdealSheafData.injective_stalkMap_toModulesι` — the inclusion is
  injective on stalks.
- `AlgebraicGeometry.Scheme.IdealSheafData.shortExact_toModulesι_toPushforwardSubscheme` —
  **`0 ⟶ J.toModules ⟶ 𝒪_X ⟶ (ι_J)_* 𝒪_{V(J)} ⟶ 0` is a short exact sequence**, so that
  `(ι_J)_* 𝒪_{V(J)}` is the quotient of `𝒪_X` by the ideal sheaf and a morphism out of `𝒪_X`
  killing the ideal sheaf descends to it through
  `AlgebraicGeometry.Scheme.Hom.descPushforwardStructure`.
- `AlgebraicGeometry.Scheme.IdealSheafData.comapModulesMap` — the comparison morphism
  `g^* I ⟶ I'` for a morphism `g` pulling the ideal `I` into the ideal `I'`, together with
  `comapModulesMap_toModulesι` and `eq_comapModulesMap`, which determine it.

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

/-- The section of the ideal sheaf lying over a section of `𝒪_X` that belongs to the ideal. -/
noncomputable def sectionOfMem {U : X.Opens} {x : Γ(X, U)} (hx : x ∈ J.idealOfOpens U) :
    Γ(J.toModules, U) :=
  ((J.range_toModulesι_app_eq_idealOfOpens U).ge hx).choose

@[simp]
lemma toModulesι_app_sectionOfMem {U : X.Opens} {x : Γ(X, U)} (hx : x ∈ J.idealOfOpens U) :
    J.toModulesι.app U (J.sectionOfMem hx) = x :=
  ((J.range_toModulesι_app_eq_idealOfOpens U).ge hx).choose_spec

/-! ### The ideal on an arbitrary open is determined by the affine opens it contains -/

/-- Membership in the ideal cut out on an open subset is stable under restriction. -/
lemma map_mem_idealOfOpens {U V : X.Opens} (h : V ≤ U) {x : Γ(X, U)}
    (hx : x ∈ J.idealOfOpens U) :
    X.presheaf.map (homOfLE h).op x ∈ J.idealOfOpens V := by
  rw [mem_idealOfOpens_iff] at hx ⊢
  have hnat := ConcreteCategory.congr_hom (J.subschemeι.naturality (homOfLE h).op) x
  simp only [CommRingCat.comp_apply] at hnat
  rw [hnat, hx, map_zero]

/-- **The ideal cut out on an arbitrary open subset is detected on the affine opens it
contains**: a section of `𝒪_X` over `U` lies in `J.idealOfOpens U` exactly when its restriction
to every affine open `V ≤ U` lies in `J.ideal V`.

This is what makes `AlgebraicGeometry.Scheme.IdealSheafData.idealOfOpens` computable from the
data recorded by `J`, which is only the family of ideals over the affine opens. -/
lemma mem_idealOfOpens_iff_forall_affineOpens {U : X.Opens} {x : Γ(X, U)} :
    x ∈ J.idealOfOpens U ↔
      ∀ (V : X.affineOpens) (h : V.1 ≤ U), X.presheaf.map (homOfLE h).op x ∈ J.ideal V := by
  refine ⟨fun hx V h ↦ ?_, fun H ↦ ?_⟩
  · rw [← idealOfOpens_eq_ideal]
    exact J.map_mem_idealOfOpens h hx
  · rw [mem_idealOfOpens_iff]
    refine TopCat.Presheaf.section_ext ⟨J.subscheme.presheaf, J.subscheme.sheaf.2⟩ _ _ 0
      fun y hy ↦ ?_
    obtain ⟨_, ⟨V, hV, rfl⟩, hyV, hVU⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open (u := U.1) hy U.2
    have hVU' : V ≤ U := hVU
    have hle : J.subschemeι ⁻¹ᵁ V ≤ J.subschemeι ⁻¹ᵁ U := fun z hz ↦ hVU' hz
    have hnat := ConcreteCategory.congr_hom (J.subschemeι.naturality (homOfLE hVU').op) x
    simp only [CommRingCat.comp_apply, Quiver.Hom.unop_op] at hnat
    have hmem : X.presheaf.map (homOfLE hVU').op x ∈ J.idealOfOpens V := by
      rw [idealOfOpens_eq_ideal J ⟨V, hV⟩]
      exact H ⟨V, hV⟩ hVU'
    have hres : J.subscheme.presheaf.map (homOfLE hle).op (J.subschemeι.app U x) = 0 := by
      rw [show (homOfLE hle : J.subschemeι ⁻¹ᵁ V ⟶ J.subschemeι ⁻¹ᵁ U) =
        (TopologicalSpace.Opens.map J.subschemeι.base).map (homOfLE hVU') from
          Subsingleton.elim _ _, ← hnat, (mem_idealOfOpens_iff (J := J)).mp hmem]
    have hgerm := TopCat.Presheaf.germ_res_apply J.subscheme.presheaf (homOfLE hle) y hyV
      (J.subschemeι.app U x)
    rw [hres, map_zero] at hgerm
    simpa only [map_zero] using hgerm.symm

/-- **Two ideal sheaves whose product vanishes annihilate each other on sections**, over an
arbitrary open subset: if `I * J = 0` and `a`, `b` are sections of `𝒪_X` over `U` lying in `I`
and in `J` respectively, then `a * b = 0`.

Multiplication of ideal sheaves is defined on the affine opens only, so the proof restricts to
an affine open, where it is `Ideal.mul_mem_mul`, and then uses the sheaf condition. -/
lemma mul_eq_zero_of_mem_idealOfOpens {I J : X.IdealSheafData} (hIJ : I * J = 0) {U : X.Opens}
    {a b : Γ(X, U)} (ha : a ∈ I.idealOfOpens U) (hb : b ∈ J.idealOfOpens U) : a * b = 0 := by
  refine TopCat.Presheaf.section_ext ⟨X.presheaf, X.sheaf.2⟩ U _ 0 fun y hy ↦ ?_
  obtain ⟨_, ⟨V, hV, rfl⟩, hyV, hVU⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open hy U.2
  have hVU' : V ≤ U := hVU
  have ha' : X.presheaf.map (homOfLE hVU').op a ∈ I.ideal ⟨V, hV⟩ := by
    rw [← idealOfOpens_eq_ideal]
    exact I.map_mem_idealOfOpens hVU' ha
  have hb' : X.presheaf.map (homOfLE hVU').op b ∈ J.ideal ⟨V, hV⟩ := by
    rw [← idealOfOpens_eq_ideal]
    exact J.map_mem_idealOfOpens hVU' hb
  have hbot : I.ideal ⟨V, hV⟩ * J.ideal ⟨V, hV⟩ = ⊥ := by
    rw [show I.ideal ⟨V, hV⟩ * J.ideal ⟨V, hV⟩ = (I * J).ideal ⟨V, hV⟩ from rfl, hIJ]
    rfl
  have hmul : X.presheaf.map (homOfLE hVU').op (a * b) = 0 := by
    rw [map_mul]
    simpa [hbot] using Ideal.mul_mem_mul ha' hb'
  have hgerm := TopCat.Presheaf.germ_res_apply X.presheaf (homOfLE hVU') y hyV (a * b)
  rw [hmul] at hgerm
  simpa only [map_zero] using hgerm.symm

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
lemma injective_stalkMap_toModulesι : Function.Injective (J.toModulesι.stalkMap x) :=
  Modules.injective_stalkMap_kernelι J.toPushforwardSubscheme x

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

end AlgebraicGeometry.Scheme.IdealSheafData

namespace AlgebraicGeometry.Scheme.Hom

open IdealSheafData

variable {X Y : Scheme.{u}} (g : Y ⟶ X) [QuasiCompact g]

/-- **A section of `𝒪_X` killed by `g` lies in the kernel ideal sheaf of `g`**, over an
arbitrary open subset. Over an affine open this is `AlgebraicGeometry.Scheme.Hom.ker_apply`;
the general case follows because `AlgebraicGeometry.Scheme.IdealSheafData.idealOfOpens` is
detected on affine opens. -/
lemma mem_idealOfOpens_ker {U : X.Opens} {x : Γ(X, U)} (hx : g.app U x = 0) :
    x ∈ g.ker.idealOfOpens U := by
  rw [mem_idealOfOpens_iff_forall_affineOpens]
  intro V h
  rw [ker_apply, RingHom.mem_ker]
  have hnat := ConcreteCategory.congr_hom (g.naturality (homOfLE h).op) x
  simp only [CommRingCat.comp_apply] at hnat
  rw [hnat, hx, map_zero]

end AlgebraicGeometry.Scheme.Hom
