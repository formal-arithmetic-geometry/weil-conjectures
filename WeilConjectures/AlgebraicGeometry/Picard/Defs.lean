/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Subfunctor.Basic
public import WeilConjectures.AlgebraicGeometry.PicardFunctor

/-!
# The relative Picard functor and its `σ`-normalized version

For a morphism of schemes `f : X ⟶ S` the Picard presheaf
`AlgebraicGeometry.picardPresheaf f : (Over S)ᵒᵖ ⥤ Type (u + 1)` sends a scheme `T` over `S` to
the Picard group of the fibre `X_T = X ×[S] T`.  In this file we define the relative Picard
functor `Pic_{X/S}` as the fppf sheafification of this presheaf, and, for a section `σ` of `f`,
the `σ`-normalized relative Picard functor `Pic_{X/S,σ}`, the subfunctor of `picardPresheaf f`
consisting of the classes `ℒ` whose pullback along the base-changed section `σ_T` is trivial.

We then state the two basic facts about them: the split exact sequence comparing `Pic (X_T)`
with `Pic T` and `Pic_{X/S}(T)`, and the fact that `Pic_{X/S,σ}` is an fppf sheaf.

## Implementation notes

`AlgebraicGeometry.Scheme.Pic` carries no group structure yet — that would require a tensor
product of sheaves of modules, which is still a placeholder — so the exactness of
`0 → Pic T → Pic (X_T) → Pic_{X/S}(T) → 0` is stated in the equivalent group-free form: the
three theorems `injective_pic_map_snd`, `pic_map_sectionBaseChange_snd`,
`bijective_toPicardFunctor_picardFunctorNormalized` and `bijective_pic_split` below.

## Main definitions

- `AlgebraicGeometry.picardFunctor`: the relative Picard functor `Pic_{X/S}`, the fppf
  sheafification of `AlgebraicGeometry.picardPresheaf` (blueprint `sk-def-picard-pic`).
- `AlgebraicGeometry.picardFunctorNormalized`: the `σ`-normalized relative Picard functor
  `Pic_{X/S,σ}` (blueprint `sk-def-picard-pic`).

## Main statements

- `AlgebraicGeometry.injective_pic_map_snd`,
  `AlgebraicGeometry.pic_map_sectionBaseChange_snd`,
  `AlgebraicGeometry.bijective_toPicardFunctor_picardFunctorNormalized` and
  `AlgebraicGeometry.bijective_pic_split`: the split exact sequence
  `0 → Pic T → Pic (X_T) → Pic_{X/S}(T) → 0` (blueprint `sk-prop-picard-pic-split`).
- `AlgebraicGeometry.isSheaf_picardFunctorNormalized`: the `σ`-normalized relative Picard
  functor is an fppf sheaf (blueprint `sk-cor-picard-pic-sheaf`).
- `AlgebraicGeometry.nonempty_picardFunctor_iso_of_isPullback`: the relative Picard functor is
  compatible with base change (blueprint `lem-pd-picard-base-change`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

open Scheme

variable {X S : Scheme.{u}}

/-- The base change to `T` of a section `σ` of `f : X ⟶ S`, as a section
`σ_T : T ⟶ X ×[S] T` of the projection `X_T ⟶ T`. -/
noncomputable abbrev sectionBaseChange (f : X ⟶ S) (σ : S ⟶ X) (hσ : σ ≫ f = 𝟙 S) (T : Over S) :
    T.left ⟶ Limits.pullback f T.hom :=
  Limits.pullback.lift (T.hom ≫ σ) (𝟙 T.left) (by
    rw [Category.assoc, hσ, Category.comp_id, Category.id_comp])

@[reassoc (attr := simp)]
lemma sectionBaseChange_snd (f : X ⟶ S) (σ : S ⟶ X) (hσ : σ ≫ f = 𝟙 S) (T : Over S) :
    sectionBaseChange f σ hσ T ≫ Limits.pullback.snd f T.hom = 𝟙 T.left :=
  Limits.pullback.lift_snd _ _ _

/-- The canonical morphism `𝒪_S ⟶ f_* 𝒪_X` of sheaves of `𝒪_S`-modules attached to a morphism
of schemes `f : X ⟶ S`, obtained from the unit of the adjunction `f^* ⊣ f_*` together with the
identification `f^* 𝒪_S ≅ 𝒪_X`:

```
                       η
    𝒪_S ──────────────────────────────▶ f_* f^* 𝒪_S
      ╲                                      │
       ╲                            f_*(f^* 𝒪_S ≅ 𝒪_X)
        ╲                                    │
         ╲                                   ▼
          ╲─────────────────────────────▶ f_* 𝒪_X
```
-/
noncomputable abbrev pushforwardUnitMap (f : X ⟶ S) :
    SheafOfModules.unit S.ringCatSheaf ⟶
      (Modules.pushforward f).obj (SheafOfModules.unit X.ringCatSheaf) :=
  (Modules.pullbackPushforwardAdjunction f).unit.app (SheafOfModules.unit S.ringCatSheaf) ≫
    (Modules.pushforward f).map (Modules.pullbackObjUnitIso f).hom

/-- The relative Picard functor `Pic_{X/S}` of a morphism of schemes `f : X ⟶ S`: the fppf
sheafification of the Picard presheaf `T ↦ Pic (X_T)`, so that on the level of sections
`Pic_{X/S}(T)` is the fppf-sheafified version of `Pic (X_T) / pr_T^* Pic T`.

The fppf topology on the category `Over S` of schemes over `S` is the localization
`Scheme.fppfTopology.over S` of the fppf topology on all schemes.

(blueprint: `sk-def-picard-pic`) -/
noncomputable def picardFunctor (f : X ⟶ S) :
    Sheaf (Scheme.fppfTopology.over S) (Type (u + 1)) :=
  (presheafToSheaf (Scheme.fppfTopology.over S) (Type (u + 1))).obj (picardPresheaf f)

/-- The canonical map from the Picard presheaf of `f : X ⟶ S` to the relative Picard functor,
i.e. the unit of the fppf sheafification adjunction. -/
noncomputable abbrev toPicardFunctor (f : X ⟶ S) : picardPresheaf f ⟶ (picardFunctor f).obj :=
  toSheafify (Scheme.fppfTopology.over S) (picardPresheaf f)

/-- **The Picard functor is compatible with base change.** Let `f : X ⟶ S` be a morphism of
schemes, let `g : S' ⟶ S` be a morphism and let `f' : X' ⟶ S'` be the base change of `f` along
`g`. Then the restriction of `Pic_{X/S}` to schemes over `S'` is `Pic_{X'/S'}`.

For `T` over `S'` the fibre products `X ×_S T` and `X' ×_{S'} T` agree, so the two Picard presheaves
agree on schemes over `S'`; the fppf coverings of a scheme over `S'` are the same in both sites, so
their sheafifications agree as well (the remark after Stacks 0B9K).

(blueprint: `lem-pd-picard-base-change`) -/
theorem nonempty_picardFunctor_iso_of_isPullback {X' S' : Scheme.{u}} {f : X ⟶ S} {g : S' ⟶ S}
    {f' : X' ⟶ S'} {g' : X' ⟶ X} (h : IsPullback g' f' f g) :
    Nonempty ((Over.map g).op ⋙ (picardFunctor f).obj ≅ (picardFunctor f').obj) :=
  sorry

/-- The `σ`-normalized relative Picard functor `Pic_{X/S,σ}` of a morphism of schemes
`f : X ⟶ S` equipped with a section `σ`: the subfunctor of the Picard presheaf `T ↦ Pic (X_T)`
consisting of the classes `ℒ` that are trivial along the base-changed section, `σ_T^* ℒ ≅ 𝒪_T`.

This is a subfunctor because the base-changed sections are compatible: for `i : V ⟶ U` in
`Over S`, the square

```
          σ_V
     V ─────────▶ X ×[S] V
     │                │
   i.left      baseChangeMap f i
     │                │
     ▼                ▼
     U ─────────▶ X ×[S] U
          σ_U
```

commutes, so pulling a normalized class back along `baseChangeMap f i` keeps it normalized.

(blueprint: `sk-def-picard-pic`) -/
noncomputable def picardFunctorNormalized (f : X ⟶ S) (σ : S ⟶ X) (hσ : σ ≫ f = 𝟙 S) :
    Subfunctor (picardPresheaf f) where
  obj T := {L | Pic.map (sectionBaseChange f σ hσ T.unop) L =
    Pic.mk (SheafOfModules.unit T.unop.left.ringCatSheaf)}
  map := by
    rintro ⟨U⟩ ⟨V⟩ ⟨i⟩ L (hL : Pic.map _ L = _)
    -- `change` rather than `show`: the repository's linter rejects a `show` that changes the
    -- goal, and this step is a definitional unfolding of `(picardPresheaf f).map`.
    change Pic.map (sectionBaseChange f σ hσ V) (Pic.map (baseChangeMap f i) L) = _
    have h : sectionBaseChange f σ hσ V ≫ baseChangeMap f i =
        i.left ≫ sectionBaseChange f σ hσ U := by
      refine Limits.pullback.hom_ext ?_ ?_
      · simp
      · simp only [Category.assoc, limit.lift_π, PullbackCone.mk_π_app, limit.lift_π_assoc,
          cospan_right, Category.comp_id]
        apply Category.id_comp
    rw [← Pic.map_comp, h, Pic.map_comp, hL, Pic.map_mk_unit]

section Split

/-- **The pullback map `Pic T → Pic (X_T)` is injective.** This is the left-exactness half of
the split exact sequence `0 → Pic T → Pic (X_T) → Pic_{X/S}(T) → 0`, under the hypothesis that
the canonical map `𝒪_T ⟶ f_{T,*} 𝒪_{X_T}` is an isomorphism for every `T` in `(Sch/S)_fppf`
(for `X ⟶ Spec k` a smooth projective curve with a `k`-point this is `H⁰(X, 𝒪_X) = k` together
with flat base change).

(blueprint: `sk-prop-picard-pic-split`) -/
theorem injective_pic_map_snd (f : X ⟶ S)
    (hf : ∀ T : Over S, IsIso (pushforwardUnitMap (Limits.pullback.snd f T.hom)))
    (T : Over S) :
    Function.Injective (Pic.map (Limits.pullback.snd f T.hom)) :=
  sorry

/-- **The pullback map `Pic T → Pic (X_T)` is split by `σ_T^*`.**

(blueprint: `sk-prop-picard-pic-split`) -/
theorem pic_map_sectionBaseChange_snd (f : X ⟶ S) (σ : S ⟶ X) (hσ : σ ≫ f = 𝟙 S)
    (hf : ∀ T : Over S, IsIso (pushforwardUnitMap (Limits.pullback.snd f T.hom)))
    (T : Over S) (N : T.left.Pic) :
    Pic.map (sectionBaseChange f σ hσ T) (Pic.map (Limits.pullback.snd f T.hom) N) = N :=
  sorry

/-- **The normalized classes map bijectively onto `Pic_{X/S}(T)`**, so that `Pic_{X/S}` is the
fppf sheafification of `Pic_{X/S,σ}`.

(blueprint: `sk-prop-picard-pic-split`) -/
theorem bijective_toPicardFunctor_picardFunctorNormalized (f : X ⟶ S) (σ : S ⟶ X)
    (hσ : σ ≫ f = 𝟙 S)
    (hf : ∀ T : Over S, IsIso (pushforwardUnitMap (Limits.pullback.snd f T.hom)))
    (T : Over S) :
    Function.Bijective (fun L : (picardFunctorNormalized f σ hσ).toFunctor.obj (.op T) ↦
      (toPicardFunctor f).app (.op T) L.1) :=
  sorry

/-- **The splitting of the sequence**: `ℒ ↦ (σ_T^* ℒ, [ℒ])` is a bijection
`Pic (X_T) ≃ Pic T × Pic_{X/S}(T)`, i.e. `Pic (X_T) = Pic T ⊕ Pic_{X/S,σ}(T)`.

```
                          f_T^*                       [-]
     0 ──────▶ Pic T ───────────────▶ Pic (X_T) ───────────────▶ Pic_{X/S}(T) ──────▶ 0
                   ◀───────────────
                        σ_T^*
```

(blueprint: `sk-prop-picard-pic-split`) -/
theorem bijective_pic_split (f : X ⟶ S) (σ : S ⟶ X) (hσ : σ ≫ f = 𝟙 S)
    (hf : ∀ T : Over S, IsIso (pushforwardUnitMap (Limits.pullback.snd f T.hom)))
    (T : Over S) :
    Function.Bijective (fun L : (Limits.pullback f T.hom).Pic ↦
      (Pic.map (sectionBaseChange f σ hσ T) L, (toPicardFunctor f).app (.op T) L)) :=
  sorry

end Split

/-- **The `σ`-normalized Picard functor is an fppf sheaf.** The relative Picard functor
`Pic_{X/S}` is an fppf sheaf, hence a Zariski sheaf, simply because it is defined as an fppf
sheafification: this is `(AlgebraicGeometry.picardFunctor f).cond`, so only the second half of
the corollary carries content. Namely, if `f` has a section `σ` and the canonical map
`𝒪_T ⟶ f_{T,*} 𝒪_{X_T}` is an isomorphism for every `T` in `(Sch/S)_fppf`, then
`Pic_{X/S,σ}(T) = ker σ_T^*` is an fppf sheaf as well.

(blueprint: `sk-cor-picard-pic-sheaf`) -/
theorem isSheaf_picardFunctorNormalized (f : X ⟶ S) (σ : S ⟶ X) (hσ : σ ≫ f = 𝟙 S)
    (hf : ∀ T : Over S, IsIso (pushforwardUnitMap (Limits.pullback.snd f T.hom))) :
    Presheaf.IsSheaf (Scheme.fppfTopology.over S)
      (picardFunctorNormalized f σ hσ).toFunctor :=
  sorry

end AlgebraicGeometry
