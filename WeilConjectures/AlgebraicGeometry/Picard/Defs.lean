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
public import WeilConjectures.AlgebraicGeometry.Modules.Dual
public import WeilConjectures.AlgebraicGeometry.Modules.ProjectionFormula
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

`AlgebraicGeometry.Scheme.Pic` carries no group structure yet, so the exactness of
`0 → Pic T → Pic (X_T) → Pic_{X/S}(T) → 0` is stated in the equivalent group-free form: the
four theorems `injective_pic_map_snd`, `pic_map_sectionBaseChange_snd`,
`bijective_toPicardFunctor_picardFunctorNormalized` and `bijective_pic_split` below.  Likewise
the exactness in the middle, `toPicardFunctor_app_eq_iff`, says that two classes have the same
image in `Pic_{X/S}(T)` if and only if they differ by a class pulled back from `T`, the
difference being expressed with the tensor product of modules.

## Main definitions

- `AlgebraicGeometry.picardFunctor`: the relative Picard functor `Pic_{X/S}`, the fppf
  sheafification of `AlgebraicGeometry.picardPresheaf` (blueprint `sk-def-picard-pic`).
- `AlgebraicGeometry.picardFunctorNormalized`: the `σ`-normalized relative Picard functor
  `Pic_{X/S,σ}` (blueprint `sk-def-picard-pic`).

## Main statements

- `AlgebraicGeometry.toPicardFunctor_app_eq_iff`: the exactness of
  `Pic T → Pic (X_T) → Pic_{X/S}(T)` in the middle (blueprint `lem-pc-pic-exact`).
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

open CategoryTheory Limits MonoidalCategory

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

/-- The base-changed sections are compatible with base change: for `i : V ⟶ U` in `Over S`,
`σ_U ∘ i = (X ×_S i) ∘ σ_V`. -/
lemma sectionBaseChange_comp_baseChangeMap (f : X ⟶ S) (σ : S ⟶ X) (hσ : σ ≫ f = 𝟙 S)
    {U V : Over S} (i : V ⟶ U) :
    sectionBaseChange f σ hσ V ≫ baseChangeMap f i = i.left ≫ sectionBaseChange f σ hσ U := by
  refine Limits.pullback.hom_ext (by simp) ?_
  rw [Category.assoc, Limits.pullback.lift_snd, sectionBaseChange_snd_assoc]
  simp

/-- Pulling back along the projection `f_T : X_T ⟶ T` and then along the section `σ_T` is the
identity: `σ_T^* f_T^* N ≅ N`. -/
noncomputable def pullbackSectionBaseChangeSndIso (f : X ⟶ S) (σ : S ⟶ X) (hσ : σ ≫ f = 𝟙 S)
    (T : Over S) (N : T.left.Modules) :
    (Modules.pullback (sectionBaseChange f σ hσ T)).obj
      ((Modules.pullback (Limits.pullback.snd f T.hom)).obj N) ≅ N :=
  (Modules.pullbackComp _ _).app N ≪≫
    (Modules.pullbackCongr (sectionBaseChange_snd f σ hσ T)).app N ≪≫
    (Modules.pullbackId _).app N

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

The blueprint asserts that the restriction *is* `Pic_{X'/S'}`, through the canonical
identification induced by `X' ×_{S'} T = X ×_S T`. The statement here only asserts that some
isomorphism exists, which is weaker; this suffices for the current applications.

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
    rw [← Pic.map_comp, sectionBaseChange_comp_baseChangeMap, Pic.map_comp, hL, Pic.map_mk_unit]

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

section Pic

namespace Scheme.Pic

variable {Y Z : Scheme.{u}}

/-- If the pullback of a class `N` along `g` is trivial, then the pullback of its representative
is isomorphic to the structure sheaf. -/
lemma nonempty_iso_unit_of_map_eq (g : Z ⟶ Y) {N : Y.Pic}
    (h : Pic.map g N = Pic.mk (SheafOfModules.unit Z.ringCatSheaf)) :
    Nonempty ((Modules.pullback g).obj ((fromSkeleton Y.Modules).obj N.val) ≅
      SheafOfModules.unit Z.ringCatSheaf) := by
  obtain ⟨e⟩ := Pic.eq_iff_nonempty_iso.1 h
  exact ⟨(fromSkeletonToSkeletonIso _).symm ≪≫ e ≪≫ fromSkeletonToSkeletonIso _⟩

/-- **Invertible modules are Zariski-locally trivial**: every point `y` has an open
neighbourhood `U` such that the restriction of the class `L` to `U` is trivial. -/
lemma exists_map_ι_eq_mk_unit (L : Y.Pic) (y : Y) :
    ∃ U : Y.Opens, y ∈ U ∧
      Pic.map U.ι L = Pic.mk (SheafOfModules.unit U.toScheme.ringCatSheaf) := by
  have := L.isInvertible
  obtain ⟨U, hy, ⟨e⟩⟩ := Modules.exists_mem_over_iso_unit ((fromSkeleton Y.Modules).obj L.val) y
  exact ⟨U, hy, Pic.ext (congr_toSkeleton_of_iso (Modules.pullbackIotaUnitIsoOfOverIso e))⟩

end Scheme.Pic

end Pic

section Exactness

/-- Twisting by a class pulled back from the base does not change the image in the relative
Picard functor: if `ℒ ≅ ℒ' ⊗ f_T^* 𝒩` for an invertible `𝒪_T`-module `𝒩`, then `ℒ` and `ℒ'` have
the same image in `Pic_{X/S}(T)`.  Indeed `𝒩` is trivial on the members `U` of a Zariski
covering of `T`, which is an fppf covering, and there `ℒ|_{X_U} ≅ ℒ'|_{X_U}`.

This is the inclusion "image ⊆ kernel" of blueprint `lem-pc-pic-exact`. -/
theorem toPicardFunctor_app_eq_of_iso (f : X ⟶ S) {T : Over S}
    (L L' : (Limits.pullback f T.hom).Pic) (N : T.left.Pic)
    (e : (fromSkeleton _).obj L.val ≅ (fromSkeleton _).obj L'.val ⊗
      (Modules.pullback (Limits.pullback.snd f T.hom)).obj ((fromSkeleton _).obj N.val)) :
    (toPicardFunctor f).app (.op T) L = (toPicardFunctor f).app (.op T) L' := by
  choose U hU hUN using fun t ↦ Pic.exists_map_ι_eq_mk_unit N t
  let V (t : T.left) : Over S := Over.mk ((U t).ι ≫ T.hom)
  let i (t : T.left) : V t ⟶ T := Over.homMk (U t).ι
  have hR : Sieve.ofArrows V i ∈ fppfTopology.over S T := by
    rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows]
    refine Precoverage.generate_mem_toGrothendieck ?_
    rw [fppfPrecoverage, ofArrows_mem_precoverage_iff]
    exact ⟨fun t ↦ ⟨t, ⟨t, hU t⟩, rfl⟩, fun t ↦ ⟨inferInstanceAs (Flat (U t).ι),
      inferInstanceAs (LocallyOfFinitePresentation (U t).ι)⟩⟩
  refine (((isSheaf_iff_isSheaf_of_type _ _).1 (picardFunctor f).property).isSeparated _
    hR).ext ?_
  rintro _ _ ⟨W, a, _, ⟨t⟩, rfl⟩
  suffices h : (picardPresheaf f).map (i t).op L = (picardPresheaf f).map (i t).op L' by
    rw [op_comp, Functor.map_comp_apply, Functor.map_comp_apply,
      ← NatTrans.naturality_apply (toPicardFunctor f) (i t).op L,
      ← NatTrans.naturality_apply (toPicardFunctor f) (i t).op L', h]
  obtain ⟨eN⟩ := Pic.nonempty_iso_unit_of_map_eq _ (hUN t)
  have hsq : baseChangeMap f (i t) ≫ Limits.pullback.snd f T.hom =
      Limits.pullback.snd f (V t).hom ≫ (U t).ι :=
    Limits.pullback.lift_snd _ _ _
  refine Pic.eq_iff_nonempty_iso.2 ⟨fromSkeletonToSkeletonIso _ ≪≫
    (Modules.pullback _).mapIso e ≪≫ (Modules.nonempty_pullback_tensorObj_iso _ _ _).some ≪≫
    (Iso.refl _ ⊗ᵢ ((Modules.pullbackComp _ _).app _ ≪≫
      (Modules.pullbackCongr hsq).app _ ≪≫ ((Modules.pullbackComp _ _).app _).symm ≪≫
      (Modules.pullback _).mapIso eN ≪≫ Modules.pullbackObjUnitIso _)) ≪≫
    ρ_ _ ≪≫ (fromSkeletonToSkeletonIso _).symm⟩

/-- **Classes with the same image in `Pic_{X/S}(T)` differ by a class from the base.** Assume
that `𝒪_T ⟶ f_{T,*} 𝒪_{X_T}` is an isomorphism for every `T` in `(Sch/S)_fppf`.  If two classes
`ℒ, ℒ' ∈ Pic (X_T)` have the same image in `Pic_{X/S}(T)`, then `ℒ ≅ ℒ' ⊗ f_T^* 𝒩` for an
invertible `𝒪_T`-module `𝒩`.

The images agree on an fppf covering `{T_i ⟶ T}`, where `ℒ ⊗ ℒ'^{-1}` is then trivial; the
transition functions of the trivializations are units of `Γ(X_{T_i ×_T T_j}, 𝒪) =
Γ(T_i ×_T T_j, 𝒪)`, hence a descent datum for an invertible `𝒪_T`-module `𝒩` (fpqc descent,
blueprint `lem-pc-fpqc-descent`), and `f_T^* 𝒩 ≅ ℒ ⊗ ℒ'^{-1}`.

This is the inclusion "kernel ⊆ image" of blueprint `lem-pc-pic-exact`. -/
theorem exists_iso_tensorObj_of_toPicardFunctor_app_eq (f : X ⟶ S)
    (hf : ∀ T : Over S, IsIso (pushforwardUnitMap (Limits.pullback.snd f T.hom))) {T : Over S}
    (L L' : (Limits.pullback f T.hom).Pic)
    (h : (toPicardFunctor f).app (.op T) L = (toPicardFunctor f).app (.op T) L') :
    ∃ N : T.left.Pic, Nonempty ((fromSkeleton _).obj L.val ≅ (fromSkeleton _).obj L'.val ⊗
      (Modules.pullback (Limits.pullback.snd f T.hom)).obj ((fromSkeleton _).obj N.val)) :=
  sorry

/-- **Exactness of the Picard sequence in the middle.** Assume that `𝒪_T ⟶ f_{T,*} 𝒪_{X_T}` is an
isomorphism for every `T` in `(Sch/S)_fppf`.  Two classes `ℒ, ℒ' ∈ Pic (X_T)` have the same image
in `Pic_{X/S}(T)` if and only if `ℒ ≅ ℒ' ⊗ f_T^* 𝒩` for an invertible `𝒪_T`-module `𝒩`: the
kernel of `Pic (X_T) ⟶ Pic_{X/S}(T)` is the image of `f_T^* : Pic T ⟶ Pic (X_T)` (Stacks 0B9M).
Together with `AlgebraicGeometry.injective_pic_map_snd` this is the exactness of
`0 → Pic T → Pic (X_T) → Pic_{X/S}(T)`.

(blueprint: `lem-pc-pic-exact`) -/
theorem toPicardFunctor_app_eq_iff (f : X ⟶ S)
    (hf : ∀ T : Over S, IsIso (pushforwardUnitMap (Limits.pullback.snd f T.hom))) {T : Over S}
    (L L' : (Limits.pullback f T.hom).Pic) :
    (toPicardFunctor f).app (.op T) L = (toPicardFunctor f).app (.op T) L' ↔
      ∃ N : T.left.Pic, Nonempty ((fromSkeleton _).obj L.val ≅ (fromSkeleton _).obj L'.val ⊗
        (Modules.pullback (Limits.pullback.snd f T.hom)).obj ((fromSkeleton _).obj N.val)) :=
  ⟨exists_iso_tensorObj_of_toPicardFunctor_app_eq f hf L L',
    fun ⟨N, ⟨e⟩⟩ ↦ toPicardFunctor_app_eq_of_iso f L L' N e⟩

end Exactness

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
    Function.Injective (Pic.map (Limits.pullback.snd f T.hom)) := by
  -- By the projection formula `f_{T,*} f_T^* 𝒩 ≅ f_{T,*} 𝒪_{X_T} ⊗ 𝒩 ≅ 𝒩`, so `𝒩` is recovered
  -- from its pullback.
  intro N N' h
  have := N.isInvertible
  have := N'.isInvertible
  have := Modules.IsInvertible.of_sheafOfModules ((fromSkeleton _).obj N.val)
  have := Modules.IsInvertible.of_sheafOfModules ((fromSkeleton _).obj N'.val)
  obtain ⟨e⟩ := toSkeleton_eq_toSkeleton_iff.1 (congrArg Pic.val h)
  obtain ⟨e₁⟩ := Modules.nonempty_pushforward_pullback_iso_self _
    (asIso (pushforwardUnitMap (Limits.pullback.snd f T.hom))).symm ((fromSkeleton _).obj N.val)
  obtain ⟨e₂⟩ := Modules.nonempty_pushforward_pullback_iso_self _
    (asIso (pushforwardUnitMap (Limits.pullback.snd f T.hom))).symm ((fromSkeleton _).obj N'.val)
  exact Pic.eq_iff_nonempty_iso.2 ⟨e₁.symm ≪≫ (Modules.pushforward _).mapIso e ≪≫ e₂⟩

/-- **The pullback map `Pic T → Pic (X_T)` is split by `σ_T^*`.**

(blueprint: `sk-prop-picard-pic-split`) -/
theorem pic_map_sectionBaseChange_snd (f : X ⟶ S) (σ : S ⟶ X) (hσ : σ ≫ f = 𝟙 S)
    (_hf : ∀ T : Over S, IsIso (pushforwardUnitMap (Limits.pullback.snd f T.hom)))
    (T : Over S) (N : T.left.Pic) :
    Pic.map (sectionBaseChange f σ hσ T) (Pic.map (Limits.pullback.snd f T.hom) N) = N := by
  rw [← Pic.map_comp, sectionBaseChange_snd, Pic.map_id]

/-- Every class of the Picard presheaf is Zariski-locally `σ`-normalized: the pullback `σ_T^* ℒ`
is trivial on the members `U` of a Zariski covering of `T`, which is an fppf covering, and there
`ℒ|_{X_U}` lies in `Pic_{X/S,σ}(U)`.  This gives the surjectivity in
`AlgebraicGeometry.bijective_toPicardFunctor_picardFunctorNormalized`.

(blueprint: `thm-pc-pic-split`) -/
instance isLocallySurjective_picardFunctorNormalized_ι (f : X ⟶ S) (σ : S ⟶ X)
    (hσ : σ ≫ f = 𝟙 S) :
    Presheaf.IsLocallySurjective (fppfTopology.over S) (picardFunctorNormalized f σ hσ).ι where
  imageSieve_mem {T} L := by
    choose U hU hUL using fun t : T.left ↦
      Pic.exists_map_ι_eq_mk_unit (Pic.map (sectionBaseChange f σ hσ T) L) t
    rw [GrothendieckTopology.mem_over_iff]
    refine fppfTopology.superset_covering ?_ (Precoverage.generate_mem_toGrothendieck
      (R := Presieve.ofArrows (fun t ↦ (U t).toScheme) (fun t ↦ (U t).ι)) ?_)
    · rw [Sieve.generate_le_iff]
      rintro _ _ ⟨t⟩
      rw [Sieve.overEquiv_iff]
      let i : Over.mk ((U t).ι ≫ T.hom) ⟶ T := Over.homMk (U t).ι
      refine ⟨⟨Pic.map (baseChangeMap f i) L, ?_⟩, rfl⟩
      exact (Pic.map_comp _ _ L).symm.trans
        ((congrArg (Pic.map · L) (sectionBaseChange_comp_baseChangeMap f σ hσ i)).trans
          ((Pic.map_comp _ _ L).trans (hUL t)))
    · rw [fppfPrecoverage, ofArrows_mem_precoverage_iff]
      exact ⟨fun t ↦ ⟨t, ⟨t, hU t⟩, rfl⟩, fun t ↦ ⟨inferInstance, inferInstance⟩⟩

/-- **The normalized classes map bijectively onto `Pic_{X/S}(T)`**, so that `Pic_{X/S}` is the
fppf sheafification of `Pic_{X/S,σ}`.

(blueprint: `sk-prop-picard-pic-split`) -/
theorem bijective_toPicardFunctor_picardFunctorNormalized (f : X ⟶ S) (σ : S ⟶ X)
    (hσ : σ ≫ f = 𝟙 S)
    (hf : ∀ T : Over S, IsIso (pushforwardUnitMap (Limits.pullback.snd f T.hom)))
    (T : Over S) :
    Function.Bijective (fun L : (picardFunctorNormalized f σ hσ).toFunctor.obj (.op T) ↦
      (toPicardFunctor f).app (.op T) L.1) := by
  -- `Pic_{X/S,σ} ⟶ Pic_{X/S}` is a morphism of fppf sheaves (`isSheaf_picardFunctorNormalized`)
  -- which is locally injective, as `Pic_{X/S,σ} ⊆ Pic_{X/S}` and `toPicardFunctor` is, and
  -- locally surjective, as both `Pic_{X/S,σ} ⊆ Pic_{X/S}` and `toPicardFunctor` are.
  let φ : (⟨_, isSheaf_picardFunctorNormalized f σ hσ hf⟩ :
      Sheaf (fppfTopology.over S) (Type (u + 1))) ⟶ picardFunctor f :=
    ⟨(picardFunctorNormalized f σ hσ).ι ≫ toPicardFunctor f⟩
  have : Presheaf.IsLocallyInjective (fppfTopology.over S) (picardFunctorNormalized f σ hσ).ι :=
    Presheaf.isLocallyInjective_of_injective _ _ fun _ ↦ Subtype.val_injective
  have : IsIso φ := (Sheaf.isLocallyBijective_iff_isIso φ).1
    ⟨Presheaf.isLocallyInjective_comp _ _ _, Presheaf.isLocallySurjective_comp _ _ _⟩
  have : IsIso φ.hom := inferInstanceAs (IsIso ((sheafToPresheaf _ _).map φ))
  have : IsIso (φ.hom.app (.op T)) := inferInstance
  exact (isIso_iff_bijective _).1 this

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
      (Pic.map (sectionBaseChange f σ hσ T) L, (toPicardFunctor f).app (.op T) L)) := by
  refine ⟨fun L L' h ↦ ?_, fun ⟨N, s⟩ ↦ ?_⟩
  · -- By exactness `ℒ ≅ ℒ' ⊗ f_T^* 𝒩`; applying `σ_T^*` gives `σ_T^* ℒ' ⊗ 𝒩 ≅ σ_T^* ℒ'`, so
    -- `𝒩` is trivial and `ℒ ≅ ℒ'`.
    obtain ⟨h₁, h₂⟩ := Prod.ext_iff.1 h
    obtain ⟨N, ⟨e⟩⟩ := exists_iso_tensorObj_of_toPicardFunctor_app_eq f hf L L' h₂
    obtain ⟨e₁⟩ := Pic.eq_iff_nonempty_iso.1
      (h₁ : Pic.map (sectionBaseChange f σ hσ T) L = Pic.map (sectionBaseChange f σ hσ T) L')
    have := L'.isInvertible
    have := Modules.IsInvertible.of_sheafOfModules ((fromSkeleton _).obj L'.val)
    obtain ⟨eN⟩ := Modules.nonempty_iso_unit_of_tensorObj_iso
      ((Modules.pullback (sectionBaseChange f σ hσ T)).obj ((fromSkeleton _).obj L'.val))
      ((fromSkeleton _).obj N.val)
      ((Iso.refl _ ⊗ᵢ pullbackSectionBaseChangeSndIso f σ hσ T _).symm ≪≫
        (Modules.nonempty_pullback_tensorObj_iso _ _ _).some.symm ≪≫
        (Modules.pullback _).mapIso e.symm ≪≫ (fromSkeletonToSkeletonIso _).symm ≪≫ e₁ ≪≫
        fromSkeletonToSkeletonIso _)
    exact Pic.eq_iff_nonempty_iso.2 ⟨e ≪≫ (Iso.refl _ ⊗ᵢ ((Modules.pullback _).mapIso eN ≪≫
      Modules.pullbackObjUnitIso _)) ≪≫ ρ_ _⟩
  · -- Write the class in `Pic_{X/S}(T)` as the image of a `σ`-normalized `ℒ₀`; then
    -- `ℒ₀ ⊗ f_T^* 𝒩` has the same image and `σ_T^* (ℒ₀ ⊗ f_T^* 𝒩) ≅ 𝒪_T ⊗ 𝒩 ≅ 𝒩`.
    obtain ⟨L₀, rfl⟩ := (bijective_toPicardFunctor_picardFunctorNormalized f σ hσ hf T).2 s
    have := L₀.1.isInvertible
    have := N.isInvertible
    have := Modules.IsInvertible.of_sheafOfModules ((fromSkeleton _).obj L₀.1.val)
    have := Modules.IsInvertible.of_sheafOfModules ((fromSkeleton _).obj N.val)
    let M := (fromSkeleton _).obj L₀.1.val ⊗
      (Modules.pullback (Limits.pullback.snd f T.hom)).obj ((fromSkeleton _).obj N.val)
    have := Modules.IsInvertible.sheafOfModules_isInvertible M
    obtain ⟨e₀⟩ := Pic.nonempty_iso_unit_of_map_eq _ L₀.2
    refine ⟨Pic.mk M, Prod.ext (Pic.eq_iff_nonempty_iso.2 ⟨fromSkeletonToSkeletonIso _ ≪≫
      (Modules.pullback _).mapIso (fromSkeletonToSkeletonIso M) ≪≫
      (Modules.nonempty_pullback_tensorObj_iso _ _ _).some ≪≫
      (e₀ ⊗ᵢ pullbackSectionBaseChangeSndIso f σ hσ T _) ≪≫ λ_ _⟩)
      (toPicardFunctor_app_eq_of_iso f _ _ N (fromSkeletonToSkeletonIso M))⟩

end Split

end AlgebraicGeometry
