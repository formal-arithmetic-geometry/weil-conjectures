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
public import WeilConjectures.AlgebraicGeometry.Picard.NormalizedDescent
public import WeilConjectures.AlgebraicGeometry.Picard.TwistedDescent
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

The group law on `AlgebraicGeometry.Scheme.Pic` is only defined downstream, in
`WeilConjectures/AlgebraicGeometry/Picard/Group.lean`, so the exactness of
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
- `AlgebraicGeometry.picardFunctorNormalized_eq_of_iso_tensorObj`: two `σ`-normalized classes
  which differ by a module pulled back from the base are equal.
- `AlgebraicGeometry.isSheaf_picardFunctorNormalized`: the `σ`-normalized relative Picard
  functor is an fppf sheaf (blueprint `sk-cor-picard-pic-sheaf`), hence a Zariski sheaf
  (`AlgebraicGeometry.isSheaf_zariski_picardFunctorNormalized`).
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

/-- If the canonical map `𝒪_B ⟶ g_* 𝒪_Z` is an isomorphism, then
`g^♯ : Γ(B, 𝒪_B) ⟶ Γ(Z, 𝒪_Z)` is surjective. On global sections the map is `b ↦ g^♯ b * m` with
`m` the image of `1`; it hits `1`, so `m` is a unit, and it hits `m²`, so `m` is in the image of
`g^♯`. -/
lemma surjective_appTop_of_isIso_pushforwardUnitMap {Z B : Scheme.{u}} (g : Z ⟶ B)
    [IsIso (pushforwardUnitMap g)] : Function.Surjective g.appTop := by
  let φ : Modules.unit B ⟶ (Modules.pushforward g).obj (Modules.unit Z) :=
    pushforwardUnitMap g
  have : IsIso φ := inferInstanceAs (IsIso (pushforwardUnitMap g))
  have hbij : Function.Bijective (Modules.Hom.app φ ⊤) := ConcreteCategory.bijective_of_isIso _
  set m : Γ(Z, ⊤) := Modules.Hom.app φ ⊤ (1 : Γ(B, ⊤))
  have hφ (b : Γ(B, ⊤)) : Modules.Hom.app φ ⊤ b = g.appTop b * m :=
    (congrArg _ (mul_one b).symm).trans (Modules.Hom.app_smul φ b (1 : Γ(B, ⊤)))
  obtain ⟨b₀, hb₀⟩ : ∃ b₀ : Γ(B, ⊤), Modules.Hom.app φ ⊤ b₀ = (1 : Γ(Z, ⊤)) := hbij.2 _
  obtain ⟨b₂, hb₂⟩ : ∃ b₂ : Γ(B, ⊤), Modules.Hom.app φ ⊤ b₂ = m * m := hbij.2 _
  have h₀ : g.appTop b₀ * m = 1 := (hφ b₀).symm.trans hb₀
  have h₂ : g.appTop b₂ * m = m * m := (hφ b₂).symm.trans hb₂
  have hm : m = g.appTop b₂ := by
    calc m = m * (g.appTop b₀ * m) := by rw [h₀, mul_one]
      _ = (m * m) * g.appTop b₀ := by ring
      _ = (g.appTop b₂ * m) * g.appTop b₀ := by rw [h₂]
      _ = g.appTop b₂ * (g.appTop b₀ * m) := by ring
      _ = g.appTop b₂ := by rw [h₀, mul_one]
  intro c
  obtain ⟨b, hb⟩ : ∃ b : Γ(B, ⊤), Modules.Hom.app φ ⊤ b = c := hbij.2 _
  exact ⟨b * b₂, by rw [map_mul, ← hm, ← hφ, hb]⟩

/-- If the canonical map `𝒪_B ⟶ g_* 𝒪_Z` is an isomorphism, then
`g^♯ : Γ(B, 𝒪_B) ⟶ Γ(Z, 𝒪_Z)` is bijective: on global sections the map is `b ↦ g^♯ b * m` for
the image `m` of `1`, and it is bijective. -/
lemma bijective_appTop_of_isIso_pushforwardUnitMap {Z B : Scheme.{u}} (g : Z ⟶ B)
    [IsIso (pushforwardUnitMap g)] : Function.Bijective g.appTop := by
  refine ⟨fun b b' h ↦ ?_, surjective_appTop_of_isIso_pushforwardUnitMap g⟩
  let φ : Modules.unit B ⟶ (Modules.pushforward g).obj (Modules.unit Z) :=
    pushforwardUnitMap g
  have : IsIso φ := inferInstanceAs (IsIso (pushforwardUnitMap g))
  have hbij : Function.Bijective (Modules.Hom.app φ ⊤) := ConcreteCategory.bijective_of_isIso _
  set m : Γ(Z, ⊤) := Modules.Hom.app φ ⊤ (1 : Γ(B, ⊤))
  have hφ (b : Γ(B, ⊤)) : Modules.Hom.app φ ⊤ b = g.appTop b * m :=
    (congrArg _ (mul_one b).symm).trans (Modules.Hom.app_smul φ b (1 : Γ(B, ⊤)))
  exact hbij.1 (by rw [hφ, hφ b', h])

/-- The relative Picard functor `Pic_{X/S}` of a morphism of schemes `f : X ⟶ S`: the fppf
sheafification of the Picard presheaf `T ↦ Pic (X_T)`, so that on the level of sections
`Pic_{X/S}(T)` is the fppf-sheafified version of `Pic (X_T) / pr_T^* Pic T`.

The fppf topology on the category `Over S` of schemes over `S` is the localization
`Scheme.fppfTopology.over S` of the fppf topology on all schemes.

(blueprint: `sk-def-picard-pic`, `def-pc-picard-functor`) -/
noncomputable def picardFunctor (f : X ⟶ S) :
    Sheaf (Scheme.fppfTopology.over S) (Type (u + 1)) :=
  (presheafToSheaf (Scheme.fppfTopology.over S) (Type (u + 1))).obj (picardPresheaf f)

/-- The canonical map from the Picard presheaf of `f : X ⟶ S` to the relative Picard functor,
i.e. the unit of the fppf sheafification adjunction. -/
noncomputable abbrev toPicardFunctor (f : X ⟶ S) : picardPresheaf f ⟶ (picardFunctor f).obj :=
  toSheafify (Scheme.fppfTopology.over S) (picardPresheaf f)

section BaseChange

variable {X' S' : Scheme.{u}} {f : X ⟶ S} {g : S' ⟶ S} {f' : X' ⟶ S'} {g' : X' ⟶ X}

/-- For a cartesian square exhibiting `f' : X' ⟶ S'` as the base change of `f : X ⟶ S` along
`g : S' ⟶ S` and a scheme `T` over `S'`, the fibre products `X' ×_{S'} T` and `X ×_S T` agree. -/
noncomputable def pullbackIsoOfIsPullback (h : IsPullback g' f' f g) (T : Over S') :
    Limits.pullback f' T.hom ≅ Limits.pullback f (T.hom ≫ g) :=
  ((IsPullback.of_hasPullback f' T.hom).paste_horiz h).isoPullback

@[reassoc (attr := simp)]
lemma pullbackIsoOfIsPullback_hom_fst (h : IsPullback g' f' f g) (T : Over S') :
    (pullbackIsoOfIsPullback h T).hom ≫ Limits.pullback.fst f (T.hom ≫ g) =
      Limits.pullback.fst f' T.hom ≫ g' :=
  IsPullback.isoPullback_hom_fst _

@[reassoc (attr := simp)]
lemma pullbackIsoOfIsPullback_hom_snd (h : IsPullback g' f' f g) (T : Over S') :
    (pullbackIsoOfIsPullback h T).hom ≫ Limits.pullback.snd f (T.hom ≫ g) =
      Limits.pullback.snd f' T.hom :=
  IsPullback.isoPullback_hom_snd _

@[reassoc]
lemma pullbackIsoOfIsPullback_hom_comp_baseChangeMap (h : IsPullback g' f' f g)
    {T T' : Over S'} (φ : T' ⟶ T) :
    (pullbackIsoOfIsPullback h T').hom ≫ baseChangeMap f ((Over.map g).map φ) =
      baseChangeMap f' φ ≫ (pullbackIsoOfIsPullback h T).hom := by
  apply Limits.pullback.hom_ext <;>
    simp [baseChangeMap]

/-- **The Picard presheaf is compatible with base change.** For a cartesian square exhibiting
`f' : X' ⟶ S'` as the base change of `f : X ⟶ S` along `g : S' ⟶ S`, the restriction of the
Picard presheaf of `f` to schemes over `S'` is the Picard presheaf of `f'`, through the
identifications `X' ×_{S'} T ≅ X ×_S T` (`AlgebraicGeometry.pullbackIsoOfIsPullback`). -/
noncomputable def picardPresheafIsoOfIsPullback (h : IsPullback g' f' f g) :
    (Over.map g).op ⋙ picardPresheaf f ≅ picardPresheaf f' :=
  NatIso.ofComponents (fun T ↦ Equiv.toIso
    { toFun := Pic.map (pullbackIsoOfIsPullback h T.unop).hom
      invFun := Pic.map (pullbackIsoOfIsPullback h T.unop).inv
      left_inv L := by rw [← Pic.map_comp, Iso.inv_hom_id, Pic.map_id]
      right_inv L := by rw [← Pic.map_comp, Iso.hom_inv_id, Pic.map_id] })
    fun {T T'} φ ↦ by
      ext L
      exact (Pic.map_comp _ _ L).symm.trans ((congrArg (fun m ↦ Pic.map m L)
        (pullbackIsoOfIsPullback_hom_comp_baseChangeMap h φ.unop)).trans (Pic.map_comp _ _ L))

@[simp]
lemma picardPresheafIsoOfIsPullback_hom_app (h : IsPullback g' f' f g) (T : (Over S')ᵒᵖ)
    (L : (picardPresheaf f).obj ((Over.map g).op.obj T)) :
    (picardPresheafIsoOfIsPullback h).hom.app T L =
      Pic.map (pullbackIsoOfIsPullback h T.unop).hom L :=
  rfl

/-- Restricting the fppf sheafification of a presheaf `P` on schemes over `S` to schemes over
`S'`, along `g : S' ⟶ S`, gives the fppf sheafification of the restriction of `P`: the functor
`Over.map g` is continuous and cocontinuous for the fppf topologies. -/
noncomputable def overMapOpCompSheafifyIso (g : S' ⟶ S) (P : (Over S)ᵒᵖ ⥤ Type (u + 1)) :
    (Over.map g).op ⋙ ((presheafToSheaf (Scheme.fppfTopology.over S) _).obj P).obj ≅
      ((presheafToSheaf (Scheme.fppfTopology.over S') _).obj ((Over.map g).op ⋙ P)).obj :=
  (sheafToPresheaf _ _).mapIso
    (((Over.map g).pushforwardContinuousSheafificationCompatibility (Type (u + 1))
      (Scheme.fppfTopology.over S') (Scheme.fppfTopology.over S)).app P).symm

end BaseChange

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
  ⟨overMapOpCompSheafifyIso g (picardPresheaf f) ≪≫
    (sheafToPresheaf _ _).mapIso ((presheafToSheaf _ _).mapIso (picardPresheafIsoOfIsPullback h))⟩

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

(blueprint: `sk-def-picard-pic`, `def-pc-pic-sigma-functor`) -/
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

/-- **The Picard group of a field is trivial.** Every invertible module on `Spec k` is isomorphic
to the structure sheaf: it is trivial on an open neighbourhood of the unique point, which is all
of `Spec k`.

(blueprint: `lem-pc-pic-of-field`) -/
instance subsingleton_spec (k : Type u) [Field k] : Subsingleton (Spec (.of k)).Pic := by
  refine ⟨fun L L' ↦ Pic.eq_iff_nonempty_iso.2 ?_⟩
  have := L.isInvertible
  have := L'.isInvertible
  have := Modules.IsInvertible.of_sheafOfModules ((fromSkeleton (Spec (.of k)).Modules).obj L.val)
  have := Modules.IsInvertible.of_sheafOfModules
    ((fromSkeleton (Spec (.of k)).Modules).obj L'.val)
  obtain ⟨e⟩ := Modules.IsInvertible.nonempty_iso_unit default
    ((fromSkeleton (Spec (.of k)).Modules).obj L.val)
  obtain ⟨e'⟩ := Modules.IsInvertible.nonempty_iso_unit default
    ((fromSkeleton (Spec (.of k)).Modules).obj L'.val)
  exact ⟨e ≪≫ e'.symm⟩

end Scheme.Pic

end Pic

/-- **`Pic_{X/S,σ}` is a subfunctor of the Picard presheaf.** For a morphism `i : V ⟶ U` of
`S`-schemes, pulling back a class of `Pic (X_U)` that is trivial along `σ_U` gives a class of
`Pic (X_V)` that is trivial along `σ_V`, since `σ_U ∘ i = (X ×_S i) ∘ σ_V`.

(blueprint: `lem-pc-sigma-subfunctor`, `rem-ptr-pc-pic-sigma-functor-8`) -/
theorem picardPresheaf_map_mem_picardFunctorNormalized (f : X ⟶ S) (σ : S ⟶ X)
    (hσ : σ ≫ f = 𝟙 S) {U V : (Over S)ᵒᵖ} (i : U ⟶ V) {L : (picardPresheaf f).obj U}
    (hL : L ∈ (picardFunctorNormalized f σ hσ).obj U) :
    (picardPresheaf f).map i L ∈ (picardFunctorNormalized f σ hσ).obj V :=
  (picardFunctorNormalized f σ hσ).map i hL

/-- **The `k`-points of `Pic_{X/k,σ}`.** Let `X` be a scheme over a field `k` with a rational
point `σ`. Then `Pic_{X/k,σ}(k) = Pic (X)`: every class of `Pic (X_k)` is trivial along
`σ_k : Spec k ⟶ X_k`, the Picard group of `Spec k` being trivial, and `X_k = X ×_k k ≅ X`.

(blueprint: `lem-pc-sigma-k-points`) -/
theorem nonempty_picardFunctorNormalized_obj_equiv_pic {k : Type u} [Field k]
    (f : X ⟶ Spec (.of k)) (σ : Spec (.of k) ⟶ X) (hσ : σ ≫ f = 𝟙 _) :
    Nonempty ((picardFunctorNormalized f σ hσ).obj (Opposite.op (Over.mk (𝟙 _))) ≃ X.Pic) := by
  let e : Limits.pullback f (Over.mk (𝟙 (Spec (.of k)))).hom ≅ X :=
    asIso (Limits.pullback.fst f (𝟙 _))
  have hmem (L : (picardPresheaf f).obj (Opposite.op (Over.mk (𝟙 _)))) :
      L ∈ (picardFunctorNormalized f σ hσ).obj (Opposite.op (Over.mk (𝟙 _))) :=
    Subsingleton.elim (α := (Spec (.of k)).Pic) _ _
  refine ⟨(Equiv.subtypeUnivEquiv hmem).trans
    { toFun := Pic.map e.inv
      invFun := Pic.map e.hom
      left_inv := fun L ↦ ?_
      right_inv := fun L ↦ ?_ }⟩
  · change Pic.map e.hom (Pic.map e.inv L) = L
    rw [← Pic.map_comp, e.hom_inv_id, Pic.map_id]
  · change Pic.map e.inv (Pic.map e.hom L) = L
    rw [← Pic.map_comp, e.inv_hom_id, Pic.map_id]

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
      (Modules.pullback (Limits.pullback.snd f T.hom)).obj ((fromSkeleton _).obj N.val)) := by
  have hbij (Y : Over S) : Function.Bijective (pullback.snd f Y.hom).appTop :=
    have := hf Y
    bijective_appTop_of_isIso_pushforwardUnitMap _
  -- The classes `ℒ` and `ℒ'` agree on the members of an fppf covering `{T i ⟶ T}`.
  have hR := Presheaf.equalizerSieve_mem (fppfTopology.over S) (toPicardFunctor f) L L' h
  have : fppfPrecoverage.HasIsos := ⟨fun {_ _} f _ ↦ by
    rw [← Presieve.ofArrows_pUnit.{0}, fppfPrecoverage, ofArrows_mem_precoverage_iff]
    exact ⟨fun x ↦ ⟨⟨⟩, (inv f) x, by rw [← Scheme.Hom.comp_apply, IsIso.inv_hom_id]; rfl⟩,
      fun _ ↦ ⟨inferInstance, inferInstance⟩⟩⟩
  rw [GrothendieckTopology.mem_over_iff,
    Precoverage.mem_toGrothendieck_iff_of_isStableUnderComposition] at hR
  obtain ⟨R, hR, hle⟩ := hR
  obtain ⟨ι, Z, a, rfl⟩ := R.exists_eq_ofArrows
  let T' (i : ι) : Over S := Over.mk (a i ≫ T.hom)
  let g (i : ι) : T' i ⟶ T := Over.homMk (a i)
  have heq (i : ι) : Pic.map (baseChangeMap f (g i)) L = Pic.map (baseChangeMap f (g i)) L' :=
    (Sieve.overEquiv_iff _ _).1 (hle _ _ (Presieve.ofArrows.mk i))
  -- The families `T i ⟶ T` and `X_{T i} ⟶ X_T` are fpqc coverings.
  have hR' : Presieve.ofArrows (fun i ↦ (T' i).left) (fun i ↦ (g i).left) ∈
      fppfPrecoverage T.left := hR
  have hgT : Sieve.ofArrows (fun i ↦ (T' i).left) (fun i ↦ (g i).left) ∈
      fpqcTopology T.left :=
    Precoverage.generate_mem_toGrothendieck (fppfPrecoverage_le_fpqcPrecoverage _ hR')
  have hgX : Sieve.ofArrows _ (fun i ↦ baseChangeMap f (g i)) ∈
      fpqcTopology (pullback f T.hom) :=
    Precoverage.generate_mem_toGrothendieck (fppfPrecoverage_le_fpqcPrecoverage _
      (Precoverage.mem_coverings_of_isPullback (fun i ↦ (g i).left) hR' (pullback.snd f T.hom)
        (fun i ↦ baseChangeMap f (g i)) (fun i ↦ pullback.snd f (T' i).hom)
        (fun i ↦ isPullback_baseChangeMap f (g i))))
  -- `𝒦 = ℒ ⊗ ℒ'^∨` is trivial on the `X_{T i}`.
  let A := (fromSkeleton _).obj L.val
  let B := (fromSkeleton _).obj L'.val
  have := L.isInvertible
  have := L'.isInvertible
  have := Modules.IsInvertible.of_sheafOfModules A
  have := Modules.IsInvertible.of_sheafOfModules B
  obtain ⟨eB⟩ := Modules.nonempty_tensorObj_dual_iso_unit B
  let K := A ⊗ Modules.dual B
  let P : (pullback f T.hom).Modules :=
    (Modules.pullback (pullback.snd f T.hom)).obj (𝟙_ T.left.Modules)
  have eK (i : ι) : Nonempty ((Modules.pullback (baseChangeMap f (g i))).obj K ≅
      (Modules.pullback (baseChangeMap f (g i))).obj P) := by
    obtain ⟨eAB⟩ := Pic.eq_iff_nonempty_iso.1 (heq i)
    exact ⟨(Modules.nonempty_pullback_tensorObj_iso _ _ _).some ≪≫
      (((fromSkeletonToSkeletonIso _).symm ≪≫ eAB ≪≫ fromSkeletonToSkeletonIso _) ⊗ᵢ
        Iso.refl _) ≪≫ (Modules.nonempty_pullback_tensorObj_iso _ _ _).some.symm ≪≫
      (Modules.pullback _).mapIso eB ≪≫ Modules.pullbackObjUnitIso _ ≪≫
      (Modules.pullbackObjUnitIso _).symm ≪≫
      (Modules.pullback _).mapIso (Modules.pullbackObjUnitIso _).symm⟩
  -- Hence the descent datum of `𝒦` is a twist of that of `f_T^* 𝒪_T` by a cocycle `c`.
  have hD₂ (i : ι) : Modules.IsInvertible (X := pullback f (T' i).hom)
      (((modulesPseudofunctor.toDescentData fun i ↦ baseChangeMap f (g i)).obj P).obj i) :=
    inferInstanceAs ((Modules.pullback (baseChangeMap f (g i))).obj P).IsInvertible
  obtain ⟨cX, ⟨eKD⟩⟩ := DescentCocycle.exists_iso_twist
    (D₁ := (modulesPseudofunctor.toDescentData fun i ↦ baseChangeMap f (g i)).obj K)
    (D₂ := (modulesPseudofunctor.toDescentData fun i ↦ baseChangeMap f (g i)).obj P) eK
  -- The cocycle comes from `T`; the twisted descent datum of `𝒪_T` is effective.
  let cT := cX.ofBaseChange hbij
  let DT := cT.twist ((modulesPseudofunctor.toDescentData fun i ↦ (g i).left).obj
    (𝟙_ T.left.Modules))
  obtain ⟨N, -, ⟨eN⟩⟩ := exists_isQuasicoherent_toDescentData_iso _ hgT DT fun i ↦
    inferInstanceAs ((Modules.pullback (g i).left).obj (𝟙_ T.left.Modules)).IsQuasicoherent
  have : SheafOfModules.IsInvertible.{u, u, u} (N : T.left.Modules) :=
    isInvertible_of_toDescentData_iso _ hgT DT N ⟨eN⟩ fun i ↦
      Modules.IsInvertible.sheafOfModules_isInvertible
        ((Modules.pullback (g i).left).obj (𝟙_ T.left.Modules))
  let N' : T.left.Modules := N
  have := Modules.IsInvertible.of_sheafOfModules N'
  -- The descent data of `f_T^* 𝒩` and of `𝒦` agree, hence `f_T^* 𝒩 ≅ 𝒦`.
  have w (i : ι) : pullback.snd f (T' i).hom ≫ (g (id i)).left =
      baseChangeMap f (g i) ≫ pullback.snd f T.hom :=
    (baseChangeMap_snd f (g i)).symm
  let E :=
    ((Pseudofunctor.DescentData.toDescentDataCompPullFunctorIso modulesPseudofunctor w).app
      N).symm ≪≫
    (Pseudofunctor.DescentData.pullFunctor modulesPseudofunctor w).mapIso eN ≪≫
    eqToIso (cT.pullFunctor_obj_twist w _) ≪≫
    (cT.pull w).twistFunctor.mapIso
      ((Pseudofunctor.DescentData.toDescentDataCompPullFunctorIso modulesPseudofunctor w).app _) ≪≫
    eqToIso (congrArg (fun c ↦ DescentCocycle.twist c _) (cX.pull_ofBaseChange hbij)) ≪≫
    eKD.symm
  obtain ⟨eNK⟩ := nonempty_iso_of_toDescentData_iso _ hgX
    (inferInstanceAs ((Modules.pullback (pullback.snd f T.hom)).obj N').IsQuasicoherent)
    (inferInstanceAs K.IsQuasicoherent) E
  refine ⟨Pic.mk N', ⟨?_⟩⟩
  exact (ρ_ A).symm ≪≫ whiskerLeftIso A (eB.symm ≪≫ β_ B _) ≪≫ (α_ A _ B).symm ≪≫
    β_ K B ≪≫ whiskerLeftIso B (eNK.symm ≪≫
      (Modules.pullback _).mapIso (fromSkeletonToSkeletonIso N').symm)

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

/-- **Normalized classes differing by a class from the base are equal.** If two `σ`-normalized
classes `ℒ, ℒ' ∈ Pic_{X/S,σ}(T)` are of the form `ℒ ≅ P ⊗ f_T^* 𝒩` and `ℒ' ≅ P ⊗ f_T^* 𝒩'`
for the same module `P` on `X_T`, then `ℒ = ℒ'`: pulling back along `σ_T` gives
`𝒪_T ≅ σ_T^* P ⊗ 𝒩` and `𝒪_T ≅ σ_T^* P ⊗ 𝒩'`, hence `𝒩 ≅ 𝒩'` and `ℒ ≅ ℒ'`.

This is the injectivity of `Pic_{X/S,σ}(T) → Pic (X_T) / Pic T` behind the splitting
`AlgebraicGeometry.bijective_pic_split`, in a form that needs no hypothesis on `f`. -/
theorem picardFunctorNormalized_eq_of_iso_tensorObj (f : X ⟶ S) (σ : S ⟶ X)
    (hσ : σ ≫ f = 𝟙 S) {T : Over S}
    (L L' : (picardFunctorNormalized f σ hσ).toFunctor.obj (.op T))
    (P : (Limits.pullback f T.hom).Modules) (N N' : T.left.Modules)
    (e : (fromSkeleton _).obj L.1.val ≅
      P ⊗ (Modules.pullback (Limits.pullback.snd f T.hom)).obj N)
    (e' : (fromSkeleton _).obj L'.1.val ≅
      P ⊗ (Modules.pullback (Limits.pullback.snd f T.hom)).obj N') :
    L = L' := by
  have key (M : (picardFunctorNormalized f σ hσ).toFunctor.obj (.op T)) (Q : T.left.Modules)
      (eM : (fromSkeleton _).obj M.1.val ≅
        P ⊗ (Modules.pullback (Limits.pullback.snd f T.hom)).obj Q) :
      Nonempty (𝟙_ T.left.Modules ≅
        (Modules.pullback (sectionBaseChange f σ hσ T)).obj P ⊗ Q) := by
    obtain ⟨n⟩ := Pic.nonempty_iso_unit_of_map_eq _ M.2
    obtain ⟨t⟩ := Modules.nonempty_pullback_tensorObj_iso (sectionBaseChange f σ hσ T) P
      ((Modules.pullback (Limits.pullback.snd f T.hom)).obj Q)
    exact ⟨n.symm ≪≫ (Modules.pullback _).mapIso eM ≪≫ t ≪≫
      whiskerLeftIso _ (pullbackSectionBaseChangeSndIso f σ hσ T Q)⟩
  obtain ⟨n⟩ := key L N e
  obtain ⟨n'⟩ := key L' N' e'
  -- `𝒪_T ≅ A ⊗ 𝒩` and `𝒪_T ≅ A ⊗ 𝒩'` give `𝒩 ≅ 𝒩'`.
  let i : N ≅ N' := (λ_ N).symm ≪≫ whiskerRightIso n' N ≪≫ whiskerRightIso (β_ _ N') N ≪≫
    α_ N' _ N ≪≫ whiskerLeftIso N' n.symm ≪≫ ρ_ N'
  exact Subtype.ext (Pic.eq_iff_nonempty_iso.2
    ⟨e ≪≫ whiskerLeftIso P ((Modules.pullback _).mapIso i) ≪≫ e'.symm⟩)

/-- **The `σ`-normalized Picard functor is an fppf sheaf.** The relative Picard functor
`Pic_{X/S}` is an fppf sheaf, hence a Zariski sheaf, simply because it is defined as an fppf
sheafification: this is `(AlgebraicGeometry.picardFunctor f).cond`, so only the second half of
the corollary carries content. Namely, if `f` has a section `σ` and the canonical map
`𝒪_T ⟶ f_{T,*} 𝒪_{X_T}` is an isomorphism for every `T` in `(Sch/S)_fppf`, then
`Pic_{X/S,σ}(T) = ker σ_T^*` is an fppf sheaf as well.

Let `ℒ i ∈ Pic_{X/S,σ}(T i)` be compatible on an fppf covering `{T i ⟶ T}`. Isomorphisms
`ℒ i ≅ ℒ j` over `X_{T i ×_T T j}` can be rescaled by a unit so as to be compatible with the
trivialisations of `σ^* ℒ i` (`AlgebraicGeometry.exists_isSectionNormalized`), and such normalized
isomorphisms are unique because `Γ(T', 𝒪) ⟶ Γ(X_{T'}, 𝒪)` is surjective
(`AlgebraicGeometry.IsSectionNormalized.eq`); hence they satisfy the cocycle condition and form a
descent datum (`AlgebraicGeometry.normalizedDescentData`). By fpqc descent it comes from an
invertible module `M` on `X_T`, and twisting `M` by the pullback of an inverse of `σ_T^* M` makes
it normalized without changing its restrictions. Uniqueness of the gluing follows from the exactness
of `Pic T → Pic (X_T) → Pic_{X/S}(T)` (`AlgebraicGeometry.toPicardFunctor_app_eq_iff`).

(blueprint: `sk-cor-picard-pic-sheaf`, `lem-pc-k-sheaf`) -/
theorem isSheaf_picardFunctorNormalized (f : X ⟶ S) (σ : S ⟶ X) (hσ : σ ≫ f = 𝟙 S)
    (hf : ∀ T : Over S, IsIso (pushforwardUnitMap (Limits.pullback.snd f T.hom))) :
    Presheaf.IsSheaf (Scheme.fppfTopology.over S)
      (picardFunctorNormalized f σ hσ).toFunctor := by
  have hsurj (Y : Over S) : Function.Surjective (pullback.snd f Y.hom).appTop :=
    have := hf Y
    surjective_appTop_of_isIso_pushforwardUnitMap _
  rw [isSheaf_iff_isSheaf_of_type, over_toGrothendieck_eq_toGrothendieck_comap_forget,
    ← Precoverage.toGrothendieck_toCoverage, Presieve.isSheaf_coverage]
  intro T R hR
  obtain ⟨ι, T', g, rfl⟩ := R.exists_eq_ofArrows
  have hR' : Presieve.ofArrows (fun i ↦ (T' i).left) (fun i ↦ (g i).left) ∈
      fppfPrecoverage T.left := by
    simpa [Precoverage.mem_comap_iff, Presieve.map_ofArrows] using hR
  rw [Presieve.isSheafFor_arrows_iff]
  intro x hx
  refine existsUnique_of_exists_of_unique ?_ ?_
  · -- The modules `ℒ i` and the trivialisations of their pullbacks along the sections.
    let L (i : ι) : (pullback f (T' i).hom).Modules := (fromSkeleton _).obj (x i).1.val
    have hL (i : ι) : (L i).IsInvertible :=
      have := (x i).1.isInvertible
      Modules.IsInvertible.of_sheafOfModules (L i)
    let α (i : ι) : (Modules.pullback (sectionBaseChange f σ hσ (T' i))).obj (L i) ≅
        (Modules.pullback (g i).left).obj (SheafOfModules.unit T.left.ringCatSheaf) :=
      (Pic.nonempty_iso_unit_of_map_eq _ (x i).2).some ≪≫ (Modules.pullbackObjUnitIso _).symm
    -- The isomorphisms on the double overlaps.
    have hxij (i j : ι) : Pic.map (chosenPullbackBaseChangeMap f (g i) (g j)).p₁ (x i).1 =
        Pic.map (chosenPullbackBaseChangeMap f (g i) (g j)).p₂ (x j).1 :=
      congrArg Subtype.val (hx i j _ (pullback.fst _ _) (pullback.snd _ _) pullback.condition)
    let e (i j : ι) : (Modules.pullback (chosenPullbackBaseChangeMap f (g i) (g j)).p₁).obj (L i) ≅
        (Modules.pullback (chosenPullbackBaseChangeMap f (g i) (g j)).p₂).obj (L j) :=
      (fromSkeletonToSkeletonIso _).symm ≪≫ (Pic.eq_iff_nonempty_iso.1 (hxij i j)).some ≪≫
        fromSkeletonToSkeletonIso _
    let D := normalizedDescentData (sectionBaseChange_snd f σ hσ)
      (sectionBaseChange_comp_baseChangeMap f σ hσ) hsurj (L := L) α e
    -- The family `X_{T i} ⟶ X_T` is an fpqc covering.
    have hg : Sieve.ofArrows _ (fun i ↦ baseChangeMap f (g i)) ∈
        fpqcTopology (pullback f T.hom) :=
      Precoverage.generate_mem_toGrothendieck (fppfPrecoverage_le_fpqcPrecoverage _
        (Precoverage.mem_coverings_of_isPullback (fun i ↦ (g i).left) hR' (pullback.snd f T.hom)
          (fun i ↦ baseChangeMap f (g i)) (fun i ↦ pullback.snd f (T' i).hom)
          (fun i ↦ isPullback_baseChangeMap f (g i))))
    obtain ⟨M, -, ⟨eM⟩⟩ := exists_isQuasicoherent_toDescentData_iso _ hg D.descentData
      (fun i ↦ inferInstanceAs (L i).IsQuasicoherent)
    have : SheafOfModules.IsInvertible.{u, u, u} (M : (pullback f T.hom).Modules) :=
      isInvertible_of_toDescentData_iso _ hg D.descentData M ⟨eM⟩
        (fun i ↦ Modules.IsInvertible.sheafOfModules_isInvertible (L i))
    let M' : (pullback f T.hom).Modules := M
    have hM : M'.IsInvertible := Modules.IsInvertible.of_sheafOfModules _
    -- `M` restricts to `ℒ i` on `X_{T i}`.
    let eMi (i : ι) : (Modules.pullback (baseChangeMap f (g i))).obj M' ≅ L i :=
      { hom := eM.hom.hom i
        inv := eM.inv.hom i
        hom_inv_id := by
          rw [← Pseudofunctor.DescentData.comp_hom, eM.hom_inv_id,
            Pseudofunctor.DescentData.id_hom]
          rfl
        inv_hom_id := by
          rw [← Pseudofunctor.DescentData.comp_hom, eM.inv_hom_id,
            Pseudofunctor.DescentData.id_hom]
          rfl }
    -- Twist `M` by the pullback of an inverse `N'` of `σ_T^* M`.
    let Mσ := (Modules.pullback (sectionBaseChange f σ hσ T)).obj M'
    obtain ⟨eN'⟩ := Modules.nonempty_tensorObj_dual_iso_unit Mσ
    let M₁ := M' ⊗ (Modules.pullback (pullback.snd f T.hom)).obj (Modules.dual Mσ)
    have : SheafOfModules.IsInvertible.{u, u, u} M₁ :=
      Modules.IsInvertible.sheafOfModules_isInvertible M₁
    refine ⟨⟨Pic.mk M₁, Pic.eq_iff_nonempty_iso.2 ⟨fromSkeletonToSkeletonIso _ ≪≫
      (Modules.pullback _).mapIso (fromSkeletonToSkeletonIso M₁) ≪≫
      (Modules.nonempty_pullback_tensorObj_iso _ _ _).some ≪≫
      (Iso.refl Mσ ⊗ᵢ pullbackSectionBaseChangeSndIso f σ hσ T _) ≪≫ eN' ≪≫
      (fromSkeletonToSkeletonIso _).symm⟩⟩, fun i ↦ Subtype.ext ?_⟩
    -- On `T i`, the pullback of `σ_T^* M` is `σ_{T i}^* ℒ i`, which is trivial; hence so is the
    -- pullback of its inverse.
    let A : (Modules.pullback (g i).left).obj Mσ ≅ SheafOfModules.unit _ :=
      (Modules.pullbackComp _ _).app M' ≪≫
        (Modules.pullbackCongr (sectionBaseChange_comp_baseChangeMap f σ hσ (g i)).symm).app M' ≪≫
        ((Modules.pullbackComp _ _).app M').symm ≪≫ (Modules.pullback _).mapIso (eMi i) ≪≫
        (Pic.nonempty_iso_unit_of_map_eq _ (x i).2).some
    let E : (Modules.pullback (g i).left).obj (Modules.dual Mσ) ≅ SheafOfModules.unit _ :=
      (λ_ _).symm ≪≫ (A.symm ⊗ᵢ Iso.refl _) ≪≫
        (Modules.nonempty_pullback_tensorObj_iso _ _ _).some.symm ≪≫
        (Modules.pullback _).mapIso eN' ≪≫ Modules.pullbackObjUnitIso _
    exact Pic.eq_iff_nonempty_iso.2 ⟨fromSkeletonToSkeletonIso _ ≪≫
      (Modules.pullback _).mapIso (fromSkeletonToSkeletonIso M₁) ≪≫
      (Modules.nonempty_pullback_tensorObj_iso _ _ _).some ≪≫
      (eMi i ⊗ᵢ ((Modules.pullbackComp _ _).app _ ≪≫
        (Modules.pullbackCongr (Limits.pullback.lift_snd _ _ _)).app _ ≪≫
        ((Modules.pullbackComp _ _).app _).symm ≪≫ (Modules.pullback _).mapIso E ≪≫
        Modules.pullbackObjUnitIso _)) ≪≫ ρ_ _⟩
  · intro t t' ht ht'
    have hJ : Sieve.ofArrows T' g ∈ fppfTopology.over S T := by
      rw [over_toGrothendieck_eq_toGrothendieck_comap_forget]
      exact Precoverage.generate_mem_toGrothendieck hR
    have himg : (toPicardFunctor f).app (.op T) t.1 = (toPicardFunctor f).app (.op T) t'.1 := by
      refine (((isSheaf_iff_isSheaf_of_type _ _).1 (picardFunctor f).property).isSeparated _
        hJ).ext ?_
      rintro _ _ ⟨W, a, _, ⟨i⟩, rfl⟩
      rw [op_comp, Functor.map_comp_apply, Functor.map_comp_apply,
        ← NatTrans.naturality_apply (toPicardFunctor f) (g i).op t.1,
        ← NatTrans.naturality_apply (toPicardFunctor f) (g i).op t'.1]
      exact congrArg (fun y ↦ (picardFunctor f).obj.map a.op ((toPicardFunctor f).app _ y))
        (congrArg Subtype.val ((ht i).trans (ht' i).symm))
    obtain ⟨N, ⟨e⟩⟩ := exists_iso_tensorObj_of_toPicardFunctor_app_eq f hf t.1 t'.1 himg
    exact picardFunctorNormalized_eq_of_iso_tensorObj f σ hσ t t' _ ((fromSkeleton _).obj N.val)
      (SheafOfModules.unit _) e
      ((ρ_ _).symm ≪≫ whiskerLeftIso _ (Modules.pullbackObjUnitIso _).symm)

/-- **The `σ`-normalized Picard functor is a Zariski sheaf.** Under the hypotheses of
`AlgebraicGeometry.isSheaf_picardFunctorNormalized` it is an fppf sheaf, and every Zariski
covering is an fppf covering.

This is condition (1) in the proof of blueprint `thm-pc-picard-representable`. -/
theorem isSheaf_zariski_picardFunctorNormalized (f : X ⟶ S) (σ : S ⟶ X) (hσ : σ ≫ f = 𝟙 S)
    (hf : ∀ T : Over S, IsIso (pushforwardUnitMap (Limits.pullback.snd f T.hom))) :
    Presheaf.IsSheaf (Scheme.zariskiTopology.over S)
      (picardFunctorNormalized f σ hσ).toFunctor :=
  (isSheaf_picardFunctorNormalized f σ hσ hf).of_le fun T R hR ↦ by
    rw [GrothendieckTopology.mem_over_iff] at hR ⊢
    exact Precoverage.toGrothendieck_mono zariskiPrecoverage_le_fppfPrecoverage _ hR

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
