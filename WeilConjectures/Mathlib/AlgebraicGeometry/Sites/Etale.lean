/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Etale
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Over

/-!
# Complements on the small étale site

- `AlgebraicGeometry.Scheme.Hom.Etale`: the base change functor `Y.Etale ⥤ X.Etale`
  along a morphism `f : X ⟶ Y`; it preserves finite limits.
- `AlgebraicGeometry.Scheme.Etale.baseChange` and
  `AlgebraicGeometry.Scheme.Etale.baseChangeHom`: for an open immersion `j : U ⟶ X`, the
  base change `V ×_X U` of an étale `X`-scheme `V`, again as an étale `X`-scheme, and its
  projection to `V`.
- `AlgebraicGeometry.Scheme.Etale.ofArrows_baseChange_mem_smallEtaleTopology`: these base
  changes cover `V` as soon as the open immersions are jointly surjective.
- `AlgebraicGeometry.Scheme.Etale.liftOfRangeSubset` and
  `AlgebraicGeometry.Scheme.Etale.isoMapLiftOfRangeSubset`: an étale `X`-scheme whose image
  lies in the range of an open immersion `j : U ⟶ X` is the image of an étale `U`-scheme
  under the localization functor along `j`.
- `AlgebraicGeometry.Scheme.Etale.isTerminalSectionsOfIsEmpty`: a sheaf on the small étale
  site has terminal sections over an object whose underlying scheme is empty. This is the
  sheaf condition for the empty covering.
- `AlgebraicGeometry.Scheme.Etale.part`: the part `V ×_X Z` of an étale `X`-scheme `V` lying
  over an open `Z ⊆ X`, again as an étale `X`-scheme.
- `AlgebraicGeometry.Scheme.Etale.ofArrows_clopenι_mem_smallEtaleTopology`: for a
  decomposition `X = Z ⊔ W` into two opens, the two parts of `V` lying over `Z` and over `W`
  cover `V`.
- `AlgebraicGeometry.Scheme.hasWeakSheafify_smallEtaleTopology`: sheafification for the
  localizations of the small étale site at all étale `U ⟶ X` gives sheafification for
  the small étale site itself, by localizing at the terminal object `𝟙 X`.

## Implementation notes

`AlgebraicGeometry.Scheme.Etale.str` is a spelling of the structure morphism of an étale
`X`-scheme whose codomain is literally `X`. The field `V.hom` has codomain
`(Functor.fromPUnit X).obj V.right`, which is definitionally but not syntactically `X`; every
`rw` along an open of `X` fails against the latter, so the abbreviation is not cosmetic.

The decomposition of `V` along `X = Z ⊔ W` is indexed by `Bool` rather than by a two-element
inductive type, so that it can be fed to the `Sieve.ofArrows` API, which takes a family of
arrows indexed by an arbitrary type.
-/

@[expose] public section

universe v u u'

open CategoryTheory Limits Opposite

noncomputable section

namespace AlgebraicGeometry.Scheme

variable {A : Type u'} [Category.{v} A] {X Y : Scheme.{u}}

section Functoriality

/-- The base change functor `Y.Etale ⥤ X.Etale` along a morphism `f : X ⟶ Y`, sending an
étale `V ⟶ Y` to the projection `V ×_Y X ⟶ X`. This is the functor along which the
pushforward `AlgebraicGeometry.Etale.lowerStar` and the pullback
`AlgebraicGeometry.Etale.upperStar` are defined. -/
def Hom.Etale (f : X ⟶ Y) : Y.Etale ⥤ X.Etale :=
  MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ f

instance (f : X ⟶ Y) : PreservesFiniteLimits f.Etale :=
  inferInstanceAs <| PreservesFiniteLimits (MorphismProperty.Over.pullback @Etale ⊤ f)

end Functoriality

section BaseChangeCover

variable {U : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] (V : X.Etale)

set_option backward.isDefEq.respectTransparency false in
/-- The base change `V ×_X U` of an étale `X`-scheme `V` along an open immersion
`j : U ⟶ X`, viewed again as an étale `X`-scheme rather than as an étale `U`-scheme; it is
the image of `j.Etale.obj V` under the localization functor along `j`. -/
def Etale.baseChange : X.Etale :=
  Etale.mk (pullback.fst V.hom j ≫ V.hom)

set_option backward.isDefEq.respectTransparency false in
/-- The projection `V ×_X U ⟶ V`, an open immersion of étale `X`-schemes. -/
def Etale.baseChangeHom : Etale.baseChange j V ⟶ V :=
  MorphismProperty.Over.homMk (pullback.fst V.hom j) rfl

set_option backward.isDefEq.respectTransparency false in
/-- The image of `V ×_X U` in `V` is the preimage of the range of `j`. -/
lemma Etale.range_baseChangeHom_left :
    Set.range (Etale.baseChangeHom j V).left.base = V.hom.base ⁻¹' Set.range j.base :=
  IsOpenImmersion.range_pullbackFst j V.hom

variable {ι : Type*} {W : ι → Scheme.{u}} (g : ∀ i, W i ⟶ X) [∀ i, IsOpenImmersion (g i)]

set_option backward.isDefEq.respectTransparency false in
/-- For a jointly surjective family of open immersions `g i : W i ⟶ X`, the base changes
`V ×_X W i` cover `V` in the small étale topology, for every étale `X`-scheme `V`. -/
lemma Etale.ofArrows_baseChange_mem_smallEtaleTopology
    (hg : ⋃ i, Set.range (g i).base = Set.univ) :
    Sieve.ofArrows (fun i => Etale.baseChange (g i) V)
        (fun i => Etale.baseChangeHom (g i) V) ∈ X.smallEtaleTopology V := by
  rw [ofArrows_mem_smallEtaleTopology_iff]
  have hrange : ∀ i, Set.range (Etale.baseChangeHom (g i) V).left.base =
      V.hom.base ⁻¹' Set.range (g i).base := fun i => Etale.range_baseChangeHom_left _ _
  simp only [hrange]
  rw [← Set.preimage_iUnion, hg, Set.preimage_univ]

end BaseChangeCover

section Lift

variable {U : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] (V : X.Etale)
  (hV : Set.range V.hom.base ⊆ Set.range j.base)

/-- An étale `X`-scheme `V` whose structure morphism has image in the range of an open
immersion `j : U ⟶ X` lifts through `j`, by the universal property of open immersions; the
lift is étale because `j` is.

```
         V.left
        ╱    │
  lift ╱     │ V.hom
      ↙      ↓
     U ────→ X
         j
```
-/
def Etale.liftOfRangeSubset : U.Etale :=
  have h : AlgebraicGeometry.Etale (IsOpenImmersion.lift j V.hom hV ≫ j) := by
    rw [IsOpenImmersion.lift_fac]
    infer_instance
  have : AlgebraicGeometry.Etale (IsOpenImmersion.lift j V.hom hV) :=
    AlgebraicGeometry.Etale.of_comp _ j
  Etale.mk (IsOpenImmersion.lift j V.hom hV)

/-- The lift of `Etale.liftOfRangeSubset` identifies `V` with the image of an étale
`U`-scheme under the localization functor along `j`: the comparison morphism is the identity
on underlying schemes.

```
              ≅
   V ────────────────→ (Over.map j).obj (Etale.liftOfRangeSubset j V hV)
    ╲                 ╱
     ╲ V.hom         ╱ lift ≫ j
      ↘             ↙
              X
```
-/
def Etale.isoMapLiftOfRangeSubset :
    V ≅ (MorphismProperty.Over.map ⊤
      (inferInstance : @AlgebraicGeometry.Etale _ _ j)).obj (Etale.liftOfRangeSubset j V hV) where
  hom := MorphismProperty.Over.homMk (𝟙 V.left)
    ((Category.id_comp _).trans (IsOpenImmersion.lift_fac j V.hom hV))
  inv := MorphismProperty.Over.homMk (𝟙 V.left)
    ((Category.id_comp _).trans (IsOpenImmersion.lift_fac j V.hom hV).symm)
  hom_inv_id := by
    apply MorphismProperty.Over.Hom.ext
    exact Category.id_comp _
  inv_hom_id := by
    apply MorphismProperty.Over.Hom.ext
    exact Category.id_comp _

end Lift

section EmptyObject

/-- The empty sieve on an object of the small étale site whose underlying scheme is empty is
a covering: the empty family of morphisms is (vacuously) jointly surjective. -/
lemma Etale.bot_mem_smallEtaleTopology (T : X.Etale) [IsEmpty T.left] :
    (⊥ : Sieve T) ∈ X.smallEtaleTopology T := by
  have h := Scheme.ofArrows_mem_smallEtaleTopology_iff
    (W := T) (Z := (Empty.elim : Empty → X.Etale)) (fun i ↦ i.elim)
  have hu : ⋃ (i : Empty), Set.range ((fun i : Empty ↦ i.elim : ∀ i, Empty.elim i ⟶ T) i).left =
      (Set.univ : Set T.left) := by
    simp [Set.eq_univ_iff_forall, IsEmpty.forall_iff]
  have hbot : Sieve.ofArrows (Empty.elim : Empty → X.Etale) (fun i ↦ i.elim) = (⊥ : Sieve T) := by
    ext W f
    simp only [Sieve.ofArrows, Sieve.generate_apply, Sieve.bot_apply, iff_false]
    rintro ⟨W', g, -, ⟨i⟩, -⟩
    exact i.elim
  exact hbot ▸ h.mpr hu

/-- A sheaf on the small étale site has terminal sections over an object whose underlying
scheme is empty. -/
def Etale.isTerminalSectionsOfIsEmpty
    (G : Sheaf X.smallEtaleTopology A) (T : X.Etale) [IsEmpty T.left] :
    IsTerminal (G.obj.obj (op T)) := by
  refine IsTerminal.ofUnique (h := fun E ↦ ?_)
  have h := G.property E (⊥ : Sieve T) (Etale.bot_mem_smallEtaleTopology T)
    (fun _ _ hf ↦ hf.elim) (by rintro _ _ _ _ _ _ _ h₁ - -; exact h₁.elim)
  exact ⟨⟨h.choose⟩, fun a ↦ h.choose_spec.2 a (by rintro _ _ hf; exact hf.elim)⟩

end EmptyObject

section Part

/-- The structure morphism of an étale `X`-scheme, with codomain spelled as `X`. This is
definitionally `V.hom`, whose codomain is `(Functor.fromPUnit X).obj V.right`; the difference
is invisible to `exact` but fatal to `rw` along opens of `X`. -/
abbrev Etale.str (V : X.Etale) : V.left ⟶ X := V.hom

/-- A morphism of étale `X`-schemes does not enlarge the image of the structure morphism. -/
lemma Etale.range_hom_base_subset {T V : X.Etale} (a : T ⟶ V) :
    Set.range T.hom.base ⊆ Set.range V.hom.base := by
  rintro _ ⟨t, rfl⟩
  exact ⟨a.left.base t, congrArg (fun g : T.left ⟶ X ↦ g.base t) (MorphismProperty.Over.w a)⟩

/-- The part of an étale `X`-scheme `V` lying over an open `Z ⊆ X`, that is, the open
subscheme `V ×_X Z` of `V`, again as an étale `X`-scheme. -/
def Etale.part (V : X.Etale) (Z : X.Opens) : X.Etale :=
  MorphismProperty.Over.mk ⊤ ((V.str ⁻¹ᵁ Z).ι ≫ V.hom)
    (MorphismProperty.comp_mem _ _ _ inferInstance V.prop)

@[simp] lemma Etale.part_left (V : X.Etale) (Z : X.Opens) :
    (V.part Z).left = ((V.str ⁻¹ᵁ Z : V.left.Opens) : Scheme.{u}) := rfl

@[simp] lemma Etale.part_hom (V : X.Etale) (Z : X.Opens) :
    (V.part Z).hom = (V.str ⁻¹ᵁ Z).ι ≫ V.hom := rfl

/-- The inclusion of the part of `V` lying over `Z` into `V`. -/
def Etale.partι (V : X.Etale) (Z : X.Opens) : V.part Z ⟶ V :=
  MorphismProperty.Over.homMk (V.str ⁻¹ᵁ Z).ι rfl

@[simp] lemma Etale.partι_left (V : X.Etale) (Z : X.Opens) :
    (V.partι Z).left = (V.str ⁻¹ᵁ Z).ι := rfl

lemma Etale.range_partι (V : X.Etale) (Z : X.Opens) :
    Set.range (V.partι Z).left = ((V.str ⁻¹ᵁ Z : V.left.Opens) : Set V.left) :=
  Scheme.Opens.range_ι (V.str ⁻¹ᵁ Z)

/-- The part of `V` lying over `Z` maps into `Z`: a point of `V ×_X Z` is by construction a
point of `V` whose image lies in `Z`. -/
lemma Etale.range_part_hom_base_subset (V : X.Etale) (Z : X.Opens) :
    Set.range (V.part Z).hom.base ⊆ (Z : Set X) := by
  rintro _ ⟨x, rfl⟩
  exact x.2

end Part

section ClopenCover

variable (Z W : X.Opens) (V : X.Etale)

/-- The two pieces into which a decomposition `X = Z ⊔ W` into opens cuts an étale
`X`-scheme `V`. The index `false` is the piece over `Z`, the index `true` the piece
over `W`. -/
def Etale.clopenObj (b : Bool) : X.Etale := V.part (bif b then W else Z)

/-- The inclusion of the `b`-th piece of the decomposition of `V` into `V`. -/
def Etale.clopenι (b : Bool) : Etale.clopenObj Z W V b ⟶ V := V.partι _

lemma Etale.range_clopenι (b : Bool) :
    Set.range (Etale.clopenι Z W V b).left =
      ((V.str ⁻¹ᵁ (bif b then W else Z) : V.left.Opens) : Set V.left) :=
  Etale.range_partι V _

variable {Z W}

/-- If `Z` and `W` cover `X`, the two pieces of the decomposition cover `V`. -/
lemma Etale.ofArrows_clopenι_mem_smallEtaleTopology (hu : Z ⊔ W = ⊤) :
    Sieve.ofArrows _ (Etale.clopenι Z W V) ∈ X.smallEtaleTopology V := by
  refine (Scheme.ofArrows_mem_smallEtaleTopology_iff _).mpr ?_
  have hV : (V.str ⁻¹ᵁ Z) ⊔ (V.str ⁻¹ᵁ W) = ⊤ := by
    rw [← Scheme.Hom.preimage_sup, hu, Scheme.Hom.preimage_top]
  ext v
  simp only [Etale.range_clopenι, Set.mem_iUnion, Set.mem_univ, iff_true]
  have hv : v ∈ (⊤ : V.left.Opens) := trivial
  rw [← hV] at hv
  rcases hv with h | h
  · exact ⟨false, h⟩
  · exact ⟨true, h⟩

end ClopenCover

section Sheafify

variable [∀ U : X.Etale, HasWeakSheafify (X.smallEtaleTopology.over U) A]

/-- Sheafification for the localizations of the small étale site at all étale `U ⟶ X`
gives sheafification for the small étale site itself, by localizing at the terminal
object `𝟙 X`. -/
instance hasWeakSheafify_smallEtaleTopology : HasWeakSheafify X.smallEtaleTopology A :=
  X.smallEtaleTopology.hasWeakSheafify_of_over_isTerminal A terminalIsTerminal

end Sheafify

end Scheme

end AlgebraicGeometry
