/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Sites.Over
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Small
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Over

/-!
# Complements on the small étale site

- `AlgebraicGeometry.Scheme.Hom.Etale`: the base change functor `Y.Etale ⥤ X.Etale`
  along a morphism `f : X ⟶ Y`; it preserves finite limits, is representably flat
  (`AlgebraicGeometry.Scheme.Hom.representablyFlat_etale`), is continuous for the small
  étale topologies (`AlgebraicGeometry.Scheme.Hom.isContinuous_etale`), and it is
  compatible with the projections `V ×_Y X ⟶ V` by
  `AlgebraicGeometry.Scheme.Hom.etale_map_left_comp_fst`.
- `AlgebraicGeometry.Scheme.mem_smallEtaleTopology_iff`: a sieve on an object of the small
  étale site is a covering exactly when the arrows in it are jointly surjective. This is the
  sieve-level form of
  `AlgebraicGeometry.Scheme.ofArrows_mem_smallEtaleTopology_iff`.
- `AlgebraicGeometry.Scheme.Etale.baseChange` and
  `AlgebraicGeometry.Scheme.Etale.baseChangeHom`: for an étale morphism `g : W ⟶ X`, the
  base change `V ×_X W` of an étale `X`-scheme `V`, again as an étale `X`-scheme, and its
  projection to `V`.
- `AlgebraicGeometry.Scheme.Etale.ofArrows_baseChange_mem_smallEtaleTopology`: these base
  changes cover `V` as soon as the étale morphisms are jointly surjective.
- `AlgebraicGeometry.Scheme.Etale.isTerminalSectionsOfIsEmpty`: a sheaf on the small étale
  site has terminal sections over an object whose underlying scheme is empty. This is the
  sheaf condition for the empty covering.
- `AlgebraicGeometry.Scheme.hasWeakSheafify_smallEtaleTopology`: sheafification for the
  localizations of the small étale site at all étale `U ⟶ X` gives sheafification for
  the small étale site itself, by localizing at the terminal object `𝟙 X`.
- The classes of `AlgebraicGeometry.Scheme.etalePrecoverage` inherited from the precoverage
  of the class of étale morphisms: `hasIsos_etalePrecoverage`,
  `isStableUnderComposition_etalePrecoverage`, `isStableUnderBaseChange_etalePrecoverage`
  and `jointlySurjective_etalePrecoverage`.
- `AlgebraicGeometry.Scheme.Etale.overEquiv`: for an étale `X`-scheme `U`, the localization
  `Over U` of the small étale site of `X` at `U` is equivalent to the small étale site of
  the scheme `U.left`, an étale `X`-scheme over `U` being the same as an étale
  `U.left`-scheme. Both functors of the equivalence are cocontinuous
  (`Etale.overToEtale_isCocontinuous`, `Etale.etaleToOver_isCocontinuous`), so that
  `CategoryTheory.Equivalence.sheafCongr` gives the equivalence of the categories of
  sheaves (`AlgebraicGeometry.Scheme.Etale.overSheafEquiv`).
-/

@[expose] public section

universe v u u'

open CategoryTheory Limits Opposite

noncomputable section

namespace AlgebraicGeometry.Scheme

variable {A : Type u'} [Category.{v} A] {X Y : Scheme.{u}}

section Precoverage

/-- Isomorphisms are étale, so a family containing an isomorphism is an étale covering. -/
instance hasIsos_etalePrecoverage : etalePrecoverage.{u}.HasIsos :=
  inferInstanceAs (precoverage @AlgebraicGeometry.Etale).HasIsos

/-- Étale coverings are stable under composition, étale morphisms being so. -/
instance isStableUnderComposition_etalePrecoverage :
    etalePrecoverage.{u}.IsStableUnderComposition :=
  inferInstanceAs (precoverage @AlgebraicGeometry.Etale).IsStableUnderComposition

/-- Étale coverings are stable under base change, étale morphisms being so. -/
instance isStableUnderBaseChange_etalePrecoverage :
    etalePrecoverage.{u}.IsStableUnderBaseChange :=
  inferInstanceAs (precoverage @AlgebraicGeometry.Etale).IsStableUnderBaseChange

/-- The members of an étale covering are jointly surjective. -/
instance jointlySurjective_etalePrecoverage : JointlySurjective etalePrecoverage.{u} :=
  inferInstanceAs (JointlySurjective (precoverage @AlgebraicGeometry.Etale))

end Precoverage

section Functoriality

/-- The base change functor `Y.Etale ⥤ X.Etale` along a morphism `f : X ⟶ Y`, sending an
étale `V ⟶ Y` to the projection `V ×_Y X ⟶ X`. This is the functor along which the
pushforward `AlgebraicGeometry.Etale.lowerStar` and the pullback
`AlgebraicGeometry.Etale.upperStar` are defined. -/
def Hom.Etale (f : X ⟶ Y) : Y.Etale ⥤ X.Etale :=
  MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ f

instance (f : X ⟶ Y) : PreservesFiniteLimits f.Etale :=
  inferInstanceAs <| PreservesFiniteLimits (MorphismProperty.Over.pullback @Etale ⊤ f)

/-- The base change functor `f.Etale` is representably flat: the small étale site of `Y`
has finite limits and base change preserves them. -/
instance Hom.representablyFlat_etale (f : X ⟶ Y) : RepresentablyFlat f.Etale :=
  MorphismProperty.Over.representablyFlat_pullback @AlgebraicGeometry.Etale f

/-- The base change functor `f.Etale` preserves the covering sieves of the small étale
topologies: étale covers are stable under base change. -/
lemma Hom.coverPreserving_etale (f : X ⟶ Y) :
    CoverPreserving (smallEtaleTopology Y) (smallEtaleTopology X) f.Etale :=
  coverPreserving_overPullback @AlgebraicGeometry.Etale @AlgebraicGeometry.Etale le_rfl f

/-- The base change functor `f.Etale` is continuous for the small étale topologies: it
preserves covers by `AlgebraicGeometry.Scheme.Hom.coverPreserving_etale`, and compatible
families since it is representably flat. -/
instance Hom.isContinuous_etale (f : X ⟶ Y) :
    f.Etale.IsContinuous (smallEtaleTopology Y) (smallEtaleTopology X) :=
  isContinuous_overPullback @AlgebraicGeometry.Etale @AlgebraicGeometry.Etale le_rfl f

set_option backward.isDefEq.respectTransparency false in
/-- Base change along `f : X ⟶ Y` is compatible with the projections from the base changes
to the original étale `Y`-schemes:

```
   V ×_Y X ──(f.Etale.map g).left──→ U ×_Y X
      │                                 │
      │ pullback.fst V.hom f            │ pullback.fst U.hom f
      ↓                                 ↓
      V ────────────g.left────────────→  U
```
-/
lemma Hom.etale_map_left_comp_fst (f : X ⟶ Y) {U V : Y.Etale} (g : V ⟶ U) :
    (f.Etale.map g).left ≫ pullback.fst U.hom f = pullback.fst V.hom f ≫ g.left :=
  pullback.lift_fst _ _ _

/-- Base change along `f : X ⟶ Y` is compatible with the projections to `X`. -/
lemma Hom.etale_map_left_comp_snd (f : X ⟶ Y) {U V : Y.Etale} (g : V ⟶ U) :
    (f.Etale.map g).left ≫ pullback.snd U.hom f = pullback.snd V.hom f :=
  pullback.lift_snd _ _ _

end Functoriality

section Sieves

/-- A sieve on an object of the small étale site is a covering exactly when the arrows in it
are jointly surjective. This is the sieve-level form of
`AlgebraicGeometry.Scheme.ofArrows_mem_smallEtaleTopology_iff`, a sieve being generated by
the family of all its arrows. -/
lemma mem_smallEtaleTopology_iff {U : X.Etale} (S : Sieve U) :
    S ∈ X.smallEtaleTopology U ↔
      ∀ x : U.left, ∃ (V : X.Etale) (g : V ⟶ U), S g ∧ x ∈ Set.range g.left := by
  let ι := Σ V : X.Etale, { g : V ⟶ U // S g }
  have hS : Sieve.ofArrows (fun i : ι ↦ i.1) (fun i ↦ i.2.1) = S := by
    apply le_antisymm
    · rw [Sieve.ofArrows, Sieve.generate_le_iff]
      rintro V g ⟨i⟩
      exact i.2.2
    · intro V g hg
      exact ⟨V, 𝟙 V, g, Presieve.ofArrows.mk (⟨V, g, hg⟩ : ι), by simp⟩
  conv_lhs => rw [← hS, ofArrows_mem_smallEtaleTopology_iff]
  simp only [Set.eq_univ_iff_forall, Set.mem_iUnion]
  constructor
  · intro h x
    obtain ⟨i, hi⟩ := h x
    exact ⟨i.1, i.2.1, i.2.2, hi⟩
  · intro h x
    obtain ⟨V, g, hg, hx⟩ := h x
    exact ⟨⟨V, g, hg⟩, hx⟩

end Sieves

section BaseChange

variable {W : Scheme.{u}} (g : W ⟶ X) [AlgebraicGeometry.Etale g] (V : X.Etale)

set_option backward.isDefEq.respectTransparency false in
/-- The base change `V ×_X W` of an étale `X`-scheme `V` along an étale morphism
`g : W ⟶ X`, viewed again as an étale `X`-scheme rather than as an étale `W`-scheme; it is
the image of `g.Etale.obj V` under the localization functor along `g`.

```
   V ×_X W ────→ W
      │          │ g
      ↓          ↓
      V ──V.hom─→ X
```
-/
def Etale.baseChange : X.Etale :=
  Etale.mk (pullback.fst V.hom g ≫ V.hom)

set_option backward.isDefEq.respectTransparency false in
/-- The projection `V ×_X W ⟶ V`, a morphism of étale `X`-schemes. -/
def Etale.baseChangeHom : Etale.baseChange g V ⟶ V :=
  MorphismProperty.Over.homMk (pullback.fst V.hom g) rfl

set_option backward.isDefEq.respectTransparency false in
/-- The image of `V ×_X W` in `V` is the preimage of the range of `g`. -/
lemma Etale.range_baseChangeHom_left :
    Set.range (Etale.baseChangeHom g V).left.base = V.hom.base ⁻¹' Set.range g.base :=
  Pullback.range_fst V.hom g

end BaseChange

section Cover

variable (V : X.Etale) {ι : Type*} {W : ι → Scheme.{u}} (g : ∀ i, W i ⟶ X)
  [∀ i, AlgebraicGeometry.Etale (g i)]

set_option backward.isDefEq.respectTransparency false in
/-- For a jointly surjective family of étale morphisms `g i : W i ⟶ X`, the base changes
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

end Cover

section EmptyObject

/-- The empty sieve on an object of the small étale site whose underlying scheme is empty is
a covering: the empty family of morphisms is (vacuously) jointly surjective. -/
lemma Etale.bot_mem_smallEtaleTopology (T : X.Etale) [IsEmpty T.left] :
    (⊥ : Sieve T) ∈ X.smallEtaleTopology T := by
  have hbot : (⊥ : Sieve T) = Sieve.ofArrows (Empty.elim : Empty → X.Etale) (fun i ↦ i.elim) := by
    simp [Sieve.ofArrows, Presieve.ofArrows_of_isEmpty]
  rw [hbot, ofArrows_mem_smallEtaleTopology_iff]
  simp [Set.eq_univ_iff_forall, IsEmpty.forall_iff]

/-- A sheaf on the small étale site has terminal sections over an object whose underlying
scheme is empty. -/
def Etale.isTerminalSectionsOfIsEmpty
    (G : Sheaf X.smallEtaleTopology A) (T : X.Etale) [IsEmpty T.left] :
    IsTerminal (G.obj.obj (op T)) :=
  G.isTerminalOfBotCover T (Etale.bot_mem_smallEtaleTopology T)

end EmptyObject

section Sheafify

variable [∀ U : X.Etale, HasWeakSheafify (X.smallEtaleTopology.over U) A]

/-- Sheafification for the localizations of the small étale site at all étale `U ⟶ X`
gives sheafification for the small étale site itself, by localizing at the terminal
object `𝟙 X`. -/
instance hasWeakSheafify_smallEtaleTopology : HasWeakSheafify X.smallEtaleTopology A :=
  X.smallEtaleTopology.hasWeakSheafify_of_over_isTerminal A terminalIsTerminal

end Sheafify

section Localization

set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Etale

variable (U : X.Etale)

/-- An étale `X`-scheme over `U`, read as an étale `U.left`-scheme. -/
@[simps]
def overToEtale : Over U ⥤ U.left.Etale where
  obj t := Etale.mk t.hom.left
  map {t t'} φ := MorphismProperty.Over.homMk φ.left.left
    (congrArg (fun m ↦ m.left) (CategoryTheory.Over.w φ))
  map_id _ := MorphismProperty.Over.Hom.ext rfl
  map_comp _ _ := MorphismProperty.Over.Hom.ext rfl

/-- An étale `U.left`-scheme, read as an étale `X`-scheme over `U`. -/
@[simps]
def etaleToOver : U.left.Etale ⥤ Over U where
  obj V := Over.mk (X := U) (MorphismProperty.Over.homMk (A := Etale.mk (V.hom ≫ U.hom)) V.hom rfl)
  map {V V'} ψ := Over.homMk (MorphismProperty.Over.homMk (A := Etale.mk (V.hom ≫ U.hom))
    (B := Etale.mk (V'.hom ≫ U.hom)) ψ.left (by
      change ψ.left ≫ V'.hom ≫ U.hom = V.hom ≫ U.hom
      rw [← Category.assoc, MorphismProperty.Over.w]))
    (MorphismProperty.Over.Hom.ext (MorphismProperty.Over.w ψ))
  map_id _ := CategoryTheory.Over.OverMorphism.ext (MorphismProperty.Over.Hom.ext rfl)
  map_comp _ _ := CategoryTheory.Over.OverMorphism.ext (MorphismProperty.Over.Hom.ext rfl)

/-- **The small étale site of `X` localized at `U` is the small étale site of `U.left`.** -/
@[simps functor inverse]
def overEquiv : Over U ≌ U.left.Etale where
  functor := overToEtale U
  inverse := etaleToOver U
  unitIso := NatIso.ofComponents
    (fun t ↦ CategoryTheory.Over.isoMk
      (MorphismProperty.Over.isoMk (Iso.refl _) (by
        change 𝟙 _ ≫ t.hom.left ≫ U.hom = t.left.hom
        rw [Category.id_comp, MorphismProperty.Over.w]))
      (MorphismProperty.Over.Hom.ext (Category.id_comp _)))
    (fun _ ↦ CategoryTheory.Over.OverMorphism.ext (MorphismProperty.Over.Hom.ext
      ((Category.comp_id _).trans (Category.id_comp _).symm)))
  counitIso := NatIso.ofComponents
    (fun V ↦ MorphismProperty.Over.isoMk (Iso.refl _) (Category.id_comp _))
    (fun _ ↦ MorphismProperty.Over.Hom.ext ((Category.comp_id _).trans (Category.id_comp _).symm))
  functor_unitIso_comp _ := MorphismProperty.Over.Hom.ext (Category.comp_id _)

/-- The composite `U.left.Etale ⥤ Over U ⥤ X.Etale` is the localization functor
`V ↦ (V ⟶ U.left ⟶ X)`. -/
def etaleToOverCompForgetIso :
    etaleToOver U ⋙ CategoryTheory.Over.forget U ≅ MorphismProperty.Over.map ⊤ U.prop :=
  NatIso.ofComponents (fun _ ↦ MorphismProperty.Over.isoMk (Iso.refl _) (Category.id_comp _))
    (fun _ ↦ MorphismProperty.Over.Hom.ext ((Category.comp_id _).trans (Category.id_comp _).symm))

section Topology

open Scheme in
/-- `overToEtale` is cocontinuous: it lifts the jointly surjective families. -/
instance overToEtale_isCocontinuous :
    (overToEtale U).IsCocontinuous (X.smallEtaleTopology.over U) U.left.smallEtaleTopology where
  cover_lift {t S} hS := by
    rw [GrothendieckTopology.mem_over_iff, mem_smallEtaleTopology_iff]
    rw [mem_smallEtaleTopology_iff] at hS
    intro x
    obtain ⟨V, g, hg, hx⟩ := hS x
    let W : X.Etale := Etale.mk (V.hom ≫ U.hom)
    let h : W ⟶ t.left := MorphismProperty.Over.homMk g.left (by
      change g.left ≫ t.left.hom = V.hom ≫ U.hom
      rw [← MorphismProperty.Over.w t.hom, ← Category.assoc]
      congr 1
      exact MorphismProperty.Over.w g)
    refine ⟨W, h, ?_, hx⟩
    rw [Sieve.overEquiv_iff]
    change S ((overToEtale U).map
      (CategoryTheory.Over.homMk (U := CategoryTheory.Over.mk (h ≫ t.hom)) h))
    have : (overToEtale U).map
        (CategoryTheory.Over.homMk (U := CategoryTheory.Over.mk (h ≫ t.hom)) h : _ ⟶ t) =
        (MorphismProperty.Over.isoMk (Iso.refl _) (by
          change 𝟙 _ ≫ V.hom = (h ≫ t.hom).left
          rw [Category.id_comp]
          exact (MorphismProperty.Over.w g).symm) :
          (overToEtale U).obj (CategoryTheory.Over.mk (h ≫ t.hom)) ≅ V).hom ≫ g :=
      MorphismProperty.Over.Hom.ext (Category.id_comp _).symm
    rw [this]
    exact S.downward_closed hg _

open Scheme in
/-- `etaleToOver` is cocontinuous: it lifts the jointly surjective families. -/
instance etaleToOver_isCocontinuous :
    (etaleToOver U).IsCocontinuous U.left.smallEtaleTopology (X.smallEtaleTopology.over U) where
  cover_lift {V S} hS := by
    rw [GrothendieckTopology.mem_over_iff, mem_smallEtaleTopology_iff] at hS
    rw [mem_smallEtaleTopology_iff]
    intro x
    obtain ⟨W, h, hh, hx⟩ := hS (x : ((etaleToOver U).obj V).left.left)
    let V' : U.left.Etale := Etale.mk (h.left ≫ (V.hom : V.left ⟶ U.left))
    let g : V' ⟶ V := MorphismProperty.Over.homMk h.left rfl
    refine ⟨V', g, ?_, hx⟩
    rw [Sieve.overEquiv_iff] at hh
    change S ((etaleToOver U).map g)
    have : (etaleToOver U).map g =
        (CategoryTheory.Over.isoMk (MorphismProperty.Over.isoMk (Iso.refl W.left) (by
          change 𝟙 W.left ≫ W.hom = (h.left ≫ V.hom) ≫ U.hom
          rw [Category.id_comp, Category.assoc]
          exact (MorphismProperty.Over.w h).symm))
          (MorphismProperty.Over.Hom.ext (Category.id_comp _)) :
          (etaleToOver U).obj V' ≅ CategoryTheory.Over.mk (h ≫ ((etaleToOver U).obj V).hom)).hom ≫
          CategoryTheory.Over.homMk
            (U := CategoryTheory.Over.mk (h ≫ ((etaleToOver U).obj V).hom)) h :=
      CategoryTheory.Over.OverMorphism.ext (MorphismProperty.Over.Hom.ext (Category.id_comp _).symm)
    rw [this]
    exact S.downward_closed hh _

instance overEquiv_functor_isCocontinuous :
    (overEquiv U).functor.IsCocontinuous (X.smallEtaleTopology.over U) U.left.smallEtaleTopology :=
  overToEtale_isCocontinuous U

instance overEquiv_inverse_isCocontinuous :
    (overEquiv U).inverse.IsCocontinuous U.left.smallEtaleTopology (X.smallEtaleTopology.over U) :=
  etaleToOver_isCocontinuous U

instance overEquiv_inverse_isDenseSubsite :
    (overEquiv U).inverse.IsDenseSubsite U.left.smallEtaleTopology (X.smallEtaleTopology.over U) :=
  (overEquiv U).isDenseSubsite_inverse_of_isCocontinuous _ _

instance overEquiv_functor_isDenseSubsite :
    (overEquiv U).functor.IsDenseSubsite (X.smallEtaleTopology.over U) U.left.smallEtaleTopology :=
  (overEquiv U).isDenseSubsite_functor_of_isCocontinuous _ _

instance etaleToOver_isDenseSubsite :
    (etaleToOver U).IsDenseSubsite U.left.smallEtaleTopology (X.smallEtaleTopology.over U) :=
  overEquiv_inverse_isDenseSubsite U

instance overToEtale_isDenseSubsite :
    (overToEtale U).IsDenseSubsite (X.smallEtaleTopology.over U) U.left.smallEtaleTopology :=
  overEquiv_functor_isDenseSubsite U

variable (A : Type u') [Category.{u + 1} A]

/-- **Sheaves on the localized small étale site of `X` at `U` are sheaves on the small étale
site of `U.left`**, the sheaf on `U.left.Etale` corresponding to `G` being `V ↦ G(V ⟶ U)`. -/
def overSheafEquiv :
    Sheaf (X.smallEtaleTopology.over U) A ≌ Sheaf U.left.smallEtaleTopology A :=
  (overEquiv U).sheafCongr (X.smallEtaleTopology.over U) U.left.smallEtaleTopology A

/-- The sections of the sheaf on `U.left.Etale` corresponding to `G` over `V` are the sections
of `G` over `V ⟶ U`. -/
lemma overSheafEquiv_functor_obj_val (G : Sheaf (X.smallEtaleTopology.over U) A) :
    ((overSheafEquiv U A).functor.obj G).obj = (etaleToOver U).op ⋙ G.obj :=
  rfl

end Topology
end Etale

end Localization

end Scheme

end AlgebraicGeometry
