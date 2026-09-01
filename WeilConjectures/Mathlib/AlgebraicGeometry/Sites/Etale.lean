/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Small
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Over

/-!
# Complements on the small étale site

- `AlgebraicGeometry.Scheme.Hom.Etale`: the base change functor `Y.Etale ⥤ X.Etale`
  along a morphism `f : X ⟶ Y`; it preserves finite limits, is representably flat
  (`AlgebraicGeometry.Scheme.Hom.representablyFlat_etale`) and is continuous for the small
  étale topologies (`AlgebraicGeometry.Scheme.Hom.isContinuous_etale`).
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

end Functoriality

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

end Scheme

end AlgebraicGeometry
