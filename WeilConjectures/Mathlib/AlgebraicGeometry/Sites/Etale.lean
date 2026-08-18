/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
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
- `AlgebraicGeometry.Scheme.hasWeakSheafify_smallEtaleTopology`: sheafification for the
  localizations of the small étale site at all étale `U ⟶ X` gives sheafification for
  the small étale site itself, by localizing at the terminal object `𝟙 X`.
-/

@[expose] public section

universe v u u'

open CategoryTheory Limits

noncomputable section

namespace AlgebraicGeometry.Scheme

variable {X Y : Scheme.{u}}

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

section Sheafify

variable {A : Type u'} [Category.{v} A]
  [∀ U : X.Etale, HasWeakSheafify (X.smallEtaleTopology.over U) A]

/-- Sheafification for the localizations of the small étale site at all étale `U ⟶ X`
gives sheafification for the small étale site itself, by localizing at the terminal
object `𝟙 X`. -/
instance hasWeakSheafify_smallEtaleTopology : HasWeakSheafify X.smallEtaleTopology A :=
  X.smallEtaleTopology.hasWeakSheafify_of_over_isTerminal A terminalIsTerminal

end Sheafify

end Scheme

end AlgebraicGeometry
