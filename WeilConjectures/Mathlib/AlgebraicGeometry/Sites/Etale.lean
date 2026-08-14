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
