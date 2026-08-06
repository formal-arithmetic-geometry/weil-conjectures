/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib
public import WeilConjectures.Compactification.Defs
public import WeilConjectures.SixFunctors.UpperLowerStar.Defs
public import WeilConjectures.SixFunctors.LowerShriek.OpenImmersion.Defs

/-!

# Lower shriek along a morphism admitting a compactification

For a morphism `f : X ⟶ Y` together with a compactification `X ⟶[i] Z ⟶[g] Y` (`i` an
open immersion, `g` proper), the lower shriek is the composition `f_! := i_! ⋙ g_*` of the
extension by zero along `i` with the pushforward `GrothendieckTopology.lowerStar` along
`g`.

## Main definitions

- `GrothendieckTopology.isContinuous_overPullback_of_le`: for `g` satisfying `P` and
  `Q ≤ P`, the base change functor is continuous for the small `Q`-topologies.
- `AlgebraicGeometry.Compactification.lowerShriek`: the lower shriek `i_! ⋙ g_*`
  associated with a compactification `X ⟶[i] Z ⟶[g] Y` of `f`.
- `AlgebraicGeometry.lowerShriek`: the lower shriek `f_!` of a morphism `f` satisfying
  `HasCompactification f`, *definitionally* equal to the composition associated with the
  chosen compactification `HasCompactification.compactification f`, see `lowerShriek_eq`.

## Implementation notes

- The pushforward `g_*` of `WeilConjectures.SixFunctors.UpperLowerStar.Defs` is defined along
  the base change functor, which exists for an *arbitrary* morphism `g` — in contrast to
  the localization functor `MorphismProperty.Over.map ⊤ h` of
  `WeilConjectures.SixFunctors.LowerShriek.OpenImmersion.Defs`, which requires `P g`. This
  is essential for compactifications, whose structure morphism is proper and in general
  does not satisfy `P`.
- The continuity of the base change functor for the small `Q`-topologies is assumed as an
  instance hypothesis throughout. For `g` satisfying `P` it is provided by
  `GrothendieckTopology.isContinuous_overPullback_of_le`, via the adjunction with the
  cocontinuous localization functor. For a general `g` (in particular the proper structure
  morphism of a compactification) the instance remains to be provided; this is the main
  outstanding input for the étale application.
- The sheafification and continuity hypotheses for the scheme-level
  `AlgebraicGeometry.lowerShriek` are quantified over all schemes `Z` since the middle
  object of the chosen compactification is choice-dependent; the Kan extension hypothesis
  is stated directly at the open immersion of the chosen compactification, so that it can
  be discharged by an instance for open immersions (as for the small étale sites). The
  hypothesis `@IsOpenImmersion ≤ P` provides `P` for the open immersion of the chosen
  compactification.

-/

@[expose] public section

universe v' u' u

open CategoryTheory Category Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme

namespace CategoryTheory

variable (A : Type u') [Category.{v'} A]

namespace GrothendieckTopology

variable (P Q : MorphismProperty Scheme.{u})
variable [P.IsStableUnderBaseChange]

variable {W U : Scheme.{u}} (g : W ⟶ U)

section SiteInstances

variable [Q.IsStableUnderBaseChange] [Q.IsMultiplicative] [Q.RespectsIso]
variable [P.IsStableUnderComposition] [P.HasOfPostcompProperty P]

variable {P Q g}

/-- For `g` satisfying `P` and `Q ≤ P`, the base change functor is continuous for the
small `Q`-topologies, by adjunction with the cocontinuous localization functor. -/
lemma isContinuous_overPullback_of_le (hg : P g) (hQP : Q ≤ P) :
    (MorphismProperty.Over.pullback P ⊤ g).IsContinuous
      (U.smallGrothendieckTopology Q (Q := P)) (W.smallGrothendieckTopology Q (Q := P)) :=
  haveI := isCocontinuous_overMap_of_le hg hQP
  (MorphismProperty.Over.mapPullbackAdj P ⊤ g hg _root_.trivial).isContinuous_of_isCocontinuous
    _ _

end SiteInstances

end GrothendieckTopology

end CategoryTheory

namespace AlgebraicGeometry

variable (A : Type u') [Category.{v'} A]
variable (P Q : MorphismProperty Scheme.{u})
variable [P.IsStableUnderComposition] [P.IsStableUnderBaseChange]
variable {X Y : Scheme.{u}}

namespace Compactification

variable {f : X ⟶ Y} (c : Compactification f) (hi : P c.i)
variable [∀ F : (P.Over ⊤ X)ᵒᵖ ⥤ A, (MorphismProperty.Over.map ⊤ hi).op.HasLeftKanExtension F]
variable [HasWeakSheafify (c.Z.smallGrothendieckTopology Q (Q := P)) A]
variable [(MorphismProperty.Over.pullback P ⊤ c.g).IsContinuous
    (Y.smallGrothendieckTopology Q (Q := P)) (c.Z.smallGrothendieckTopology Q (Q := P))]

/-- The lower shriek associated with a compactification `X ⟶[i] Z ⟶[g] Y` of `f`: the
extension by zero `i_!` followed by the pushforward `g_*`. -/
noncomputable def lowerShriek :
    Sheaf (X.smallGrothendieckTopology Q (Q := P)) A ⥤
      Sheaf (Y.smallGrothendieckTopology Q (Q := P)) A :=
  GrothendieckTopology.localizationLowerShriek A P Q c.i hi ⋙
    GrothendieckTopology.lowerStar A P Q c.g

end Compactification

variable (f : X ⟶ Y) [HasCompactification f] (hP : @IsOpenImmersion ≤ P)
variable [∀ F : (P.Over ⊤ X)ᵒᵖ ⥤ A,
  (MorphismProperty.Over.map ⊤
    (hP _ (HasCompactification.compactification f).isOpenImmersion)).op.HasLeftKanExtension F]
variable [∀ Z : Scheme.{u}, HasWeakSheafify (Z.smallGrothendieckTopology Q (Q := P)) A]
variable [∀ (Z : Scheme.{u}) (g : Z ⟶ Y),
  (MorphismProperty.Over.pullback P ⊤ g).IsContinuous
    (Y.smallGrothendieckTopology Q (Q := P)) (Z.smallGrothendieckTopology Q (Q := P))]

/-- The lower shriek `f_!` along a morphism `f` admitting a compactification: the
composition `i_! ⋙ g_*` associated with the chosen compactification
`HasCompactification.compactification f`. -/
noncomputable def lowerShriek :
    Sheaf (X.smallGrothendieckTopology Q (Q := P)) A ⥤
      Sheaf (Y.smallGrothendieckTopology Q (Q := P)) A :=
  (HasCompactification.compactification f).lowerShriek A P Q
    (hP _ (HasCompactification.compactification f).isOpenImmersion)

/-- The lower shriek of `f` is definitionally the extension by zero along the open
immersion of the chosen compactification followed by the pushforward along its proper
structure morphism. -/
lemma lowerShriek_eq :
    lowerShriek A P Q f hP =
      GrothendieckTopology.localizationLowerShriek A P Q
          (HasCompactification.compactification f).i
          (hP _ (HasCompactification.compactification f).isOpenImmersion) ⋙
        GrothendieckTopology.lowerStar A P Q (HasCompactification.compactification f).g :=
  rfl

end AlgebraicGeometry
