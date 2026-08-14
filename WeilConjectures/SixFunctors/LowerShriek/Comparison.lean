/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib
public import WeilConjectures.Mathlib.CategoryTheory.MorphismProperty.OverAdjunction
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
public import WeilConjectures.SixFunctors.LowerShriek.Etale
public import WeilConjectures.SixFunctors.UpperLowerStar.Comp

/-!

# The canonical comparison `f_! ⟶ f_*`

For a morphism `f : X ⟶ Y` admitting a compactification `X --i--> Z --g--> Y`, this file
constructs the canonical natural transformation

`ι_f : f_! ⟶ f_*`

from the lower shriek to the pushforward on étale sheaves.

The construction proceeds through the adjoint triple `i_! ⊣ i^* ⊣ i_*` of the open
immersion `i`:

- Since `i` is a monomorphism, the localization functor `MorphismProperty.Over.map` of
  the small étale sites along `i` is fully faithful
  (`CategoryTheory.MorphismProperty.Over.full_map`), so the unit of the site-level
  adjunction `MorphismProperty.Over.mapPullbackAdj` is an isomorphism, and hence so is
  the counit of the induced sheaf-level adjunction `i^* ⊣ i_*`
  (`CategoryTheory.Adjunction.isIso_sheafPushforwardContinuous_counit`); this expresses
  that the restriction of a pushforward along an open immersion is the original sheaf.
- Inverting this counit and contracting with the counit of `i_! ⊣ i^*` yields the
  canonical map `i_! ⟶ i_*` (`Etale.openImmersionLowerShriekToLowerStar`).
- Pushing forward along `g` and composing with the composition isomorphism
  `Etale.lowerStarComp` gives `ι_f : f_! = g_* ∘ i_! ⟶ g_* ∘ i_* ≅ f_*`
  (`Etale.lowerShriekToLowerStar`).

For a proper morphism `f`, the comparison `ι_f` is an isomorphism
(`Etale.isIso_lowerShriekToLowerStar`, stated with `sorry`): the open immersion into a
compactification of a proper morphism is also proper, hence a closed and open immersion,
and extension by zero along an open and closed immersion agrees with the pushforward.

## Main definitions

- `AlgebraicGeometry.Etale.openImmersionLowerShriekToLowerStar`: the canonical map
  `i_! ⟶ i_*` for an open immersion `i`.
- `AlgebraicGeometry.Etale.lowerShriekToLowerStar`: the canonical comparison
  `ι_f : f_! ⟶ f_*` for `f` admitting a compactification.
- `AlgebraicGeometry.Etale.isIso_lowerShriekToLowerStar`: for proper `f`, the comparison
  `ι_f` is an isomorphism.

-/

@[expose] public section

universe w v' u' u

open CategoryTheory Category Limits Opposite

namespace AlgebraicGeometry

open Scheme

variable (A : Type u') [Category.{v'} A]

section OpenImmersion

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- The counit of the adjunction `j^* ⊣ j_*` along an open immersion `j` is an
isomorphism: the restriction of a pushforward along an open immersion is the original
sheaf. This holds since `j` is a monomorphism, so the unit of the site-level adjunction
`MorphismProperty.Over.mapPullbackAdj` is an isomorphism. -/
instance Etale.isIso_openImmersionRestrictionLowerStarAdjunction_counit :
    IsIso (Etale.openImmersionRestrictionLowerStarAdjunction A j).counit :=
  Adjunction.isIso_sheafPushforwardContinuous_counit A
    (MorphismProperty.Over.mapPullbackAdj @Etale ⊤ j inferInstance trivial)
    (U.smallGrothendieckTopology (Q := @Etale) @Etale)
    (X.smallGrothendieckTopology (Q := @Etale) @Etale)

variable [HasInitial A] [HasWeakSheafify X.smallEtaleTopology A]

/-- The canonical natural transformation `i_! ⟶ i_*` from the extension by zero to the
pushforward along an open immersion, obtained from the adjoint triple `i_! ⊣ i^* ⊣ i_*`:
insert the inverse of the counit of `i^* ⊣ i_*` and contract with the counit of
`i_! ⊣ i^*`. -/
noncomputable def Etale.openImmersionLowerShriekToLowerStar :
    Etale.openImmersionLowerShriek A j ⟶ Etale.lowerStar A j :=
  (Functor.leftUnitor _).inv ≫
    Functor.whiskerRight (inv (Etale.openImmersionRestrictionLowerStarAdjunction A j).counit)
      (Etale.openImmersionLowerShriek A j) ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft (Etale.lowerStar A j)
      (Etale.openImmersionLowerShriekAdjunction A j).counit ≫
    (Functor.rightUnitor _).hom

end OpenImmersion

section Comparison

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]
variable [HasInitial A] [∀ Z : Scheme.{u}, HasWeakSheafify Z.smallEtaleTopology A]

/-- The canonical comparison `ι_f : f_! ⟶ f_*` from the lower shriek to the pushforward
along a morphism `f` admitting a compactification `X --i--> Z --g--> Y`: it is induced by
the canonical map `i_! ⟶ i_*` for the open immersion `i`, using `f_! = g_* ∘ i_!` and the
composition isomorphism `g_* ∘ i_* ≅ (i ≫ g)_* = f_*`. -/
noncomputable def Etale.lowerShriekToLowerStar :
    Etale.lowerShriek A f ⟶ Etale.lowerStar A f :=
  Functor.whiskerRight
      (Etale.openImmersionLowerShriekToLowerStar A (HasCompactification.compactification f).i)
      (Etale.lowerStar A (HasCompactification.compactification f).g) ≫
    (Etale.lowerStarComp A (HasCompactification.compactification f).i
      (HasCompactification.compactification f).g).hom ≫
    eqToHom (by rw [← (HasCompactification.compactification f).comm])

/-- For a **proper** morphism `f`, the canonical comparison `ι_f : f_! ⟶ f_*` is an
isomorphism.

Mathematically, since `f` is proper and the structure morphism `g` of the
compactification is separated, the open immersion `i` is proper as well, hence a closed
immersion; an open and closed immersion `i` satisfies `i_! ≅ i_*` (a section over an
étale `Z`-scheme `V` is determined by its restrictions to the open and closed
complementary pieces of `V`), so the induced comparison of the composites is an
isomorphism. -/
theorem Etale.isIso_lowerShriekToLowerStar [IsProper f] :
    IsIso (Etale.lowerShriekToLowerStar A f) :=
  sorry

end Comparison

end AlgebraicGeometry
