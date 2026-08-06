/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib

/-!

# The pushforward `g_*` and the pullback `g^*` on small sites of schemes

Let `P` and `Q` be morphism properties of schemes. For an *arbitrary* morphism of schemes
`g : W ⟶ U`, base change induces the functor
`MorphismProperty.Over.pullback P ⊤ g : P.Over ⊤ U ⥤ P.Over ⊤ W` between the small sites,
and composition with it defines the pushforward `g_*` on `A`-valued sheaves for the small
`Q`-topologies. Its left adjoint `g^*` is the left Kan extension on presheaves followed by
sheafification.

## Main definitions

- `CategoryTheory.GrothendieckTopology.lowerStar`: the pushforward `g_*`, given by
  composition with the base change functor.
- `CategoryTheory.GrothendieckTopology.upperStar`: the pullback `g^*`, given by left Kan
  extension on presheaves followed by sheafification.
- `CategoryTheory.GrothendieckTopology.upperStarLowerStarAdjunction`: the adjunction
  `g^* ⊣ g_*`.

## Implementation notes

- Both functors are defined along the base change functor, which exists for an *arbitrary*
  morphism `g` — in contrast to the localization functor `MorphismProperty.Over.map ⊤ h`
  of `WeilConjectures.SixFunctors.LowerShriek.OpenImmersion.Defs`, which requires `P g`.
  This is essential for compactifications, whose structure morphism is proper and in
  general does not satisfy `P`.
- The continuity of the base change functor for the small `Q`-topologies is assumed as an
  instance hypothesis; for `g` satisfying `P` it is provided by
  `CategoryTheory.GrothendieckTopology.isContinuous_overPullback_of_le` of
  `WeilConjectures.SixFunctors.LowerShriek.Defs`.

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

variable [(MorphismProperty.Over.pullback P ⊤ g).IsContinuous
    (U.smallGrothendieckTopology Q (Q := P)) (W.smallGrothendieckTopology Q (Q := P))]

/-- The pushforward `g_*` along `g : W ⟶ U`, given objectwise by
`(g_* G)(V → U) = G(V ×_U W → W)`. -/
noncomputable def lowerStar :
    Sheaf (W.smallGrothendieckTopology Q (Q := P)) A ⥤
      Sheaf (U.smallGrothendieckTopology Q (Q := P)) A :=
  (MorphismProperty.Over.pullback P ⊤ g).sheafPushforwardContinuous A
    (U.smallGrothendieckTopology Q (Q := P)) (W.smallGrothendieckTopology Q (Q := P))

/-- The sections of `g_* G` over `V → U` are the sections of `G` over `V ×_U W → W`. -/
lemma lowerStar_obj_val_obj
    (G : Sheaf (W.smallGrothendieckTopology Q (Q := P)) A) (b : P.Over ⊤ U) :
    ((lowerStar A P Q g).obj G).obj.obj (op b) =
      G.obj.obj (op ((MorphismProperty.Over.pullback P ⊤ g).obj b)) :=
  rfl

/-- `g_*` acts on morphisms by whiskering along `(MorphismProperty.Over.pullback P ⊤ g).op`. -/
lemma lowerStar_map_hom_app
    {G G' : Sheaf (W.smallGrothendieckTopology Q (Q := P)) A} (φ : G ⟶ G') (b : P.Over ⊤ U) :
    (((lowerStar A P Q g).map φ).hom).app (op b) =
      φ.hom.app (op ((MorphismProperty.Over.pullback P ⊤ g).obj b)) :=
  rfl

section Adjunction

variable [∀ F : (P.Over ⊤ U)ᵒᵖ ⥤ A,
  (MorphismProperty.Over.pullback P ⊤ g).op.HasLeftKanExtension F]
variable [HasWeakSheafify (W.smallGrothendieckTopology Q (Q := P)) A]

/-- The pullback `g^*` along `g : W ⟶ U`: left Kan extension on presheaves followed by
sheafification, left adjoint to `lowerStar`. -/
noncomputable def upperStar :
    Sheaf (U.smallGrothendieckTopology Q (Q := P)) A ⥤
      Sheaf (W.smallGrothendieckTopology Q (Q := P)) A :=
  Functor.sheafPullbackConstruction.sheafPullback (MorphismProperty.Over.pullback P ⊤ g) A
    (U.smallGrothendieckTopology Q (Q := P)) (W.smallGrothendieckTopology Q (Q := P))

/-- The adjunction `g^* ⊣ g_*`. -/
noncomputable def upperStarLowerStarAdjunction :
    upperStar A P Q g ⊣ lowerStar A P Q g :=
  Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (MorphismProperty.Over.pullback P ⊤ g) A
    (U.smallGrothendieckTopology Q (Q := P)) (W.smallGrothendieckTopology Q (Q := P))

instance : (lowerStar A P Q g).IsRightAdjoint :=
  (upperStarLowerStarAdjunction A P Q g).isRightAdjoint

instance : (upperStar A P Q g).IsLeftAdjoint :=
  (upperStarLowerStarAdjunction A P Q g).isLeftAdjoint

end Adjunction

end GrothendieckTopology

end CategoryTheory
