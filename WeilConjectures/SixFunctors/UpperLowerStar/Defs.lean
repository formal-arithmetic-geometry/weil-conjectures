/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib
public import WeilConjectures.Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous

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
- `CategoryTheory.GrothendieckTopology.lowerStarComp` and
  `CategoryTheory.GrothendieckTopology.upperStarComp`: the composition isomorphisms
  `(h₁)_* ⋙ (h₂)_* ≅ (h₁ ≫ h₂)_*` and `(h₁ ≫ h₂)^* ≅ (h₂)^* ⋙ (h₁)^*`, the latter
  obtained from the former by uniqueness of left adjoints.

## Main results

- `CategoryTheory.GrothendieckTopology.preservesLimitsOfShape_lowerStar` and
  `CategoryTheory.GrothendieckTopology.preservesFiniteLimits_lowerStar`: the pushforward
  `g_*` preserves every limit that exists in the coefficient category. This needs no
  hypothesis beyond the continuity of the base change functor, in particular it does not
  use the adjunction `g^* ⊣ g_*`.
- `CategoryTheory.GrothendieckTopology.preservesFiniteLimits_upperStar`: the pullback `g^*`
  is left exact, provided sheafification is and the left Kan extension along the opposite
  of the base change functor is. In contrast to `g_*` this is not automatic; see
  `AlgebraicGeometry.Etale.preservesFiniteLimits_op_lan_overPullback` for the case of an
  étale morphism, where the Kan extension is precomposition with a right adjoint.

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

/-- `g_*` preserves limits of any shape that exists in the coefficient category: it is
given by restriction along the base change functor, and limits of sheaves are computed
pointwise on the underlying presheaves. -/
instance preservesLimitsOfShape_lowerStar (E : Type*) [Category E] [HasLimitsOfShape E A] :
    PreservesLimitsOfShape E (lowerStar A P Q g) := by
  unfold lowerStar
  infer_instance

/-- `g_*` is left exact. Note that this does not use the adjunction `g^* ⊣ g_*`, which is
only available under the extra hypotheses of the section below. -/
instance preservesFiniteLimits_lowerStar [HasFiniteLimits A] :
    PreservesFiniteLimits (lowerStar A P Q g) := by
  unfold lowerStar
  infer_instance

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

/-- `g^*` is left exact as soon as the left Kan extension along the base change functor is:
`g^*` is the composite of the inclusion of sheaves into presheaves, which preserves finite
limits, that left Kan extension, and sheafification, which is left exact by
`HasSheafify`. Unlike `preservesFiniteLimits_lowerStar` this is not automatic; see
`AlgebraicGeometry.Etale.preservesFiniteLimits_op_lan_overPullback` for the case of an étale
morphism, where the Kan extension is precomposition with a right adjoint. -/
instance preservesFiniteLimits_upperStar [HasFiniteLimits A]
    [HasSheafify (W.smallGrothendieckTopology Q (Q := P)) A]
    [PreservesFiniteLimits ((MorphismProperty.Over.pullback P ⊤ g).op.lan :
      ((P.Over ⊤ U)ᵒᵖ ⥤ A) ⥤ (P.Over ⊤ W)ᵒᵖ ⥤ A)] :
    PreservesFiniteLimits (upperStar A P Q g) := by
  unfold upperStar Functor.sheafPullbackConstruction.sheafPullback
  infer_instance

end Adjunction

section Comp

variable {R S T : Scheme.{u}} (h₁ : T ⟶ S) (h₂ : S ⟶ R)

variable [(MorphismProperty.Over.pullback P ⊤ h₁).IsContinuous
    (S.smallGrothendieckTopology Q (Q := P)) (T.smallGrothendieckTopology Q (Q := P))]
  [(MorphismProperty.Over.pullback P ⊤ h₂).IsContinuous
    (R.smallGrothendieckTopology Q (Q := P)) (S.smallGrothendieckTopology Q (Q := P))]
  [(MorphismProperty.Over.pullback P ⊤ (h₁ ≫ h₂)).IsContinuous
    (R.smallGrothendieckTopology Q (Q := P)) (T.smallGrothendieckTopology Q (Q := P))]

/-- The composition isomorphism `(h₁)_* ⋙ (h₂)_* ≅ (h₁ ≫ h₂)_*` of pushforwards on
sheaves for the small sites: both sides send a sheaf `G` to the sheaf
`(V → R) ↦ G(V ×_R T → T)`, up to the pullback pasting isomorphism
`(V ×_R S) ×_S T ≅ V ×_R T` of `MorphismProperty.Over.pullbackComp`. -/
noncomputable def lowerStarComp :
    lowerStar A P Q h₁ ⋙ lowerStar A P Q h₂ ≅ lowerStar A P Q (h₁ ≫ h₂) :=
  Functor.sheafPushforwardContinuousComp'
    (eFG := (MorphismProperty.Over.pullbackComp (P := P) (Q := ⊤) h₁ h₂).symm) A
    (R.smallGrothendieckTopology Q (Q := P)) (S.smallGrothendieckTopology Q (Q := P))
    (T.smallGrothendieckTopology Q (Q := P))

section UpperStar

variable [∀ F : (P.Over ⊤ S)ᵒᵖ ⥤ A,
    (MorphismProperty.Over.pullback P ⊤ h₁).op.HasLeftKanExtension F]
  [∀ F : (P.Over ⊤ R)ᵒᵖ ⥤ A,
    (MorphismProperty.Over.pullback P ⊤ h₂).op.HasLeftKanExtension F]
  [∀ F : (P.Over ⊤ R)ᵒᵖ ⥤ A,
    (MorphismProperty.Over.pullback P ⊤ (h₁ ≫ h₂)).op.HasLeftKanExtension F]
  [HasWeakSheafify (S.smallGrothendieckTopology Q (Q := P)) A]
  [HasWeakSheafify (T.smallGrothendieckTopology Q (Q := P)) A]

/-- The composition isomorphism `(h₁ ≫ h₂)^* ≅ (h₂)^* ⋙ (h₁)^*` of pullbacks on sheaves
for the small sites, obtained from the composition isomorphism `lowerStarComp` of the
pushforwards by uniqueness of left adjoints: both sides are left adjoint to
`(h₁)_* ⋙ (h₂)_*`. -/
noncomputable def upperStarComp :
    upperStar A P Q (h₁ ≫ h₂) ≅ upperStar A P Q h₂ ⋙ upperStar A P Q h₁ :=
  ((conjugateIsoEquiv (upperStarLowerStarAdjunction A P Q (h₁ ≫ h₂))
      ((upperStarLowerStarAdjunction A P Q h₂).comp
        (upperStarLowerStarAdjunction A P Q h₁))).symm
    (lowerStarComp A P Q h₁ h₂).symm).symm

end UpperStar

end Comp

end GrothendieckTopology

end CategoryTheory
