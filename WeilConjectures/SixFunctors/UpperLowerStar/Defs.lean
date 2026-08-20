/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasLeftKanExtension
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.IsContinuous
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasLeftKanExtension
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.IsContinuous

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

- The coefficient category `A` is a Grothendieck abelian category with `Hom`-types in the
  universe `u` of the base schemes, following the convention of the `SixFunctors` folder.
- Both functors are defined along the base change functor, which exists for an *arbitrary*
  morphism `g` — in contrast to the localization functor `MorphismProperty.Over.map ⊤ h`
  of `WeilConjectures.SixFunctors.LowerShriek.OpenImmersion.Defs`, which requires `P g`.
  This is essential for compactifications, whose structure morphism is proper and in
  general does not satisfy `P`.
- The continuity of the base change functor along an arbitrary morphism, the left Kan
  extensions on presheaves and the sheafification entering the definitions are provided,
  for `Q ≤ P`, by the sorried results of the folder
  `WeilConjectures.CategoryTheory.GrothendieckAbelian`, under the multiplicativity-type
  assumptions on `P` and `Q` assumed throughout; all of them
  hold for `P = Q = @Etale`. The inequality `hQP : Q ≤ P` is an explicit argument of the
  definitions using continuity. For `g` satisfying `P` the continuity is proved as
  `CategoryTheory.GrothendieckTopology.isContinuous_overPullback_of_le` in
  `WeilConjectures.SixFunctors.LowerShriek.Defs`, and for the small étale sites along an
  arbitrary morphism as `AlgebraicGeometry.Etale.isContinuous_overPullback` in
  `WeilConjectures.SixFunctors.UpperLowerStar.Etale`.

-/

@[expose] public section

universe u' u

open CategoryTheory Category Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme

namespace CategoryTheory

variable (A : Type u') [Category.{u} A] [Abelian A] [IsGrothendieckAbelian.{u} A]

namespace GrothendieckTopology

variable (P Q : MorphismProperty Scheme.{u})
variable [P.IsMultiplicative] [P.IsStableUnderBaseChange] [P.HasOfPostcompProperty P]
  [Q.IsMultiplicative] [Q.IsStableUnderBaseChange]
variable (hQP : Q ≤ P)

variable {W U : Scheme.{u}} (g : W ⟶ U)

/-- The pushforward `g_*` along `g : W ⟶ U`, given objectwise by
`(g_* G)(V → U) = G(V ×_U W → W)`. The continuity of the base change functor is provided
by the sorried `CategoryTheory.GrothendieckTopology.isContinuous_overPullback` of
`WeilConjectures.CategoryTheory.GrothendieckAbelian.IsContinuous`. -/
noncomputable def lowerStar :
    Sheaf (W.smallGrothendieckTopology Q (Q := P)) A ⥤
      Sheaf (U.smallGrothendieckTopology Q (Q := P)) A :=
  have := isContinuous_overPullback P Q hQP g
  (MorphismProperty.Over.pullback P ⊤ g).sheafPushforwardContinuous A
    (U.smallGrothendieckTopology Q (Q := P)) (W.smallGrothendieckTopology Q (Q := P))

omit [Abelian A] [IsGrothendieckAbelian.{u} A] in
/-- The sections of `g_* G` over `V → U` are the sections of `G` over `V ×_U W → W`. -/
lemma lowerStar_obj_val_obj
    (G : Sheaf (W.smallGrothendieckTopology Q (Q := P)) A) (b : P.Over ⊤ U) :
    ((lowerStar A P Q hQP g).obj G).obj.obj (op b) =
      G.obj.obj (op ((MorphismProperty.Over.pullback P ⊤ g).obj b)) :=
  rfl

omit [Abelian A] [IsGrothendieckAbelian.{u} A] in
/-- `g_*` acts on morphisms by whiskering along `(MorphismProperty.Over.pullback P ⊤ g).op`. -/
lemma lowerStar_map_hom_app
    {G G' : Sheaf (W.smallGrothendieckTopology Q (Q := P)) A} (φ : G ⟶ G') (b : P.Over ⊤ U) :
    (((lowerStar A P Q hQP g).map φ).hom).app (op b) =
      φ.hom.app (op ((MorphismProperty.Over.pullback P ⊤ g).obj b)) :=
  rfl

/-- `g_*` preserves limits of any shape that exists in the coefficient category: it is
given by restriction along the base change functor, and limits of sheaves are computed
pointwise on the underlying presheaves. -/
instance preservesLimitsOfShape_lowerStar (E : Type*) [Category E] [HasLimitsOfShape E A] :
    PreservesLimitsOfShape E (lowerStar A P Q hQP g) :=
  have := isContinuous_overPullback P Q hQP g
  inferInstanceAs (PreservesLimitsOfShape E
    ((MorphismProperty.Over.pullback P ⊤ g).sheafPushforwardContinuous A
      (U.smallGrothendieckTopology Q (Q := P)) (W.smallGrothendieckTopology Q (Q := P))))

/-- `g_*` is left exact. Note that this does not use the adjunction `g^* ⊣ g_*`, which is
only available under the extra hypotheses of the section below. -/
instance preservesFiniteLimits_lowerStar :
    PreservesFiniteLimits (lowerStar A P Q hQP g) :=
  have := isContinuous_overPullback P Q hQP g
  inferInstanceAs (PreservesFiniteLimits
    ((MorphismProperty.Over.pullback P ⊤ g).sheafPushforwardContinuous A
      (U.smallGrothendieckTopology Q (Q := P)) (W.smallGrothendieckTopology Q (Q := P))))

section Adjunction

/-- The pullback `g^*` along `g : W ⟶ U`: left Kan extension on presheaves followed by
sheafification, left adjoint to `lowerStar`. The Kan extensions and the sheafification
are provided by the sorried instances of
`WeilConjectures.CategoryTheory.GrothendieckAbelian.HasLeftKanExtension` and
`WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify`. -/
noncomputable def upperStar :
    Sheaf (U.smallGrothendieckTopology Q (Q := P)) A ⥤
      Sheaf (W.smallGrothendieckTopology Q (Q := P)) A :=
  Functor.sheafPullbackConstruction.sheafPullback (MorphismProperty.Over.pullback P ⊤ g) A
    (U.smallGrothendieckTopology Q (Q := P)) (W.smallGrothendieckTopology Q (Q := P))

/-- The adjunction `g^* ⊣ g_*`. -/
noncomputable def upperStarLowerStarAdjunction :
    upperStar A P Q g ⊣ lowerStar A P Q hQP g :=
  have := isContinuous_overPullback P Q hQP g
  Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (MorphismProperty.Over.pullback P ⊤ g) A
    (U.smallGrothendieckTopology Q (Q := P)) (W.smallGrothendieckTopology Q (Q := P))

instance : (lowerStar A P Q hQP g).IsRightAdjoint :=
  (upperStarLowerStarAdjunction A P Q hQP g).isRightAdjoint

include hQP in
/-- `g^*` is a left adjoint. Not an instance, since its statement does not determine the
inequality `hQP : Q ≤ P` entering the adjunction `g^* ⊣ g_*`; for the small étale sites
the corresponding instance is registered in
`WeilConjectures.SixFunctors.UpperLowerStar.Etale`. -/
lemma isLeftAdjoint_upperStar : (upperStar A P Q g).IsLeftAdjoint :=
  (upperStarLowerStarAdjunction A P Q hQP g).isLeftAdjoint

/-- `g^*` is left exact as soon as the left Kan extension along the base change functor is:
`g^*` is the composite of the inclusion of sheaves into presheaves, which preserves finite
limits, that left Kan extension, and sheafification, which is left exact by
`HasSheafify`. Unlike `preservesFiniteLimits_lowerStar` this is not automatic; see
`AlgebraicGeometry.Etale.preservesFiniteLimits_op_lan_overPullback` for the case of an étale
morphism, where the Kan extension is precomposition with a right adjoint. -/
instance preservesFiniteLimits_upperStar
    [PreservesFiniteLimits ((MorphismProperty.Over.pullback P ⊤ g).op.lan :
      ((P.Over ⊤ U)ᵒᵖ ⥤ A) ⥤ (P.Over ⊤ W)ᵒᵖ ⥤ A)] :
    PreservesFiniteLimits (upperStar A P Q g) := by
  unfold upperStar Functor.sheafPullbackConstruction.sheafPullback
  infer_instance

end Adjunction

section Comp

variable {R S T : Scheme.{u}} (h₁ : T ⟶ S) (h₂ : S ⟶ R)

/-- The composition isomorphism `(h₁)_* ⋙ (h₂)_* ≅ (h₁ ≫ h₂)_*` of pushforwards on
sheaves for the small sites: both sides send a sheaf `G` to the sheaf
`(V → R) ↦ G(V ×_R T → T)`, up to the pullback pasting isomorphism
`(V ×_R S) ×_S T ≅ V ×_R T` of `MorphismProperty.Over.pullbackComp`. -/
noncomputable def lowerStarComp :
    lowerStar A P Q hQP h₁ ⋙ lowerStar A P Q hQP h₂ ≅ lowerStar A P Q hQP (h₁ ≫ h₂) :=
  have := isContinuous_overPullback P Q hQP h₁
  have := isContinuous_overPullback P Q hQP h₂
  have := isContinuous_overPullback P Q hQP (h₁ ≫ h₂)
  Functor.sheafPushforwardContinuousComp'
    (eFG := (MorphismProperty.Over.pullbackComp (P := P) (Q := ⊤) h₁ h₂).symm) A
    (R.smallGrothendieckTopology Q (Q := P)) (S.smallGrothendieckTopology Q (Q := P))
    (T.smallGrothendieckTopology Q (Q := P))

section UpperStar

/-- The composition isomorphism `(h₁ ≫ h₂)^* ≅ (h₂)^* ⋙ (h₁)^*` of pullbacks on sheaves
for the small sites, obtained from the composition isomorphism `lowerStarComp` of the
pushforwards by uniqueness of left adjoints: both sides are left adjoint to
`(h₁)_* ⋙ (h₂)_*`. -/
noncomputable def upperStarComp :
    upperStar A P Q (h₁ ≫ h₂) ≅ upperStar A P Q h₂ ⋙ upperStar A P Q h₁ :=
  ((conjugateIsoEquiv (upperStarLowerStarAdjunction A P Q hQP (h₁ ≫ h₂))
      ((upperStarLowerStarAdjunction A P Q hQP h₂).comp
        (upperStarLowerStarAdjunction A P Q hQP h₁))).symm
    (lowerStarComp A P Q hQP h₁ h₂).symm).symm

end UpperStar

end Comp

end GrothendieckTopology

end CategoryTheory
