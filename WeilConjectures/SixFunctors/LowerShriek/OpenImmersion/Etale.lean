/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.Mathlib.CategoryTheory.MorphismProperty.OverAdjunction
public import WeilConjectures.SixFunctors.LowerShriek.OpenImmersion.Defs
public import WeilConjectures.SixFunctors.UpperLowerStar.Etale

/-!

# Lower shriek on small étale sites along an open immersion

For an open immersion `j : U ⟶ X`, the localization lower shriek of
`WeilConjectures.SixFunctors.LowerShriek.OpenImmersion.Defs` (with `P = Q = @Etale`) specializes to
the small étale sites. This file records the resulting functor
`j_! : Sheaf U.smallEtaleTopology A ⥤ Sheaf X.smallEtaleTopology A`.

In contrast to the general situation, for an open immersion no Kan extension existence
hypothesis is needed: an open immersion is a monomorphism, so the existence and the left
exactness of the presheaf-level left Kan extension are provided by the `P`-general
instances of `WeilConjectures.CategoryTheory.GrothendieckAbelian.HasLeftKanExtension`,
whose indexing comma categories are either empty or admit a terminal object.

Since an open immersion `j` is in particular étale, the pullback `j^*` of
`WeilConjectures.SixFunctors.UpperLowerStar.Etale` is available without further hypotheses
and is computed by restriction along the localization functor. This yields the adjunction
`j_! ⊣ j^*`, completing the triple `j_! ⊣ j^* ⊣ j_*` on the small étale sites.

## Main definitions

- `AlgebraicGeometry.Etale.openImmersionLowerShriek`: the lower shriek `j_!` on étale
  sheaves along an open immersion `j`.
- `AlgebraicGeometry.Etale.openImmersionRestriction`: the restriction `j^*` along an open
  immersion `j`, given objectwise by `(j^* G)(T → U) = G(T → U → X)`.
- `AlgebraicGeometry.Etale.openImmersionLowerShriekAdjunction`: the adjunction
  `j_! ⊣ j^*` with the restriction.
- `AlgebraicGeometry.Etale.upperStarIsoOpenImmersionRestriction`: the pullback `j^*` of
  `WeilConjectures.SixFunctors.UpperLowerStar.Etale` is computed by restriction.
- `AlgebraicGeometry.Etale.openImmersionLowerShriekUpperStarAdjunction`: the adjunction
  `j_! ⊣ j^*` between the lower shriek and the pullback `Etale.upperStar`.
- `AlgebraicGeometry.Etale.preservesFiniteLimits_openImmersionLowerShriek` and
  `AlgebraicGeometry.Etale.preservesFiniteColimits_openImmersionLowerShriek`: the lower
  shriek `j_!` is exact when `j` is an open immersion. The left exactness of the
  presheaf-level lower shriek is the `P`-general
  `CategoryTheory.GrothendieckTopology.preservesFiniteLimits_op_lan_overMap` of
  `WeilConjectures.CategoryTheory.GrothendieckAbelian.HasLeftKanExtension`.

-/

@[expose] public section

universe u' u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

section LowerShriek

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- The restriction `j^*` along an open immersion `j : U ⟶ X` on sheaves for the small
étale sites, given objectwise by `(j^* G)(T → U) = G(T → U → X)`. In contrast to
`Etale.upperStar` it requires neither Kan extensions nor sheafification. -/
def Etale.openImmersionRestriction :
    Sheaf X.smallEtaleTopology A ⥤ Sheaf U.smallEtaleTopology A :=
  GrothendieckTopology.localizationRestriction A @Etale @Etale le_rfl j inferInstance

omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] in
/-- The sections of `j^* G` over `T → U` are the sections of `G` over `T → U → X`. -/
lemma Etale.openImmersionRestriction_obj_val_obj (G : Sheaf X.smallEtaleTopology A)
    (b : U.Etale) :
    ((Etale.openImmersionRestriction A j).obj G).obj.obj (op b) =
      G.obj.obj (op ((MorphismProperty.Over.map ⊤ (inferInstance : @Etale _ _ j)).obj b)) :=
  rfl

/-- Restriction along an open immersion is left adjoint to the pushforward `j_*`: this is
the right half of the triple `j_! ⊣ j^* ⊣ j_*`. -/
noncomputable def Etale.openImmersionRestrictionLowerStarAdjunction :
    Etale.openImmersionRestriction A j ⊣ Etale.lowerStar A j :=
  GrothendieckTopology.localizationRestrictionLowerStarAdjunction A @Etale @Etale le_rfl j
    inferInstance

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

/-- The restriction `j^*` along an open immersion on étale sheaves is additive. -/
instance Etale.openImmersionRestriction_additive :
    (Etale.openImmersionRestriction A j).Additive where

/-- The lower shriek `j_!` along an open immersion `j : U ⟶ X` on sheaves for the small
étale sites. -/
noncomputable def Etale.openImmersionLowerShriek :
    Sheaf U.smallEtaleTopology A ⥤ Sheaf X.smallEtaleTopology A :=
  GrothendieckTopology.localizationLowerShriek A @Etale @Etale j inferInstance

/-- The adjunction `j_! ⊣ j^*` between the extension by zero and the restriction along an
open immersion. -/
noncomputable def Etale.openImmersionLowerShriekAdjunction :
    Etale.openImmersionLowerShriek A j ⊣ Etale.openImmersionRestriction A j :=
  GrothendieckTopology.localizationLowerShriekAdjunction A @Etale @Etale le_rfl j inferInstance

instance : (Etale.openImmersionLowerShriek A j).IsLeftAdjoint :=
  (Etale.openImmersionLowerShriekAdjunction A j).isLeftAdjoint

instance : (Etale.openImmersionRestriction A j).IsRightAdjoint :=
  (Etale.openImmersionLowerShriekAdjunction A j).isRightAdjoint

/-- The extension by zero `j_!` along an open immersion on étale sheaves with values in a
preadditive category is additive, being left adjoint to the additive restriction `j^*`. -/
instance Etale.openImmersionLowerShriek_additive :
    (Etale.openImmersionLowerShriek A j).Additive :=
  (Etale.openImmersionLowerShriekAdjunction A j).left_adjoint_additive

/-- The extension by zero `j_!` along an open immersion on étale sheaves with values in an
abelian category is exact. This is the left exactness half.

`j_!` is the presheaf-level left Kan extension followed by sheafification, and both factors
are left exact: the first by the `P`-general
`CategoryTheory.GrothendieckTopology.preservesFiniteLimits_op_lan_overMap`, the second by
the left exactness of sheafification, which is the content of `HasSheafify` beyond the
`HasWeakSheafify` needed to define `j_!`; both are provided for the Grothendieck abelian
coefficient category `A`, the second by the sorried instance of
`WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify`. -/
instance Etale.preservesFiniteLimits_openImmersionLowerShriek :
    PreservesFiniteLimits (Etale.openImmersionLowerShriek A j) := by
  have heq : Etale.openImmersionLowerShriek A j =
      sheafToPresheaf U.smallEtaleTopology A ⋙
        localizationLowerShriekPresheaf A @Etale j inferInstance ⋙
          presheafToSheaf X.smallEtaleTopology A :=
    rfl
  have hlan : PreservesFiniteLimits (localizationLowerShriekPresheaf A @Etale j inferInstance) :=
    GrothendieckTopology.preservesFiniteLimits_op_lan_overMap A @Etale inferInstance
  rw [heq]
  exact comp_preservesFiniteLimits _ _

/-- Together with `Etale.preservesFiniteLimits_openImmersionLowerShriek` this
makes `j_!` exact. -/
example : PreservesFiniteColimits (Etale.openImmersionLowerShriek A j) :=
  inferInstance

section UpperStar

/-- For an open immersion `j`, the pullback `j^*` of
`WeilConjectures.SixFunctors.UpperLowerStar.Etale` is computed by restriction along the
localization functor: both are left adjoint to `j_*`. In particular its sections are given
by `Etale.openImmersionRestriction_obj_val_obj`. -/
noncomputable def Etale.upperStarIsoOpenImmersionRestriction :
    Etale.upperStar A j ≅ Etale.openImmersionRestriction A j :=
  (Etale.upperStarLowerStarAdjunction A j).leftAdjointUniq
    (Etale.openImmersionRestrictionLowerStarAdjunction A j)

/-- The adjunction `j_! ⊣ j^*` between the lower shriek along an open immersion and the
pullback `Etale.upperStar`. -/
noncomputable def Etale.openImmersionLowerShriekUpperStarAdjunction :
    Etale.openImmersionLowerShriek A j ⊣ Etale.upperStar A j :=
  (Etale.openImmersionLowerShriekAdjunction A j).ofNatIsoRight
    (Etale.upperStarIsoOpenImmersionRestriction A j).symm

end UpperStar

end LowerShriek

end AlgebraicGeometry
