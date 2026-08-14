/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib
public import WeilConjectures.SixFunctors.LowerShriek.OpenImmersion.Defs
public import WeilConjectures.SixFunctors.UpperLowerStar.Etale

/-!

# Lower shriek on small étale sites along an open immersion

For an open immersion `j : U ⟶ X`, the localization lower shriek of
`WeilConjectures.SixFunctors.LowerShriek.OpenImmersion.Defs` (with `P = Q = @Etale`) specializes to
the small étale sites. This file records the resulting functor
`j_! : Sheaf U.smallEtaleTopology A ⥤ Sheaf X.smallEtaleTopology A`.

In contrast to the general situation, for an open immersion no Kan extension existence
hypothesis is needed: the comma category indexing the pointwise left Kan extension at
`V : X.Etale` is governed by the type `Scheme.Etale.LiftIndex j V` of factorizations of
the structure morphism of `V` through `j`. For a monomorphism `j` a lift induces a
terminal object of the comma category, and if no lift exists the comma category is empty;
hence all pointwise left Kan extensions with values in a category with an initial object
exist, which is registered as an instance.

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
  shriek `j_!` is exact when `j` is an open immersion.

-/

@[expose] public section

universe v' u' u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

namespace Scheme

section LiftIndex

variable {U X : Scheme.{u}} (j : U ⟶ X) [Etale j] (V : X.Etale)

/-- The type of lifts of `V : X.Etale` through `j : U ⟶ X`: factorizations of the
structure morphism of `V` through `j`. It indexes the colimit computing the presheaf-level
lower shriek at `V`. -/
private def Etale.LiftIndex : Type u :=
  {α : V.left ⟶ U // α ≫ j = V.hom}

namespace Etale.LiftIndex

variable {j V}

/-- The lift of an étale `X`-scheme through an étale morphism is étale. -/
private lemma etale_val (α : Etale.LiftIndex j V) : Etale α.1 := by
  have h : Etale (α.1 ≫ j) := by
    rw [α.2]
    infer_instance
  exact Etale.of_comp α.1 j

/-- The étale `U`-scheme determined by a lift of `V : X.Etale` through `j`. -/
private def toEtale (α : Etale.LiftIndex j V) : U.Etale :=
  haveI := α.etale_val
  Etale.mk α.1

/-- The comparison morphism from `V` to the image of `α.toEtale` in `X.Etale`; its
underlying morphism is the identity. -/
private def homToComp (α : Etale.LiftIndex j V) :
    V ⟶ (MorphismProperty.Over.map ⊤ ‹Etale j›).obj α.toEtale :=
  MorphismProperty.Over.homMk (𝟙 V.left) ((Category.id_comp _).trans α.2)

/-- The object of the comma category indexing the pointwise left Kan extension at `V`
associated with a lift `α`; for a monomorphism `j` it is terminal, see
`Etale.LiftIndex.isTerminalCostructuredArrow`. -/
private def costructuredArrow (α : Etale.LiftIndex j V) :
    CostructuredArrow (MorphismProperty.Over.map ⊤ ‹Etale j›).op (op V) :=
  CostructuredArrow.mk α.homToComp.op

variable (j V) in
/-- The lift of `V` extracted from an object of the indexing comma category. -/
private def ofCostructuredArrow
    (s : CostructuredArrow (MorphismProperty.Over.map ⊤ ‹Etale j›).op (op V)) :
    Etale.LiftIndex j V :=
  ⟨s.hom.unop.left ≫ s.left.unop.hom, by
    have hw : s.hom.unop.left ≫
        ((MorphismProperty.Over.map ⊤ ‹Etale j›).obj s.left.unop).hom = V.hom :=
      MorphismProperty.Over.w s.hom.unop
    rw [Category.assoc]
    exact hw⟩

variable (j V) in
/-- If `V` has no lift through `j`, the indexing comma category is empty. -/
private lemma isEmpty_costructuredArrow (h : IsEmpty (Etale.LiftIndex j V)) :
    IsEmpty (CostructuredArrow (MorphismProperty.Over.map ⊤ ‹Etale j›).op (op V)) :=
  ⟨fun s => h.elim (ofCostructuredArrow j V s)⟩

/-- For a monomorphism `j`, the comma object associated with a lift `α` of `V` is
terminal: the pointwise left Kan extension formula collapses to a single value. -/
private noncomputable def isTerminalCostructuredArrow [Mono j] (α : Etale.LiftIndex j V) :
    IsTerminal α.costructuredArrow :=
  IsTerminal.ofUniqueHom
    (fun s =>
      CostructuredArrow.homMk
        (Quiver.Hom.op
          (MorphismProperty.Over.homMk s.hom.unop.left
            (by
              rw [← cancel_mono j, Category.assoc]
              have hs : s.hom.unop.left ≫ s.left.unop.hom ≫ j = V.hom :=
                MorphismProperty.Over.w s.hom.unop
              exact hs.trans α.2.symm) :
            α.toEtale ⟶ s.left.unop))
        (by
          apply Quiver.Hom.unop_inj
          apply MorphismProperty.Over.Hom.ext
          exact Category.id_comp _))
    (fun s m => by
      ext
      apply Quiver.Hom.unop_inj
      apply MorphismProperty.Over.Hom.ext
      have hw := m.w
      apply_fun (fun z => z.unop.left) at hw
      exact (Category.id_comp _).symm.trans hw)

end Etale.LiftIndex

end LiftIndex

end Scheme

section KanExtension

variable (A : Type u') [Category.{v'} A]
variable {U X : Scheme.{u}} (j : U ⟶ X) [Etale j]

open Scheme in
/-- Along the localization functor induced by an étale monomorphism `j`, all pointwise
left Kan extensions with values in a category with an initial object exist: the indexing
comma categories are either empty or admit a terminal object. -/
instance [Mono j] [HasInitial A] (F : U.Etaleᵒᵖ ⥤ A) :
    (MorphismProperty.Over.map ⊤ ‹Etale j›).op.HasPointwiseLeftKanExtension F := by
  intro V
  by_cases h : Nonempty (Etale.LiftIndex j V.unop)
  · obtain ⟨α⟩ := h
    haveI : HasTerminal (CostructuredArrow (MorphismProperty.Over.map ⊤ ‹Etale j›).op V) :=
      α.isTerminalCostructuredArrow.hasTerminal
    infer_instance
  · haveI : IsEmpty (CostructuredArrow (MorphismProperty.Over.map ⊤ ‹Etale j›).op V) :=
      Etale.LiftIndex.isEmpty_costructuredArrow j V.unop (not_nonempty_iff.mp h)
    haveI : HasColimitsOfShape
        (CostructuredArrow (MorphismProperty.Over.map ⊤ ‹Etale j›).op V) A :=
      hasColimitsOfShape_of_equivalence (equivalenceOfIsEmpty (Discrete PEmpty.{1}) _)
    infer_instance

end KanExtension

section LowerShriek

variable (A : Type u') [Category.{v'} A]
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- The restriction `j^*` along an open immersion `j : U ⟶ X` on sheaves for the small
étale sites, given objectwise by `(j^* G)(T → U) = G(T → U → X)`. In contrast to
`Etale.upperStar` it requires neither Kan extensions nor sheafification. -/
def Etale.openImmersionRestriction :
    Sheaf X.smallEtaleTopology A ⥤ Sheaf U.smallEtaleTopology A :=
  GrothendieckTopology.localizationRestriction A @Etale @Etale j inferInstance

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
  GrothendieckTopology.localizationRestrictionLowerStarAdjunction A @Etale @Etale j
    inferInstance

/-- The restriction `j^*` along an open immersion on étale sheaves is additive. -/
instance Etale.openImmersionRestriction_additive [Preadditive A] :
    (Etale.openImmersionRestriction A j).Additive where

variable [HasInitial A] [HasWeakSheafify X.smallEtaleTopology A]

/-- The lower shriek `j_!` along an open immersion `j : U ⟶ X` on sheaves for the small
étale sites. -/
noncomputable def Etale.openImmersionLowerShriek :
    Sheaf U.smallEtaleTopology A ⥤ Sheaf X.smallEtaleTopology A :=
  have : HasWeakSheafify (X.smallGrothendieckTopology (Q := @Etale) @Etale) A :=
    inferInstanceAs (HasWeakSheafify X.smallEtaleTopology A)
  GrothendieckTopology.localizationLowerShriek A @Etale @Etale j inferInstance

/-- The adjunction `j_! ⊣ j^*` between the extension by zero and the restriction along an
open immersion. -/
noncomputable def Etale.openImmersionLowerShriekAdjunction :
    Etale.openImmersionLowerShriek A j ⊣ Etale.openImmersionRestriction A j :=
  have : HasWeakSheafify (X.smallGrothendieckTopology (Q := @Etale) @Etale) A :=
    inferInstanceAs (HasWeakSheafify X.smallEtaleTopology A)
  GrothendieckTopology.localizationLowerShriekAdjunction A @Etale @Etale j inferInstance

instance : (Etale.openImmersionLowerShriek A j).IsLeftAdjoint :=
  (Etale.openImmersionLowerShriekAdjunction A j).isLeftAdjoint

instance : (Etale.openImmersionRestriction A j).IsRightAdjoint :=
  (Etale.openImmersionLowerShriekAdjunction A j).isRightAdjoint

/-- The extension by zero `j_!` along an open immersion on étale sheaves with values in a
preadditive category is additive, being left adjoint to the additive restriction `j^*`. -/
instance Etale.openImmersionLowerShriek_additive [Preadditive A] :
    (Etale.openImmersionLowerShriek A j).Additive :=
  (Etale.openImmersionLowerShriekAdjunction A j).left_adjoint_additive

/-- The extension by zero `j_!` along an open immersion on étale sheaves with values in an
abelian category is exact. This is the left exactness half; it preserves finite colimits
by `Etale.preservesFiniteColimits_openImmersionLowerShriek`, being a left adjoint. -/
instance Etale.preservesFiniteLimits_openImmersionLowerShriek [Abelian A] :
    PreservesFiniteLimits (Etale.openImmersionLowerShriek A j) :=
  sorry

/-- The extension by zero `j_!` along an open immersion preserves finite colimits, being a
left adjoint. Together with `Etale.preservesFiniteLimits_openImmersionLowerShriek` this
makes `j_!` exact. -/
instance Etale.preservesFiniteColimits_openImmersionLowerShriek :
    PreservesFiniteColimits (Etale.openImmersionLowerShriek A j) :=
  inferInstance

section UpperStar

variable [HasWeakSheafify U.smallEtaleTopology A]

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
