/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib
public import WeilConjectures.Mathlib.CategoryTheory.Functor.KanExtension.Preserves
public import WeilConjectures.Mathlib.CategoryTheory.MorphismProperty.OverAdjunction
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
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

- `AlgebraicGeometry.Scheme.Etale.LiftIndex`: the type of factorizations of the structure
  morphism of `V : X.Etale` through `j`, together with
  `AlgebraicGeometry.Scheme.Etale.LiftIndex.toEtale`, the induced étale `U`-scheme, and
  `AlgebraicGeometry.Scheme.Etale.LiftIndex.isoComp`, which identifies `V` with its image
  under the localization functor.
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

## Main results

- `AlgebraicGeometry.essImage_or_isEmpty_costructuredArrow`: every étale `X`-scheme either
  lies in the essential image of the localization functor along an étale monomorphism `j`,
  or has empty indexing comma category.
- `AlgebraicGeometry.preservesFiniteLimits_lan_of_etale_and_mono`: consequently the
  presheaf-level lower shriek along an étale monomorphism is left exact.

-/

@[expose] public section

universe u' u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

namespace Scheme

section LiftIndex

variable {U X : Scheme.{u}} (j : U ⟶ X) [Etale j] (V : X.Etale)

/-- The type of lifts of `V : X.Etale` through `j : U ⟶ X`: factorizations of the
structure morphism of `V` through `j`. It indexes the colimit computing the presheaf-level
lower shriek at `V`. -/
def Etale.LiftIndex : Type u :=
  {α : V.left ⟶ U // α ≫ j = V.hom}

namespace Etale.LiftIndex

variable {j V}

/-- The lift of an étale `X`-scheme through an étale morphism is étale. -/
lemma etale_val (α : Etale.LiftIndex j V) : Etale α.1 := by
  have h : Etale (α.1 ≫ j) := by
    rw [α.2]
    infer_instance
  exact Etale.of_comp α.1 j

/-- The étale `U`-scheme determined by a lift of `V : X.Etale` through `j`. -/
def toEtale (α : Etale.LiftIndex j V) : U.Etale :=
  have := α.etale_val
  Etale.mk α.1

/-- The comparison morphism from `V` to the image of `α.toEtale` in `X.Etale`; its
underlying morphism is the identity. -/
def homToComp (α : Etale.LiftIndex j V) :
    V ⟶ (MorphismProperty.Over.map ⊤ ‹Etale j›).obj α.toEtale :=
  MorphismProperty.Over.homMk (𝟙 V.left) ((Category.id_comp _).trans α.2)

/-- A lift of `V` through `j` identifies `V` with the image of an étale `U`-scheme under the
localization functor: the comparison morphism `Etale.LiftIndex.homToComp` is the identity on
underlying schemes. -/
def isoComp (α : Etale.LiftIndex j V) :
    V ≅ (MorphismProperty.Over.map ⊤ ‹Etale j›).obj α.toEtale where
  hom := α.homToComp
  inv := MorphismProperty.Over.homMk (𝟙 V.left) ((Category.id_comp _).trans α.2.symm)
  hom_inv_id := by
    apply MorphismProperty.Over.Hom.ext
    exact Category.id_comp _
  inv_hom_id := by
    apply MorphismProperty.Over.Hom.ext
    exact Category.id_comp _

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

variable (A : Type u') [Category.{u} A] [Abelian A]
  {FA : A → A → Type*} {CD : A → Type u}
  [∀ X Y, FunLike (FA X Y) (CD X) (CD Y)] [ConcreteCategory.{u} A FA]
  [PreservesLimits (CategoryTheory.forget A)]
  [(CategoryTheory.forget A).ReflectsIsomorphisms]
  [PreservesFilteredColimitsOfSize.{u, u} (CategoryTheory.forget A)]
  [IsGrothendieckAbelian.{u} A]
variable {U X : Scheme.{u}} (j : U ⟶ X) [Etale j]

open Scheme in
/-- Along the localization functor induced by an étale monomorphism `j`, all pointwise
left Kan extensions with values in a category with an initial object exist: the indexing
comma categories are either empty or admit a terminal object. -/
instance hasPointwiseLeftKanExtension_of_etale_and_mono
    [Mono j] (F : U.Etaleᵒᵖ ⥤ A) :
    (MorphismProperty.Over.map ⊤ ‹Etale j›).op.HasPointwiseLeftKanExtension F := by
  intro V
  by_cases h : Nonempty (Etale.LiftIndex j V.unop)
  · obtain ⟨α⟩ := h
    have : HasTerminal (CostructuredArrow (MorphismProperty.Over.map ⊤ ‹Etale j›).op V) :=
      α.isTerminalCostructuredArrow.hasTerminal
    infer_instance
  · have : IsEmpty (CostructuredArrow (MorphismProperty.Over.map ⊤ ‹Etale j›).op V) :=
      Etale.LiftIndex.isEmpty_costructuredArrow j V.unop (not_nonempty_iff.mp h)
    have : HasColimitsOfShape
        (CostructuredArrow (MorphismProperty.Over.map ⊤ ‹Etale j›).op V) A :=
      hasColimitsOfShape_of_equivalence (equivalenceOfIsEmpty (Discrete PEmpty.{1}) _)
    infer_instance

open Scheme in
/-- Every étale `X`-scheme either lies in the essential image of the localization functor
along an étale monomorphism `j`, or has empty indexing comma category. This is the
dichotomy underlying the left exactness of the presheaf-level lower shriek. -/
lemma essImage_or_isEmpty_costructuredArrow [Mono j] (V : X.Etaleᵒᵖ) :
    (∃ W : U.Etaleᵒᵖ,
        Nonempty ((MorphismProperty.Over.map ⊤ ‹Etale j›).op.obj W ≅ V)) ∨
      IsEmpty (CostructuredArrow (MorphismProperty.Over.map ⊤ ‹Etale j›).op V) := by
  by_cases h : Nonempty (Etale.LiftIndex j V.unop)
  · obtain ⟨α⟩ := h
    exact Or.inl ⟨op α.toEtale, ⟨α.isoComp.op⟩⟩
  · exact Or.inr
      (Etale.LiftIndex.isEmpty_costructuredArrow j V.unop (not_nonempty_iff.mp h))

/-- The presheaf-level lower shriek along an étale monomorphism is left exact: the pointwise
left Kan extension is either an evaluation or a zero object. -/
instance preservesFiniteLimits_lan_of_etale_and_mono [Mono j] :
    PreservesFiniteLimits
      ((MorphismProperty.Over.map ⊤ ‹Etale j›).op.lan : (U.Etaleᵒᵖ ⥤ A) ⥤ X.Etaleᵒᵖ ⥤ A) :=
  Functor.preservesFiniteLimits_lan_of_essImage_or_isEmpty _
    (essImage_or_isEmpty_costructuredArrow j)

end KanExtension

section LowerShriek

variable (A : Type u') [Category.{u} A] [Abelian A]
  {FA : A → A → Type*} {CD : A → Type u}
  [∀ X Y, FunLike (FA X Y) (CD X) (CD Y)] [ConcreteCategory.{u} A FA]
  [PreservesLimits (CategoryTheory.forget A)]
  [(CategoryTheory.forget A).ReflectsIsomorphisms]
  [PreservesFilteredColimitsOfSize.{u, u} (CategoryTheory.forget A)]
  [IsGrothendieckAbelian.{u} A]
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- The restriction `j^*` along an open immersion `j : U ⟶ X` on sheaves for the small
étale sites, given objectwise by `(j^* G)(T → U) = G(T → U → X)`. In contrast to
`Etale.upperStar` it requires neither Kan extensions nor sheafification. -/
def Etale.openImmersionRestriction :
    Sheaf X.smallEtaleTopology A ⥤ Sheaf U.smallEtaleTopology A :=
  GrothendieckTopology.localizationRestriction A @Etale @Etale j inferInstance

omit [Abelian A] [IsGrothendieckAbelian.{u} A] in
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
  GrothendieckTopology.localizationLowerShriekAdjunction A @Etale @Etale j inferInstance

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
are left exact: the first by
`AlgebraicGeometry.preservesFiniteLimits_lan_of_etale_and_mono`, the second by the left
exactness of sheafification, which is the content of `HasSheafify` beyond the
`HasWeakSheafify` needed to define `j_!`; both are provided for the concrete Grothendieck
abelian coefficient category `A` by Mathlib
(`Mathlib/AlgebraicGeometry/Sites/AffineEtale.lean`). -/
instance Etale.preservesFiniteLimits_openImmersionLowerShriek :
    PreservesFiniteLimits (Etale.openImmersionLowerShriek A j) := by
  have heq : Etale.openImmersionLowerShriek A j =
      sheafToPresheaf U.smallEtaleTopology A ⋙
        localizationLowerShriekPresheaf A @Etale j inferInstance ⋙
          presheafToSheaf X.smallEtaleTopology A :=
    rfl
  have hlan : PreservesFiniteLimits (localizationLowerShriekPresheaf A @Etale j inferInstance) :=
    preservesFiniteLimits_lan_of_etale_and_mono A j
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
