/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib
public import WeilConjectures.SixFunctors.UpperLowerStar.Defs

/-!

# The pushforward `g_*` and the pullback `g^*` on small étale sites

For a morphism of schemes `g : Z ⟶ Y`, the pushforward and the pullback of
`WeilConjectures.SixFunctors.UpperLowerStar.Defs` (with `P = Q = @Etale`) specialize to the
small étale sites. This file records the resulting functors
`g_* : Sheaf Z.smallEtaleTopology A ⥤ Sheaf Y.smallEtaleTopology A` and
`g^* : Sheaf Y.smallEtaleTopology A ⥤ Sheaf Z.smallEtaleTopology A`.

The site-theoretic inputs of the general definitions are discharged here:

- The base change functor `MorphismProperty.Over.pullback @Etale ⊤ g` along an *arbitrary*
  morphism `g` is continuous for the small étale topologies
  (`Etale.isContinuous_overPullback`): it preserves covers since étale covers are stable
  under base change — points are lifted through the pullback-pasting isomorphism
  `W ×_V (V ×_Y Z) ≅ W ×_Y Z` — and it preserves compatible families since it is
  representably flat, being a finite-limit-preserving functor on the finitely complete
  étale slice. Hence `Etale.lowerStar` carries no hypotheses at all.
- For `g` étale, base change is right adjoint to the localization functor
  `MorphismProperty.Over.map ⊤ ‹Etale g›`, so its opposite is a *left* adjoint and all
  pointwise left Kan extensions along it exist
  (`Etale.hasPointwiseLeftKanExtension_op_overPullback`). Hence for étale `g` only
  sheafification remains as a hypothesis of `Etale.upperStar`.

## Main definitions

- `AlgebraicGeometry.Etale.coverPreserving_overPullback` and
  `AlgebraicGeometry.Etale.isContinuous_overPullback`: base change along an arbitrary
  morphism is cover-preserving and continuous for the small étale topologies.
- `AlgebraicGeometry.Etale.hasPointwiseLeftKanExtension_op_overPullback`: along the
  opposite of base change by an étale morphism, all pointwise left Kan extensions exist.
- `AlgebraicGeometry.Etale.lowerStar`: the pushforward `g_*` on étale sheaves.
- `AlgebraicGeometry.Etale.upperStar`: the pullback `g^*` on étale sheaves.
- `AlgebraicGeometry.Etale.upperStarLowerStarAdjunction`: the adjunction `g^* ⊣ g_*`.
- `AlgebraicGeometry.Etale.preservesFiniteLimits_lowerStar`: the pushforward `g_*` with
  values in an abelian category is left exact.
- `AlgebraicGeometry.Etale.preservesFiniteLimits_upperStar` and
  `AlgebraicGeometry.Etale.preservesFiniteColimits_upperStar`: the pullback `g^*` with
  values in an abelian category is exact.

-/

@[expose] public section

universe v' u' u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

open Scheme

section Continuity

variable {Z Y : Scheme.{u}} (g : Z ⟶ Y)

/-- Base change along an arbitrary morphism `g : Z ⟶ Y` preserves covering sieves of the
small étale topologies. -/
lemma Etale.coverPreserving_overPullback :
    CoverPreserving (Y.smallGrothendieckTopology @Etale) (Z.smallGrothendieckTopology @Etale)
      (MorphismProperty.Over.pullback @Etale ⊤ g) where
  cover_preserve {V S} hS := by
    rw [smallGrothendieckTopology_eq_toGrothendieck_smallPretopology Y le_rfl] at hS
    rw [smallGrothendieckTopology_eq_toGrothendieck_smallPretopology Z le_rfl]
    replace hS := (mem_toGrothendieck_smallPretopology _ _).mp hS
    refine (mem_toGrothendieck_smallPretopology _ _).mpr fun x => ?_
    obtain ⟨W, φ, w, hSφ, hφl, hφw⟩ := hS (pullback.fst V.hom g x)
    -- The base change of `φ` is a morphism between étale `Z`-schemes, hence étale.
    have hmap : Etale ((MorphismProperty.Over.pullback @Etale ⊤ g).map φ).left := by
      refine MorphismProperty.of_postcomp (W := @Etale) (W' := @Etale) _
        ((MorphismProperty.Over.pullback @Etale ⊤ g).obj V).hom
        (MorphismProperty.Comma.prop _) ?_
      rw [MorphismProperty.Over.w ((MorphismProperty.Over.pullback @Etale ⊤ g).map φ)]
      exact MorphismProperty.Comma.prop _
    -- Lift `x` through the base change of `φ` via `W ×_V (V ×_Y Z) ≅ W ×_Y Z`.
    obtain ⟨ξ, hξ₁, hξ₂⟩ := Scheme.Pullback.exists_preimage_pullback
      (f := φ.left) (g := pullback.fst V.hom g) w x hφw
    have hcomp : (pullbackRightPullbackFstIso V.hom g φ.left ≪≫
        pullback.congrHom (MorphismProperty.Over.w φ) rfl).hom ≫
          ((MorphismProperty.Over.pullback @Etale ⊤ g).map φ).left =
        pullback.snd φ.left (pullback.fst V.hom g) := by
      apply pullback.hom_ext
      · simp [pullback.condition]
      · simp
    refine ⟨(MorphismProperty.Over.pullback @Etale ⊤ g).obj W,
      (MorphismProperty.Over.pullback @Etale ⊤ g).map φ,
      (pullbackRightPullbackFstIso V.hom g φ.left ≪≫
        pullback.congrHom (MorphismProperty.Over.w φ) rfl).hom ξ,
      ⟨W, φ, 𝟙 _, hSφ, (Category.id_comp _).symm⟩, hmap, ?_⟩
    exact ((Scheme.Hom.comp_apply _ _ _).symm.trans (by rw [hcomp]; rfl)).trans hξ₂

/-- Base change along an arbitrary morphism `g : Z ⟶ Y` is continuous for the small étale
topologies. -/
instance Etale.isContinuous_overPullback :
    (MorphismProperty.Over.pullback @Etale ⊤ g).IsContinuous
      (Y.smallGrothendieckTopology @Etale) (Z.smallGrothendieckTopology @Etale) :=
  have : RepresentablyFlat (MorphismProperty.Over.pullback @Etale ⊤ g) :=
    flat_of_preservesFiniteLimits _
  Functor.isContinuous_of_coverPreserving
    (compatiblePreservingOfFlat _ _)
    (Etale.coverPreserving_overPullback g)

end Continuity

section KanExtension

variable (A : Type u') [Category.{v'} A]
variable {Z Y : Scheme.{u}} (g : Z ⟶ Y) [Etale g]

/-- For an étale morphism `g`, base change is right adjoint to the localization functor
`MorphismProperty.Over.map ⊤ ‹Etale g›`, hence its opposite is a left adjoint and the
indexing comma categories of the pointwise left Kan extensions along it have terminal
objects. In particular all pointwise left Kan extensions along it exist. -/
instance Etale.hasPointwiseLeftKanExtension_op_overPullback (F : Y.Etaleᵒᵖ ⥤ A) :
    (MorphismProperty.Over.pullback @Etale ⊤ g).op.HasPointwiseLeftKanExtension F := by
  have : (MorphismProperty.Over.pullback @Etale ⊤ g).op.IsLeftAdjoint :=
    ((MorphismProperty.Over.mapPullbackAdj @Etale ⊤ g ‹Etale g› _root_.trivial).op).isLeftAdjoint
  intro V
  have : HasTerminal (CostructuredArrow (MorphismProperty.Over.pullback @Etale ⊤ g).op V) :=
    (mkTerminalOfRightAdjoint _
      (Adjunction.ofIsLeftAdjoint (MorphismProperty.Over.pullback @Etale ⊤ g).op) V).hasTerminal
  infer_instance

end KanExtension

section Star

variable (A : Type u') [Category.{v'} A]
variable {Z Y : Scheme.{u}} (g : Z ⟶ Y)

/-- The pushforward `g_*` along an arbitrary morphism `g : Z ⟶ Y` on sheaves for the small
étale sites, given objectwise by `(g_* G)(V → Y) = G(V ×_Y Z → Z)`. -/
noncomputable def Etale.lowerStar :
    Sheaf Z.smallEtaleTopology A ⥤ Sheaf Y.smallEtaleTopology A :=
  GrothendieckTopology.lowerStar A @Etale @Etale g

/-- The sections of `g_* G` over `V → Y` are the sections of `G` over `V ×_Y Z → Z`. -/
lemma Etale.lowerStar_obj_val_obj (G : Sheaf Z.smallEtaleTopology A) (b : Y.Etale) :
    ((Etale.lowerStar A g).obj G).obj.obj (op b) =
      G.obj.obj (op ((MorphismProperty.Over.pullback @Etale ⊤ g).obj b)) :=
  rfl

/-- `g_*` acts on morphisms by whiskering along `(MorphismProperty.Over.pullback @Etale ⊤ g).op`. -/
lemma Etale.lowerStar_map_hom_app {G G' : Sheaf Z.smallEtaleTopology A} (φ : G ⟶ G')
    (b : Y.Etale) :
    (((Etale.lowerStar A g).map φ).hom).app (op b) =
      φ.hom.app (op ((MorphismProperty.Over.pullback @Etale ⊤ g).obj b)) :=
  rfl

/-- The pushforward `g_*` on étale sheaves with values in a preadditive category is
additive: it acts on morphisms by whiskering, which is compatible with the objectwise
addition. -/
instance Etale.lowerStar_additive [Preadditive A] : (Etale.lowerStar A g).Additive where

/-- The pushforward `g_*` on étale sheaves with values in an abelian category is left
exact. -/
instance Etale.preservesFiniteLimits_lowerStar [Abelian A] :
    PreservesFiniteLimits (Etale.lowerStar A g) :=
  sorry

section Adjunction

variable [∀ F : Y.Etaleᵒᵖ ⥤ A,
  (MorphismProperty.Over.pullback @Etale ⊤ g).op.HasLeftKanExtension F]
variable [HasWeakSheafify Z.smallEtaleTopology A]

/-- The pullback `g^*` along an arbitrary morphism `g : Z ⟶ Y` on sheaves for the small
étale sites: left Kan extension on presheaves followed by sheafification. For `g` étale the
Kan extension hypothesis is automatic by
`Etale.hasPointwiseLeftKanExtension_op_overPullback`, and `g^*` is computed by restriction,
see `Etale.upperStarIsoOpenImmersionRestriction`. -/
noncomputable def Etale.upperStar :
    Sheaf Y.smallEtaleTopology A ⥤ Sheaf Z.smallEtaleTopology A :=
  have : HasWeakSheafify (Z.smallGrothendieckTopology (Q := @Etale) @Etale) A :=
    inferInstanceAs (HasWeakSheafify Z.smallEtaleTopology A)
  GrothendieckTopology.upperStar A @Etale @Etale g

/-- The adjunction `g^* ⊣ g_*` on sheaves for the small étale sites. -/
noncomputable def Etale.upperStarLowerStarAdjunction :
    Etale.upperStar A g ⊣ Etale.lowerStar A g :=
  have : HasWeakSheafify (Z.smallGrothendieckTopology (Q := @Etale) @Etale) A :=
    inferInstanceAs (HasWeakSheafify Z.smallEtaleTopology A)
  GrothendieckTopology.upperStarLowerStarAdjunction A @Etale @Etale g

instance : (Etale.lowerStar A g).IsRightAdjoint :=
  (Etale.upperStarLowerStarAdjunction A g).isRightAdjoint

instance : (Etale.upperStar A g).IsLeftAdjoint :=
  (Etale.upperStarLowerStarAdjunction A g).isLeftAdjoint

/-- The pullback `g^*` on étale sheaves with values in an abelian category is left
exact. -/
instance Etale.preservesFiniteLimits_upperStar [Abelian A] :
    PreservesFiniteLimits (Etale.upperStar A g) :=
  sorry

/-- The pullback `g^*` on étale sheaves is right exact, being a left adjoint. -/
instance Etale.preservesFiniteColimits_upperStar :
    PreservesFiniteColimits (Etale.upperStar A g) :=
  have : PreservesColimitsOfSize.{0, 0} (Etale.upperStar A g) :=
    (Etale.upperStarLowerStarAdjunction A g).leftAdjoint_preservesColimits
  PreservesColimitsOfSize.preservesFiniteColimits _

end Adjunction

end Star

end AlgebraicGeometry
