/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib
public import WeilConjectures.SixFunctors.LowerShriek.Defs
public import WeilConjectures.SixFunctors.LowerShriek.OpenImmersion.Etale

/-!

# Lower shriek on small étale sites

For a morphism `f : X ⟶ Y` admitting a compactification, the general lower shriek of
`WeilConjectures.SixFunctors.LowerShriek.Defs` (with `P = Q = @Etale`) specializes to the
small étale sites. This file records the resulting functor
`f_! : Sheaf X.smallEtaleTopology A ⥤ Sheaf Y.smallEtaleTopology A`.

All site-theoretic inputs of the general definition are discharged here:

- `@IsOpenImmersion ≤ @Etale` holds since open immersions are étale.
- The Kan extension hypothesis holds by the instance of
  `WeilConjectures.SixFunctors.LowerShriek.OpenImmersion.Etale` for a category `A` with an initial
  object.
- The base change functor `MorphismProperty.Over.pullback @Etale ⊤ g` along an *arbitrary*
  morphism `g` is continuous for the small étale topologies
  (`Etale.isContinuous_overPullback`): it preserves covers since étale covers are stable
  under base change — points are lifted through the pullback-pasting isomorphism
  `W ×_V (V ×_Y Z) ≅ W ×_Y Z` — and it preserves compatible families since it is
  representably flat, being a finite-limit-preserving functor on the finitely complete
  étale slice.

Only sheafification on the small étale sites remains as a hypothesis.

## Main definitions

- `AlgebraicGeometry.isOpenImmersion_le_etale`: open immersions are étale, as an
  inequality of morphism properties.
- `AlgebraicGeometry.Etale.coverPreserving_overPullback` and
  `AlgebraicGeometry.Etale.isContinuous_overPullback`: base change along an arbitrary
  morphism is cover-preserving and continuous for the small étale topologies.
- `AlgebraicGeometry.Etale.lowerShriek`: the lower shriek `f_!` on étale sheaves along a
  morphism admitting a compactification.

-/

@[expose] public section

universe v' u' u

open CategoryTheory Limits

namespace AlgebraicGeometry

open Scheme

/-- Open immersions are étale, as an inequality of morphism properties. -/
lemma isOpenImmersion_le_etale : @IsOpenImmersion ≤ @Etale := fun _ _ _ hi =>
  haveI : IsOpenImmersion _ := hi
  inferInstance

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
  haveI : RepresentablyFlat (MorphismProperty.Over.pullback @Etale ⊤ g) :=
    flat_of_preservesFiniteLimits _
  Functor.isContinuous_of_coverPreserving
    (compatiblePreservingOfFlat _ _)
    (Etale.coverPreserving_overPullback g)

end Continuity

section LowerShriek

variable (A : Type u') [Category.{v'} A]
variable {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]
variable [HasInitial A]
variable [∀ Z : Scheme.{u}, HasWeakSheafify Z.smallEtaleTopology A]

/-- The lower shriek `f_!` along a morphism `f : X ⟶ Y` admitting a compactification on
sheaves for the small étale sites. -/
noncomputable def Etale.lowerShriek :
    Sheaf X.smallEtaleTopology A ⥤ Sheaf Y.smallEtaleTopology A :=
  have : ∀ Z : Scheme.{u},
      HasWeakSheafify (Z.smallGrothendieckTopology (Q := @Etale) @Etale) A :=
    fun Z => inferInstanceAs (HasWeakSheafify Z.smallEtaleTopology A)
  AlgebraicGeometry.lowerShriek A @Etale @Etale f isOpenImmersion_le_etale

end LowerShriek

end AlgebraicGeometry
