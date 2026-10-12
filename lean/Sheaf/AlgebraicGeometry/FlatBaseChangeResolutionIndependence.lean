/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R2
-/
module

public import Sheaf.AlgebraicGeometry.FlatBaseChangeMapSectionsDefs
import Sheaf.Algebra.Homology.LiftToInjectiveUniqueUpToHomotopy

/-! # FlatBaseChangeResolutionIndependence

Source: Stacks Project, Cohomology, Tags 02N7, 01FB and 01E4.
-/

@[expose] public section
universe uBC
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits Opposite
noncomputable section
namespace AlgebraicGeometry.Scheme.Modules
attribute [local instance] AlgebraicGeometry.Scheme.Modules.enoughInjectives

/-- Resolution comparison and homotopy invariance of the flat base-change morphism.
Source: Stacks, Cohomology, Tag 02N7 and Derived Categories, Tags 013P, 013S.
(blueprint: lem-weil-pbc-flat-base-change-resolution-independence).

Proof: Compare I and I₁ by lifts of the identity of F, and J and J₁ by lifts of
 the identity of g'^*F. Their composites are homotopic to identities. Pushforward
 preserves injectives because g' is flat. The two augmented maps into the pushed
 target resolution are homotopic by uniqueness of lifts. Apply f_*, the square
 isomorphism, and the termwise adjunction; these preserve homotopies. Homology
 identifies the two resulting maps. Naturality of the exact pullback homology
 comparison and of isoRightDerivedObj cancels the resolution comparisons, giving
 the asserted equality on the fixed derived objects. -/
theorem flatBaseChangeResolutionBeta_independent {X S S' : Scheme.{uBC}} (f : X ⟶ S) (g : S' ⟶ S)
    [Flat g] [Flat (pullback.snd g f)] {F : X.Modules}
    (I : InjectiveResolution F)
    (J : InjectiveResolution ((tensorPullback (pullback.snd g f)).obj F))
    (t : I.cocomplex ⟶ ((pushforward (pullback.snd g f)).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj J.cocomplex)
    (ht : I.ι.f 0 ≫ t.f 0 =
      (Classical.choose (exists_tensorPullbackAdjunction (pullback.snd g f))).unit.app F ≫
        (pushforward (pullback.snd g f)).map (J.ι.f 0))
    (I₁ : InjectiveResolution F)
    (J₁ : InjectiveResolution ((tensorPullback (pullback.snd g f)).obj F))
    (t₁ : I₁.cocomplex ⟶ ((pushforward (pullback.snd g f)).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj J₁.cocomplex)
    (ht₁ : I₁.ι.f 0 ≫ t₁.f 0 =
      (Classical.choose (exists_tensorPullbackAdjunction (pullback.snd g f))).unit.app F ≫
        (pushforward (pullback.snd g f)).map (J₁.ι.f 0))
    (p : ℕ) :
    flatBaseChangeResolutionBeta f g I J t p =
      flatBaseChangeResolutionBeta f g I₁ J₁ t₁ p := by
  sorry

end AlgebraicGeometry.Scheme.Modules
