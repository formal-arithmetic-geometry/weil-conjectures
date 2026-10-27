/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B4
-/
module

public import Sheaf.Paper.ConstantCompletionDerivedPull

/-! # Ordinary finite transport for constant-completion pullback

Source: Stacks Project, sites-modules.tex, Tags 03EK, 03EL, 093M;
sites-cohomology.tex, Tag 06YY.
(blueprint: lem-weil-pbc-constant-completion-ordinary-reduced-pull-transport).
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.ConstantCompletion

namespace CategoryTheory.ConstantCompletion

variable {C C' : Type u} [SmallCategory C] [SmallCategory C']
variable {J : GrothendieckTopology C} {J' : GrothendieckTopology C'}
variable {L : Sheaf J (Type u) ⥤ Sheaf J' (Type u)} (F : InverseImageData L)
variable (V : Sheaf J' (Type u) ⥤ Sheaf J (Type u)) (adj : L ⊣ V)
variable [PreservesFiniteLimits L]

/-- Both finite reductions of the ordinary scalar comparison are transported to one
ordinary finite-module functor, and the comparison is the map induced by that transport.
The transport is assembled from the sectionwise quotient identifications, the normalized
finite pullback comparison, and the coefficient-map projection equation; on pure tensors
all three maps send `1 ⊗ m` to the same class.  This is the ordinary (underived) part of
the common-quotient insertion argument.
Proof: identify both finite-reduced sides with the same finite-module functor using the
sectionwise adic quotient and normalized pullback isomorphisms.  The projection equation
for the coefficient map makes these identifications natural, and the defining insertion
equation for `ordinaryPullComparison` gives the displayed equality.
Source: Stacks Project, sites-modules.tex, Tags 03EK, 03EL, 093M;
sites-cohomology.tex, Tag 06YY.
(blueprint: lem-weil-pbc-constant-completion-ordinary-reduced-pull-transport).
-/
theorem ordinaryReducedPull_transport (A : Type u) [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) (n : ℕ) :
    ∃ (X : Mod (completed J A I) ⥤ Mod (finite J' A I n))
      (s : (res (coefficientMap J A I) ⋙ pull F (constantMap F A) ⋙
        change (quotient J' A I n)) ≅ X)
      (t : (pull F (completedMap F A I) ⋙ res (coefficientMap J' A I) ⋙
        change (quotient J' A I n)) ≅ X),
      Functor.whiskerRight (ordinaryPullComparison F A I)
          (change (quotient J' A I n)) ≫ t.hom = s.hom := by
  sorry

end CategoryTheory.ConstantCompletion
