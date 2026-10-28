/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.ConstantCompletionOrdinaryReducedPullTargetIso

/-! # Normalized ordinary reduced transport equation

This records the normalized comparison equation after both transports have been
constructed.
(blueprint: lem-weil-pbc-constant-completion-ordinary-reduced-pull-transport-equation).
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

/- STATEMENT-DISPUTED: The quantified isomorphisms are arbitrary; postcomposing `t`
with a nontrivial natural automorphism changes the right-hand side while leaving all
hypotheses true. -/

/- The reduced ordinary comparison agrees with the two normalized transports.
Source: Stacks Project, sites-modules.tex, Tags 03EK, 03EL and 093M;
sites-cohomology.tex, Tag 06YY.
Proof: evaluate the three maps on the quotient unit, where all insertion maps send
`1 ⊗ m` to the same class, then use the scalar-extension adjunction to extend this
equality to every object and cancel the coefficient identifications.
(blueprint: lem-weil-pbc-constant-completion-ordinary-reduced-pull-transport-equation).
-/
theorem ordinaryReducedPull_transport_eq (A : Type u) [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) (n : ℕ)
    (s : (res (coefficientMap J A I) ⋙ pull F (constantMap F A) ⋙
      change (quotient J' A I n)) ≅
      (change (projection J A I n) ⋙
        pull F (constantMap F (A ⧸ I ^ (n + 1)))))
    (t : (pull F (completedMap F A I) ⋙ res (coefficientMap J' A I) ⋙
      change (quotient J' A I n)) ≅
      (change (projection J A I n) ⋙
        pull F (constantMap F (A ⧸ I ^ (n + 1))))) :
    Functor.whiskerRight (ordinaryPullComparison F A I)
        (change (quotient J' A I n)) ≫ t.hom = s.hom := by
  sorry

end CategoryTheory.ConstantCompletion
