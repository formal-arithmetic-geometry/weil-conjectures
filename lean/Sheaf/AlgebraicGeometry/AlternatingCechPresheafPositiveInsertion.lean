/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H3
-/
module

public import Sheaf.AlgebraicGeometry.CechCapPresheafLocalIso

/-! # Positive-degree signed insertion before sheafification

Source: Stacks Project, Tags 02FU and 01FM.
(blueprint: lem-pc-s3-alternating-cech-presheaf-positive-insertion).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory
namespace AlgebraicGeometry

/-- The positive insertion identity valued in intersection presheaves.
Source: Stacks Project, Tag 02FU, local insertion; Tag 01FM, increasing tuples.
(blueprint: lem-pc-s3-alternating-cech-presheaf-positive-insertion).

Proof: Write W=U i and K(P)(V)=P(V intersect W), with scalars restricted
from V. For an increasing tuple a of length q+1, define the a-coordinate
of the degree-q insertion map from P(q+1) to K(Pq) by zero if i occurs
in a. Otherwise insert i in its unique increasing position b, project
to that tuple, restrict to V intersect W intersect the intersection of a,
and multiply by (-1)^b. These opens coincide with the inserted tuple's
intersection with V; their equality provides a linear section map.
The maps commute with restriction. The finite product comparison for K
identifies these coordinate maps with a morphism to K(Pq). Use q=p for s
and q=p+1 for t. To check the equation, project to a tuple a of length p+2
and evaluate on V. If a omits i, in the face sum of the inserted tuple
the face deleting i contributes restriction of the a-coordinate to W.
Each other deletion pairs with inserting i after that deletion, with the
same restriction and opposite sign. More precisely, if the inserted index
has position b and a face deletes position j<b, the two exponents are
j+b-1 and j+b. If j is at least b, they are j+b and j+b+1. The face
omitting the inserted i has the product of two signs (-1)^b, hence sign
one. If a contains i, insertion at a is
zero, and among its faces only deleting i permits insertion; the two
signs are (-1)^b and their product is one. Thus s K(d)+d t is exactly
restriction to W in every coordinate. Product extensionality proves the
presheaf equality. This argument needs no cover condition. Empty opens
and empty tuple index sets are zero modules; if r=0 no index i exists.
There is no sheafification or extension to integer degrees in this claim. -/
theorem alternatingCechSheafPresheaf_positive_insertion
    {X : Scheme.{u}} {r : ℕ} (U : Fin r → X.Opens) (G : X.Modules) (i : Fin r)
    (p : ℕ) :
    let K := cechCapPresheafFunctor (U i)
    let P₀ := alternatingCechSheafPresheafTerms U G p
    let P₁ := alternatingCechSheafPresheafTerms U G (p + 1)
    let P₂ := alternatingCechSheafPresheafTerms U G (p + 1 + 1)
    ∃ (s : P₁ ⟶ K.obj P₀) (t : P₂ ⟶ K.obj P₁),
      (cechCapPresheafUnit (U i)).app P₁ =
        s ≫ K.map (alternatingCechSheafPresheafD U G p) +
          alternatingCechSheafPresheafD U G (p + 1) ≫ t := by sorry

end AlgebraicGeometry
