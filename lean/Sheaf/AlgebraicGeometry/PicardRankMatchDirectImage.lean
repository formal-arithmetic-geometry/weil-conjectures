/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U4
-/
module

public import Sheaf.AlgebraicGeometry.PicardUniversalSingleRankMatch
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation

/-! # Ordinary local normal forms of the reference-rank predicate

Source: Stacks Project, Tag 0BDP, first three proof paragraphs, with the empty
and mixed-fibre cases of the unrestricted chart argument.
(blueprint: lem-sc-picard-rank-match-direct-image-normal-form).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- Locally, the reference-rank predicate is either universal fixed-rank freeness
of the ordinary direct image, or the condition that the test scheme is empty.
No derived category, complex, perfectness, or Tor bound occurs in this assertion.
Source: Stacks Project, Tag 0BDP, first three proof paragraphs; the empty and
mixed-fibre adaptation in the unrestricted perfect-chart argument.
(blueprint: lem-sc-picard-rank-match-direct-image-normal-form).

Proof: Let X_r be the clopen local rank-r locus of E. Flatness and local finite
presentation make f open; properness makes f closed, so f(X_r), f(X minus X_r)
and f(X) are clopen. If the fibre at s is nonempty and has one rank r, use the
neighbourhood f(X) minus f(X minus X_r). Every fibre there is nonempty of rank r,
including after arbitrary field extension. Pullback preserves local rank. In any
local witness for the predicate, the reference rank must equal r by comparing
finranks at a point of its nonempty fibre. Fixed-rank freeness of the direct image
is local, so the witnesses give global rank-r freeness on every further test.
Conversely, restrict the globally rank-r direct image to the top open and use
the already rank-r reference bundle to supply witnesses.
If the fibre at s is empty, use S minus f(X). Every base-changed source is empty,
its modules are zero, and its direct image is zero. Use rank zero on every test;
the reference condition on the empty source is vacuous.
Otherwise choose two different local ranks a and c in the fibre and use
f(X_a) intersect f(X_c). A nonempty test has a residue-field point, and its fibre
has points of both ranks, since nonempty fibres persist under field extension.
Any reference witness over that point would have both ranks a and c, contrary
to stalk invariant basis number. Thus the predicate forces the test to be empty.
For empty tests the universal pointwise condition is vacuous. These cases exhaust
all fibres. Rank zero, empty sources, and nonreduced tests are included. -/
theorem exists_picardRankMatchDirectImageNormalForm
    {X S : Scheme.{u}} (f : X ⟶ S)
    [Flat f] [IsProper f] [LocallyOfFinitePresentation f]
    (E F : X.Modules) [E.IsFiniteLocallyFree] [F.IsFiniteLocallyFree] (s : S) :
    ∃ U : S.Opens, s ∈ U ∧
      ((∃ r : ℕ, ∀ (T : Scheme.{u}) (g : T ⟶ U.toScheme),
        PicardUniversalSingleRankMatch f E F (g ≫ U.ι) ↔
          ∀ (T' : Scheme.{u}) (h : T' ⟶ T),
            SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
              ((Modules.pushforward (pullback.snd f (h ≫ g ≫ U.ι))).obj
                ((Modules.tensorPullback (pullback.fst f (h ≫ g ≫ U.ι))).obj F)) r) ∨
      (∀ (T : Scheme.{u}) (g : T ⟶ U.toScheme),
        PicardUniversalSingleRankMatch f E F (g ≫ U.ι) ↔ IsEmpty T)) := by sorry

end AlgebraicGeometry.Scheme
