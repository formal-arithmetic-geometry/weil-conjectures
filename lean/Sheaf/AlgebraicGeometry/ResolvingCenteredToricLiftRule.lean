/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V3
-/
module

public import Sheaf.AlgebraicGeometry.MonoschemeTowerComparisonCoherence

/-!
# Resolving centered lifts of one rational toric rule

Source: ILO, Travaux de Gabber, Exposé VIII, construction 3.2.19, p.106
(blueprint: lem-trf-resolving-centered-toric-lift-rule).
-/

@[expose] public section

universe u

namespace AlgebraicGeometry.Monoscheme.TowerComparison

/-- One rational scheme rule admits unique centered saturated monoscheme lifts whose
last objects are smooth. No comparisons of monoscheme towers are asserted here.

Source: ILO, Exposé VIII, construction 3.2.19, first half, and Theorem 3.2.20, p.106
(blueprint: lem-trf-resolving-centered-toric-lift-rule).

Proof: Fix the normalized toric desingularization rule of
`lem-trf-toric-normalized-desingularization`, simultaneously on every fine torsion-free
monoscheme and its finite disjoint unions. Forget its extra torus-action and terminal
regularity fields to obtain `SchemeRule`; the normalized towers and comparisons are
unchanged, so its identity and composition equations are the original ones.
For each input apply `lem-trf-monoscheme-toric-tower-descent` to this assigned tower.
The rule supplies coherent invariant centers with nowhere-dense zero schemes. The
canonical centered lift has the same ordered stages, fine torsion-free intermediate
objects, and finite affine covers. Its canonical chart identifications give `Lift`.
To compare with any other `Lift`, start with the pinned base identification and
induct on the stages. The injective monoid-ideal comparison identifies the centers
under the preceding realization-preserving local isomorphism. The fraction-chart
substitutions for the same saturated blowup then give unique local maps in both
directions; their composites are identities because they fix the preceding level
and every chart fraction. The normalized blowup uniqueness over its base identifies
their realizations with the prescribed scheme isomorphisms. This constructs `LiftIso`;
the same induction makes it a subsingleton, giving `LiftRule.unique`. Transporting the
original invariant centers through these canonical toric charts gives
`LiftRule.invariant`. Finally the toric rule has regular terminal scheme; the last
clause of the tower-descent theorem gives the displayed terminal smoothness. The empty input
and zero-length towers cause no
exception. Whole-ideal stages giving nonidentity saturation are retained throughout;
no contraction or compatibility of monoscheme comparisons is used in this argument. -/
theorem exists_resolvingLiftRule :
    ∃ F : SchemeRule.{u}, ∃ T : LiftRule F,
      ∀ M : Input.{u},
        ((T.lift M).tower.level (Fin.last (F.tower M).length)).IsSmooth := by
  sorry

end AlgebraicGeometry.Monoscheme.TowerComparison
