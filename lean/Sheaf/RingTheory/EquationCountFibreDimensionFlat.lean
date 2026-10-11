/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
import Mathlib.RingTheory.RingHom.Flat
import WeilConjectures.Mathlib.Topology.KrullDimension

/-!
# Flatness from the number of equations and fibre dimension

Source: Stacks Project, Algebra, Tags 00ST (3), 00SW, 00QD and 00HT
(blueprint: lem-weil-pbc-equation-count-fibre-dimension-flat).
-/

universe u

namespace MvPolynomial

/-- Stacks Project, Algebra, Tags 00ST (3), 00SW, 00QD and 00HT.
(blueprint: lem-weil-pbc-equation-count-fibre-dimension-flat)
A quotient by `c` equations in `N` variables is flat near a prime where its fibre has
local topological dimension `N - c`; both prime-localization flatness conclusions follow.

Proof: `lem-weil-pbc-fibre-dimension-neighborhood` supplies `g` outside the prime with
all nonempty fibres of dimension at most `N - c`. Lift `g` to a polynomial `h` and
present the localization by adding a variable `z` and the equation `h*z - 1`, using
`lem-weil-pbc-localization-away-universal-property`. Polynomial scalar extension and
quotient base change (`lem-weil-pbc-polynomial-scalar-extension` and
`lem-weil-pbc-tensor-quotient-base-change`) identify every fibre of this presentation.
The lower bound `lem-weil-pbc-polynomial-quotient-dimension-lower-bound` makes every
nonempty fibre have dimension exactly `N - c`, so the presentation is a relative global
complete intersection (`def-weil-pbc-relative-global-complete-intersection`). It is flat
by `lem-weil-pbc-relative-global-complete-intersection-flat`. Localizing further at the
prime uses `lem-weil-pbc-localization-of-localization` and
`lem-weil-pbc-localization-flat`; transitivity of tensoring preserves injections and
therefore gives flatness over `R`. Finally `lem-weil-pbc-flat-local-ring-maps` gives
flatness of the induced map between the two prime localizations. -/
theorem exists_flat_away_of_fibre_dimension_eq
    (R : Type u) [CommRing R] (N c : ℕ) (hc : c ≤ N)
    (equations : Fin c → MvPolynomial (Fin N) R) :
    let S := MvPolynomial (Fin N) R ⧸ Ideal.span (Set.range equations)
    ∀ q : PrimeSpectrum S,
      let p := PrimeSpectrum.comap (algebraMap R S) q
      let Q := PrimeSpectrum.preimageEquivFiber R S p ⟨q, rfl⟩
      topologicalKrullDimAt Q = ((N - c : ℕ) : WithBot ℕ∞) →
        (∃ g : S, g ∉ q.asIdeal ∧ Module.Flat R (Localization.Away g)) ∧
        Module.Flat R (Localization.AtPrime q.asIdeal) ∧
        (Localization.localRingHom p.asIdeal q.asIdeal (algebraMap R S) rfl).Flat := by
  sorry

end MvPolynomial
