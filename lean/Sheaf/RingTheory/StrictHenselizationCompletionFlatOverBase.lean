/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
import Sheaf.RingTheory.IsStrictHenselization
import Mathlib.RingTheory.AdicCompletion.Algebra
import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.RingTheory.RingHom.Flat

/-!
# Flatness over the base of the completed strict henselization

Source: Stacks Project, More on Algebra, Lemma Tag 06LJ, proof of (c), paragraph
“To finish the proof of (c)”
(blueprint: lem-sc-strict-henselization-completion-flat-over-base).
-/

universe v

namespace Algebra

/-- For a Noetherian local ring `A`, the completion of its strict henselization `C` at
`nC`, where `n` is the maximal ideal of `A`, is flat over `A`.
Source: Stacks Project, Tag 06LJ, proof of (c)
(blueprint: lem-sc-strict-henselization-completion-flat-over-base).

Proof: `lem-sc-strict-henselization-mod-power-free` identifies this completion with the
`n`-adic completion of a free `A`-module `F`, using the compatible isomorphisms modulo
`n^r`. The identification respects the action of the completed base ring through its
canonical map to the completed strict henselization. Since `F` is free and hence flat,
`lem-weil-pbc-flat-module-completion-flat` makes its completion flat over the completed
base ring. The map from `A` to its completion is flat by
`lem-weil-pbc-noetherian-completion-flat`. Composition, by
`lem-weil-pbc-flat-ring-map-comp`, gives flatness of the canonical map from `A`. -/
theorem strictHenselization_completion_flat_over_base
    (A K C : Type v) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [Field K]
    [Algebra (IsLocalRing.ResidueField A) K] [IsSepClosure (IsLocalRing.ResidueField A) K]
    [Algebra A K] [IsScalarTower A (IsLocalRing.ResidueField A) K]
    [CommRing C] [Algebra A C] (hC : IsStrictHenselization A K C) :
    (algebraMap A
      (AdicCompletion ((IsLocalRing.maximalIdeal A).map (algebraMap A C)) C)).Flat := by
  sorry

end Algebra
