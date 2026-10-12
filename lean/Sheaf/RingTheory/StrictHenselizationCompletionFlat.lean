/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q1
-/
module

public import Sheaf.RingTheory.IsStrictHenselization
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.RingHom.Flat
import Sheaf.RingTheory.EtaleTripleToStrictHenselizationCompletionFlat
import Sheaf.RingTheory.FlatColimitRings
import Sheaf.RingTheory.StrictHenselizationTriples

/-!
# Flatness of the completion of a strict henselization

Source: Stacks Project, More on Algebra, Lemma Tag 06LJ, proof of (c),
paragraph beginning “To finish the proof of (c)”
(blueprint: lem-sc-strict-henselization-completion-flat).
-/

@[expose] public section

universe v

namespace Algebra

/-- The maximal-ideal completion of a strict henselization is flat over the
strict henselization.
Source: Stacks Project, More on Algebra, Lemma Tag 06LJ, proof of (c)
(blueprint: lem-sc-strict-henselization-completion-flat).

Proof: Write the strict henselization as the filtered colimit of pointed étale
algebras from `lem-weil-pbc-strict-henselization-triples`. For each pointed
étale algebra, the map to the completed strict henselization is flat by the
per-triple completion-flatness assertion
`lem-sc-etale-triple-to-sh-completion-flat`. The composite maps are therefore
flat, and the filtered-colimit flatness lemma
`lem-weil-pbc-colimit-rings-flat` gives flatness of the canonical map from the
strict henselization to its completion. -/
theorem strictHenselization_completion_flat
    (R K C : Type v) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [Field K] [Algebra (IsLocalRing.ResidueField R) K]
    [IsSepClosure (IsLocalRing.ResidueField R) K] [Algebra R K]
    [IsScalarTower R (IsLocalRing.ResidueField R) K] [CommRing C]
    [Algebra R C] (hC : IsStrictHenselization R K C) :
    (algebraMap C
      (AdicCompletion ((IsLocalRing.maximalIdeal R).map (algebraMap R C)) C)).Flat := by
  sorry

end Algebra
