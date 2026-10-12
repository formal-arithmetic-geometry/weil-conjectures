/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
module

public import Sheaf.RingTheory.IsStrictHenselization
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.FieldTheory.IsSepClosed
import Sheaf.RingTheory.StrictHenselizationCompletionNoetherian
import Sheaf.RingTheory.StrictHenselizationFaithfullyFlat

/-!
# Noetherianity and strict henselization

Source: Stacks Project, More on Algebra, Lemma 15.46.3 (Tag 06LJ), conditions (1) and (3)
(blueprint: lem-sc-strict-henselization-noetherian).
-/

@[expose] public section

universe u

namespace Algebra

/-- For a local commutative ring, Noetherianity is equivalent to Noetherianity of its
strict henselization relative to a chosen separable closure of its residue field.
Source: Stacks Project, More on Algebra, Lemma 15.46.3 (Tag 06LJ), conditions (1) and (3).

Proof: The map from the base ring to its strict henselization is faithfully flat, so
Noetherianity descends. Conversely, when the base is Noetherian, the completion of the
strict henselization is Noetherian and faithfully flat over it; faithfully flat descent
then gives Noetherianity of the strict henselization. These are the three proof steps
recorded in the DAG (lem-sc-strict-henselization-faithfully-flat,
lem-weil-pbc-faithfully-flat-descent-noetherian, and
lem-sc-strict-henselization-completion-noetherian).
(blueprint: lem-sc-strict-henselization-noetherian). -/
theorem isNoetherianRing_iff_isStrictHenselization
    (R K C : Type u) [CommRing R] [IsLocalRing R] [Field K]
    [Algebra (IsLocalRing.ResidueField R) K] [IsSepClosure (IsLocalRing.ResidueField R) K]
    [Algebra R K] [IsScalarTower R (IsLocalRing.ResidueField R) K]
    [CommRing C] [Algebra R C] (hC : IsStrictHenselization R K C) :
    IsNoetherianRing R ↔ IsNoetherianRing C := by
  sorry

end Algebra
