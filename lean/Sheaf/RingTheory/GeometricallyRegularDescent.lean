/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
module

public import Sheaf.RingTheory.GRing
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Sheaf.RingTheory.RegularRingFaithfullyFlatDescent

/-!
# Geometric regularity descends along faithfully flat algebra maps

Source: Stacks Project, Algebra, Lemma Tag 07NH
(blueprint: lem-weil-pbc-geometrically-regular-descent).
-/

@[expose] public section

universe u v w

namespace Algebra

/-- Geometric regularity descends along a faithfully flat map of algebras over a field: the
`k`-algebra map `A → B` is `algebraMap A B`, compatible with `k` by `IsScalarTower k A B`.
Source: Stacks Project, Algebra, Lemma Tag 07NH
(blueprint: lem-weil-pbc-geometrically-regular-descent).

Proof: assume `B` is geometrically regular and fix a finite purely inseparable extension
`k'/k`, as in `def-weil-pbc-finite-purely-inseparable-extension`. The map from
`A ⊗[k] k'` to `B ⊗[k] k'` is faithfully flat by the faithfully-flat base-change lemma.
Geometric regularity of `B` makes `B ⊗[k] k'` regular by `def-weil-pbc-g-ring` and
`def-weil-regular-scheme`. Regularity descends along this faithfully flat map by
`lem-weil-pbc-regular-ring-faithfully-flat-descent`, so `A ⊗[k] k'` is regular. Since
`k'/k` was arbitrary, `def-weil-pbc-g-ring` gives geometric regularity of `A`. -/
theorem isGeometricallyRegular_of_faithfullyFlat
    (k : Type u) (A : Type v) (B : Type w) [Field k] [CommRing A] [CommRing B]
    [Algebra k A] [Algebra k B] [Algebra A B] [IsScalarTower k A B]
    [Module.FaithfullyFlat A B] (hB : IsGeometricallyRegular k B) :
    IsGeometricallyRegular k A := by
  sorry

end Algebra
