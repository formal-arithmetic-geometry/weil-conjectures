/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Topology.Constructible
public import Mathlib.Topology.NoetherianSpace

/-!
# Dense constructible sets contain a dense open

In a Noetherian space, a constructible set dense in an irreducible closed set `t` contains a
nonempty open subset of `t`.

The other affine-geometric facts of the blueprint subsection are in Mathlib: the spectrum of a
finitely generated algebra over a field is Noetherian (`Algebra.FiniteType.isNoetherianRing` and
`PrimeSpectrum.instNoetherianSpace`), a Noetherian space has finitely many irreducible components
(`TopologicalSpace.NoetherianSpace.finite_irreducibleComponents`), and the image of a constructible
set under a morphism of finite presentation is constructible (Chevalley,
`PrimeSpectrum.isConstructible_comap_image`).

## Main results

- `exists_isOpen_inter_subset_of_isConstructible`

## Blueprint

- `sk-i-geometry`: dense constructible sets.
-/

@[expose] public section

open Topology

/-- In a Noetherian space, a constructible set `s` dense in an irreducible closed set `t` contains
a nonempty open subset of `t`. (blueprint: `sk-i-geometry`) -/
theorem exists_isOpen_inter_subset_of_isConstructible {X : Type*} [TopologicalSpace X]
    [TopologicalSpace.NoetherianSpace X] {s t : Set X} (hs : IsConstructible s) (ht : IsClosed t)
    (hirr : IsIrreducible t) (hst : closure s = t) :
    ∃ u : Set X, IsOpen u ∧ (u ∩ t).Nonempty ∧ u ∩ t ⊆ s := by
  sorry
