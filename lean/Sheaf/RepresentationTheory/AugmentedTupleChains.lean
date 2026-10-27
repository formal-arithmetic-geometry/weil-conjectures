/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q120
-/
module

public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.LinearAlgebra.Finsupp.VectorSpace
public import Mathlib.Data.Fin.Tuple.Basic

/-! # Augmented free integer chains on ordered tuples

Source: six-functors direct-images proof, paragraph (3), agent arithmetic expansion
of homogeneous-cocycle rectangle detection, prefix-homotopy calculations 1–2.
The expansion is not asserted by the blueprint text; an exact literature reference
is WANTED (blueprint: def-sfb-augmented-tuple-chains).

The natural-number index is tuple length, hence one more than homological degree.
Length zero is the free integer module on the unique empty tuple, canonically ℤ.
Groups below homological degree −1, and maps from them, are zero and are omitted
from this nonnegative length indexing. The basis is `Finsupp.basisSingleOne`.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v

open scoped BigOperators

namespace ContinuousCohomology.AugmentedTupleChains

/-- The free integer module on ordered tuples of length `m`, repetitions allowed.
Source: prefix-homotopy calculation 1 in the agent arithmetic expansion below
blueprint direct-images paragraph (3) (blueprint: def-sfb-augmented-tuple-chains). -/
abbrev Chains (Y : Type u) (m : ℕ) := (Fin m → Y) →₀ ℤ

/-- The specified free basis, including the single empty tuple at length zero.
Source: prefix-homotopy calculation 1, using def-weil-pbc-free-module
(blueprint: def-sfb-augmented-tuple-chains). -/
def basis (Y : Type u) (m : ℕ) : Module.Basis (Fin m → Y) ℤ (Chains Y m) :=
  Finsupp.basisSingleOne

/-- Alternating deletion from length `m + 1` to length `m`; at `m = 0` this is
augmentation to the empty generator. Source: prefix-homotopy calculation 1
(blueprint: def-sfb-augmented-tuple-chains). -/
def boundary (Y : Type u) (m : ℕ) : Chains Y (m + 1) →+ Chains Y m :=
  (Finsupp.linearCombination ℤ fun x : Fin (m + 1) → Y ↦
    ∑ i : Fin (m + 1), Finsupp.single (x ∘ i.succAbove) ((-1 : ℤ) ^ i.val)).toAddMonoidHom

/-- The homomorphism induced by a map on every coordinate; at length zero it
fixes the empty generator. Source: prefix-homotopy calculation 1
(blueprint: def-sfb-augmented-tuple-chains). -/
def map {Y : Type u} {Z : Type v} (f : Y → Z) (m : ℕ) :
    Chains Y m →+ Chains Z m :=
  Finsupp.mapDomain.addMonoidHom (fun x ↦ f ∘ x)

/-- Prefix the fixed vertex `b`, including prefixing to the empty tuple.
Source: prefix-homotopy calculation 2
(blueprint: def-sfb-augmented-tuple-chains). -/
def prepend {Y : Type u} (b : Y) (m : ℕ) : Chains Y m →+ Chains Y (m + 1) :=
  Finsupp.mapDomain.addMonoidHom (fun x : Fin m → Y ↦ Fin.cons b x)

/-- Diagonal left translation, trivial on the unique empty tuple.
Source: prefix-homotopy calculations 1–2
(blueprint: def-sfb-augmented-tuple-chains). -/
def translate {Y : Type u} [Mul Y] (g : Y) (m : ℕ) : Chains Y m →+ Chains Y m :=
  map (fun y ↦ g * y) m

end ContinuousCohomology.AugmentedTupleChains
