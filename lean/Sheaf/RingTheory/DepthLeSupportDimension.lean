/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
module

public import Sheaf.RingTheory.Depth
public import Mathlib.RingTheory.KrullDimension.Module
public import Mathlib.RingTheory.Noetherian.Defs

/-!
# Depth is bounded by support dimension

Source: Stacks Project, Algebra, Lemma 00LK (lemma-bound-depth)
(blueprint: lem-weil-pbc-depth-le-support-dimension).
-/

@[expose] public section

universe u v

namespace IsLocalRing

/-- The depth of a nonzero finite module over a Noetherian local ring is at most
its support dimension. Source: Stacks Project, Algebra, Lemma 00LK
(blueprint: lem-weil-pbc-depth-le-support-dimension).

Proof, following the five steps of the DAG node:
1. The maximal ideal is the Jacobson radical. Nakayama
   (lem-weil-pbc-nakayama-jacobson) gives `m M ≠ M` for the nonzero finite module.
   Thus def-weil-pbc-depth expresses depth as the supremum of lengths of regular
   sequences in `m` (def-weil-pbc-regular-sequence), the relevant case of Tag 00LJ.
2. Induct on `r` to show that any nonzero finite module admitting a regular
   sequence of length `r` in `m` has support dimension at least `r`. For `r = 0`,
   its annihilator is proper and lies in `m`; its support contains `m` by
   lem-weil-pbc-finite-module-support-annihilator, giving a chain of length zero.
3. For a sequence `f₁, …, fᵣ` with `r > 0`, the finite quotient `N/f₁N` is nonzero.
   The quotient isomorphisms identify its successive quotients by `f₂, …, fᵣ`
   with those of `N`, so the tail is regular by def-weil-pbc-regular-sequence.
   Induction bounds the quotient's support dimension below by `r - 1`.
4. The first element is a nonzerodivisor in `m`. Clause (2) of
   lem-weil-pbc-support-dimension-quotient-element-equality (Tag 0B52) says that
   the quotient's support dimension plus one is that of `N`. Therefore the latter
   is at least `r`, also when the quotient's support dimension is infinite.
5. Apply this bound to every regular sequence on `M` and take their supremum
   (def-weil-pbc-depth), obtaining the required inequality. -/
theorem depth_le_supportDim {R : Type u} [CommRing R] [IsNoetherianRing R]
    [IsLocalRing R] (M : Type v) [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Nontrivial M] :
    (IsLocalRing.depth (R := R) M : WithBot ℕ∞) ≤ Module.supportDim R M := by
  sorry

end IsLocalRing
