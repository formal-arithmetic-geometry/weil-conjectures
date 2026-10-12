/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
module

public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.RingTheory.Ideal.Quotient.Defs
import Sheaf.RingTheory.SubsingletonH1CotangentOfCharP

/-!
# Lifting ring maps from fields of positive characteristic

Source: Stacks Project, Algebra, Tag 0320 (3), and the successive lifting argument of Tag 07K4
(blueprint: lem-weil-pbc-field-char-p-nilpotent-lifting).
-/

@[expose] public section

universe u v

namespace RingHom

/-- Ring maps from a field of characteristic `p > 0` lift along nilpotent ideals of rings
annihilated by `p`.

Source: Stacks Project, Algebra, Tag 0320 (3), with the induction of Tag 07K4
(blueprint: lem-weil-pbc-field-char-p-nilpotent-lifting).

Proof:
1. The prime subfield of `K` is `F_p`. Rings annihilated by `p` have a unique `F_p`-algebra
   structure, and all the ring maps in question are automatically `F_p`-algebra maps.
2. The node `lem-weil-pbc-field-char-p-h1-cotangent-vanishing` gives vanishing of the first
   cotangent homology of `K/F_p`. Its differentials form a vector space, hence are projective
   by `lem-weil-pbc-vector-space-projective`. The node
   `lem-weil-pbc-smooth-ring-map-square-zero-lifting` therefore gives lifting along every
   square-zero ideal. This is formal smoothness in Tag 0320 (3), via Tags 031Z and 031J.
3. Starting with `g` into `D/J`, lift successively into `D/J^i` for `1 ≤ i ≤ N`. The kernel
   of `D/J^(i+1) → D/J^i` is `J^i/J^(i+1)` and is square-zero since `2*i ≥ i+1`.
   Each lift still reduces to `g`; at `i = N`, the equality `J^N = 0` identifies the target
   with `D`. This also covers `N = 1`, when `J = 0`. -/
theorem exists_lift_of_field_charP (K : Type u) (D : Type v) [Field K] [CommRing D]
    (p : ℕ) [CharP K p] (hp : 0 < p) (hD : (p : D) = 0)
    (J : Ideal D) (N : ℕ) (hN : 1 ≤ N) (hJ : J ^ N = ⊥) (g : K →+* D ⧸ J) :
    ∃ f : K →+* D, (Ideal.Quotient.mk J).comp f = g := by
  sorry

end RingHom
