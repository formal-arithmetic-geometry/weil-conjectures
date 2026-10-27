/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q120
-/
module

public import Sheaf.RepresentationTheory.AugmentedTupleChains

/-! # The homogeneous-tuple prefix comparison homotopy

Source: six-functors direct-images proof, paragraph (3), agent arithmetic expansion
below local continuous-cocycle descent, extracted rectangle-detection steps 5–7.
This calculation is not asserted by the blueprint text; the exact literature
reference is WANTED (blueprint: lem-sfb-homogeneous-tuple-prefix-homotopy).

Chains are indexed by length, so length `m` means homological degree `m - 1`.
The comparison maps exist only at lengths `0, …, n + 1`. The recursive homotopy
is extended by zero outside these lengths solely to make its recursion total.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open scoped BigOperators

namespace ContinuousCohomology.AugmentedTupleChains

/-- A fixed finite integer formula whose coordinates are input coordinates,
optionally right-multiplied by one of the fixed `a i`. All labels and coefficients
are quantified before the input; repetitions are retained in the sum.
Source: prefix-homotopy hypothesis and calculations 8–9 in the agent arithmetic
expansion below blueprint direct-images paragraph (3)
(blueprint: lem-sfb-homogeneous-tuple-prefix-homotopy). -/
def HasCoordinateFormula {G : Type u} [Group G] (H : Subgroup G) {n : ℕ}
    (a : Fin (n + 1) → G) (m k : ℕ) (f : Chains H m →+ Chains G k) : Prop :=
  ∃ (r : ℕ) (c : Fin r → ℤ) (j : Fin r → Fin k → Fin m)
    (t : Fin r → Fin k → Option (Fin (n + 1))),
    ∀ x : Fin m → H,
      f (Finsupp.single x 1) = ∑ l : Fin r,
        Finsupp.single (fun s ↦ match t l s with
          | none => (x (j l s) : G)
          | some i => (x (j l s) : G) * a i) (c l)

/-- The prescribed prefix recursion, extended additively on each specified basis.
Length zero is `Q_{-1} = 0`. The `if` branch beyond length `n + 1` is unused.
At length `m + 1`, subtract the given comparison and the previous homotopy of the
deletion boundary from inclusion, then prefix the first coordinate of the input.
Source: prefix-homotopy recursion and calculations 3–6 in the agent arithmetic
expansion below blueprint direct-images paragraph (3)
(blueprint: lem-sfb-homogeneous-tuple-prefix-homotopy). -/
def prefixHomotopy {G : Type u} [Group G] (H : Subgroup G) (n : ℕ)
    (A : (m : Fin (n + 2)) → Chains H m.val →+ Chains G m.val) :
    (m : ℕ) → Chains H m →+ Chains G (m + 1)
  | 0 => 0
  | m + 1 =>
    if hm : m + 1 < n + 2 then
      (Finsupp.linearCombination ℤ fun x : Fin (m + 1) → H ↦
        prepend (x 0 : G) (m + 1)
          (map H.subtype (m + 1) (Finsupp.single x 1) -
            A ⟨m + 1, hm⟩ (Finsupp.single x 1) -
            prefixHomotopy H n A m (boundary H m (Finsupp.single x 1)))).toAddMonoidHom
    else 0

/-- The basis defect `Z_q(x)`, prior to prefixing. Source: prefix-homotopy recursion,
calculations 3–6 in the agent arithmetic expansion below blueprint direct-images
paragraph (3) (blueprint: lem-sfb-homogeneous-tuple-prefix-homotopy). -/
def prefixDefect {G : Type u} [Group G] (H : Subgroup G) (n : ℕ)
    (A : (m : Fin (n + 2)) → Chains H m.val →+ Chains G m.val)
    (q : Fin (n + 1)) (x : Fin (q.val + 1) → H) : Chains G (q.val + 1) :=
  map H.subtype (q.val + 1) (Finsupp.single x 1) -
    A ⟨q.val + 1, Nat.succ_lt_succ q.isLt⟩ (Finsupp.single x 1) -
    prefixHomotopy H n A q.val (boundary H q.val (Finsupp.single x 1))

/-- The prescribed homotopy has cycle defects, the comparison identity,
H-equivariance, and fixed finite coordinate formulas. Prefixing contracts the
augmented deletion boundary and is natural for the moving translated prefix.

Source: prefix-homotopy calculations 1–9 in the agent arithmetic expansion below
blueprint direct-images paragraph (3), extracted rectangle-detection steps 5–7;
not a claim asserted in the blueprint itself; exact literature reference WANTED
(blueprint: lem-sfb-homogeneous-tuple-prefix-homotopy).

Proof:
1. Use the specified free bases (def-weil-pbc-free-module). An assignment on
   tuples extends by finite integer sums. Double deletion cancels in the two
   orders: positions i < j give signs (-1)^(i+j-1) and (-1)^(i+j). In length two,
   the next augmentation is 1-1; the empty boundary is zero. Deletion commutes
   with inclusion and diagonal translation.
2. Expanding d[b,y] gives [y]-C_b d[y]. For a singleton the subtracted term is
   [b]; for the empty tuple, d[b] is the empty generator. Additivity proves the
   contraction identities at every length. Translation sends [b,y] to [gb,gy],
   proving the moving-prefix equivariance identity, also on the empty tuple.
3. Put D=I-A. Then D in length zero is zero and dD=Dd. Induct on degree q to
   prove that the basis defect is a cycle and D_q=dQ_q+Q_{q-1}d. Extend basis
   identities by finite sums to identities on every chain.
4. At q=0 the previous Q is zero and dZ_0=D_{-1}d=0. The contraction identity
   gives dQ_0=dC_{h_0}Z_0=Z_0=D_0 on basis elements.
5. For q>=1 the preceding homotopy identity gives
   dZ_q=D_{q-1}d-dQ_{q-1}d=Q_{q-2}d²=0. For q=1 the final term uses Q_{-1}=0;
   no homotopy below augmented degree is required.
6. Contract the resulting cycle: dQ_q=dC_{h_0}Z_q=Z_q=D_q-Q_{q-1}d.
   This finishes induction through n without requiring A_{n+1}.
7. Induct separately for equivariance, starting with zero Q_{-1}. Equivariance
   of I,A,d and the preceding Q gives Z_q(gx)=gZ_q(x). The first coordinate
   changes from h_0 to gh_0, so C_{gh_0}(gZ_q(x))=gC_{h_0}Z_q(x). Extend
   additively from basis elements.
8. A coordinate label is (j,none) for h_j or (j,some i) for h_j a_i. In degree
   zero the Q list is [h_0,h_0] with coefficient 1 followed by the given A_0
   words prefixed by h_0 and with negated coefficients. These are fixed lists.
9. For degree q>=1, on deletion at s substitute the order-preserving injection
   omitting s in every preceding input label j. Concatenate inclusion, the
   negated A_q list, and these substituted Q_{q-1} lists with signs -(-1)^s.
   Prefix label (0,none) to obtain Q_q. The lists remain finite and fixed,
   with q+2 output coordinates of the required forms. No equal evaluated
   tuples need to be collected, so coincident coordinates and zero terms cause
   no input-dependent choices.
-/
theorem homogeneousTuplePrefixHomotopy
    {G : Type u} [Group G] (H : Subgroup G) (n : ℕ) (a : Fin (n + 1) → G)
    (A : (m : Fin (n + 2)) → Chains H m.val →+ Chains G m.val)
    (haug : A 0 = map H.subtype 0)
    (hchain : ∀ (q : Fin (n + 1)) (z : Chains H (q.val + 1)),
      boundary G q.val (A ⟨q.val + 1, Nat.succ_lt_succ q.isLt⟩ z) =
        A ⟨q.val, Nat.lt_succ_of_lt q.isLt⟩ (boundary H q.val z))
    (hequiv : ∀ (m : Fin (n + 2)) (g : H) (z : Chains H m.val),
      A m (translate g m.val z) = translate (g : G) m.val (A m z))
    (hformula : ∀ q : Fin (n + 1),
      HasCoordinateFormula H a (q.val + 1) (q.val + 1) (A ⟨q.val + 1, Nat.succ_lt_succ q.isLt⟩)) :
    (∀ (b : G) (z : Chains G 0), boundary G 0 (prepend b 0 z) = z) ∧
    (∀ (m : ℕ) (b : G) (z : Chains G (m + 1)),
      boundary G (m + 1) (prepend b (m + 1) z) +
        prepend b m (boundary G m z) = z) ∧
    (∀ (m : ℕ) (g : H) (b : G) (z : Chains G m),
      translate (g : G) (m + 1) (prepend b m z) =
        prepend ((g : G) * b) m (translate (g : G) m z)) ∧
    (∀ (q : Fin (n + 1)) (x : Fin (q.val + 1) → H),
      boundary G q.val (prefixDefect H n A q x) = 0) ∧
    (∀ (q : Fin (n + 1)) (z : Chains H (q.val + 1)),
      map H.subtype (q.val + 1) z - A ⟨q.val + 1, Nat.succ_lt_succ q.isLt⟩ z =
        boundary G (q.val + 1) (prefixHomotopy H n A (q.val + 1) z) +
          prefixHomotopy H n A q.val (boundary H q.val z)) ∧
    (∀ (m : Fin (n + 2)) (g : H) (z : Chains H m.val),
      prefixHomotopy H n A m.val (translate g m.val z) =
        translate (g : G) (m.val + 1) (prefixHomotopy H n A m.val z)) ∧
    (∀ q : Fin (n + 1),
      HasCoordinateFormula H a (q.val + 1) (q.val + 2)
        (prefixHomotopy H n A (q.val + 1))) := by
  sorry

end ContinuousCohomology.AugmentedTupleChains
