/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE
-/
module

public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.RootsOfUnity.Basic
public import Mathlib.GroupTheory.Index

/-! # Image of the intermediate power map in a root algebra

Source: Stacks Project, Tags 0EYG and 09EV, intermediate-root calculation,
expanded as a monic-basis calculation without a domain hypothesis.
(blueprint: lem-sbc-root-power-map-invariants)
-/

@[expose] public section

universe u
set_option autoImplicit false

namespace AlgebraicGeometry.Scheme

/-- The intermediate power map is injective and its image is precisely the
fixed elements. The homomorphisms are supplied as data: this theorem neither
chooses a map nor constructs an isomorphism from an existence assertion.

Source: Stacks Project, Tag 0EYG, final intermediate-field paragraph, and
Tag 09EV, cyclic intermediate-root calculation. The argument below is the
monic-basis extension of that calculation to general commutative rings.
(blueprint: lem-sbc-root-power-map-invariants)

Proof: Let r=|K| and e=[mu_n(H):K], so r*e=n by the cardinality hypothesis
and Lagrange. Both r and e are positive since n>0. The monic relations give
bases 1,t,...,t^(n-1) and 1,s,...,s^(e-1). The map sends s^j to t^(r*j).
These have distinct exponents below n, hence are linearly independent;
comparison of coefficients proves injectivity. Choose a generator zeta
of the finite cyclic group K, of order r. An endomorphism with the specified
root image acts on t^i by zeta^i*t^i, since it fixes H. If r does not divide
i, zeta^i is a nonidentity nth root, so zeta^i-1 is a unit by the separation
hypothesis. Comparing coefficients of a fixed element then forces its
coefficient at i to be zero. Conversely, r dividing i makes every element
of K act trivially on t^i, since each has rth power one. Thus exactly the
coefficients at exponents r*j with j<e survive. Such an element is the
image of the corresponding sum of coefficients times s^j, proving the
range assertion. This includes r=1 (all coefficients survive) and e=1
(only constants survive), and does not require h to be nonzero or regular. -/
theorem root_power_map_invariants
    (H : Type u) [CommRing H] (h : H) (n : ℕ) (hn : 0 < n)
    [Finite (rootsOfUnity n H)] [IsCyclic (rootsOfUnity n H)]
    (hcard : Nat.card (rootsOfUnity n H) = n)
    (hsep : ∀ ζ : rootsOfUnity n H, ζ ≠ 1 → IsUnit (((ζ : Hˣ) : H) - 1))
    (K : Subgroup (rootsOfUnity n H))
    (ρ : rootsOfUnity n H →
      (AdjoinRoot ((Polynomial.X : Polynomial H) ^ n - Polynomial.C h) →ₐ[H]
        AdjoinRoot ((Polynomial.X : Polynomial H) ^ n - Polynomial.C h)))
    (hρ : ∀ ζ, ρ ζ (AdjoinRoot.root
      ((Polynomial.X : Polynomial H) ^ n - Polynomial.C h)) =
        algebraMap H _ ((ζ : Hˣ) : H) * AdjoinRoot.root _)
    (φ : AdjoinRoot ((Polynomial.X : Polynomial H) ^ K.index - Polynomial.C h) →ₐ[H]
      AdjoinRoot ((Polynomial.X : Polynomial H) ^ n - Polynomial.C h))
    (hφ : φ (AdjoinRoot.root _) =
      AdjoinRoot.root ((Polynomial.X : Polynomial H) ^ n - Polynomial.C h) ^ Nat.card K) :
    Function.Injective φ ∧ ∀ x, (∀ ζ : K, ρ ζ.val x = x) ↔ x ∈ Set.range φ := by sorry

end AlgebraicGeometry.Scheme
