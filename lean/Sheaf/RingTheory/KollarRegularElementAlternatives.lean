/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
module

public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Regular.RegularSequence
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic

/-!
# Kollár's alternatives after a regular element

Source: Stacks Project, Algebra, Tag 0BHZ, the two subcases following the choice of y.
-/

@[expose] public section

universe u v

namespace IsLocalRing

/-- Source: Stacks Project, Algebra, Lemma Tag 0BHZ, fourth and fifth proof paragraphs.
(blueprint: lem-weil-pbc-kollar-regular-element-alternatives).

Proof: The associated-prime hypothesis supplies a nonzero class of y modulo xR whose
annihilator is the maximal ideal. Thus y is outside xR and y m is contained in xR.
If y m is contained in x m, division by the regular element x defines an R-linear
endomorphism of the finite ideal m. The determinantal trick gives a monic polynomial
annihilating it. In R localized at x, evaluate this identity on x to see that y/x is
integral. The subalgebra R[y/x] is therefore finite. The map R to this subalgebra is
injective, not surjective (otherwise regularity of x would force y into xR), and its
cokernel is killed by m: multiplication by y/x preserves m, as do all its powers.
The image of x is regular on the subalgebra, so m cannot be an associated prime there.
This yields the extension alternative, with n = 1, lifted to Type (max u v).
Otherwise choose t in m with yt = xu for a unit u, and replace t by u inverse times t.
Then yt = x. Regularity of x implies regularity of y. For every t' in m, write yt' = xs;
cancelling y gives t' = ts, hence m = (t). The dimension is at most one by the height
theorem. It cannot be zero: in dimension zero the maximal ideal is a minimal prime,
hence associated to R, contradicting the regular element x in m. Thus the dimension
is one, and the one generator of m proves that R is regular local. -/
theorem kollar_regular_element_alternatives (R : Type u)
    [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (x : R) (hx : x ∈ maximalIdeal R) (hr : IsSMulRegular R x)
    (hquot : maximalIdeal R ∈ associatedPrimes R (QuotSMulTop x R)) :
    let extension : Prop := ∃ (S : Type (max u v)) (sRing : CommRing S),
      letI := sRing
      ∃ φ : R →+* S,
        letI := φ.toAlgebra
        Nontrivial S ∧ Module.Finite R S ∧ ¬ Function.Bijective φ ∧
          (∃ n : ℕ, 1 ≤ n ∧ (maximalIdeal R) ^ n * RingHom.ker φ = ⊥ ∧
            ∀ z ∈ Ideal.map φ ((maximalIdeal R) ^ n), z ∈ φ.range) ∧
          ¬ ∃ z : S, ∀ a : R, φ a * z = 0 ↔ a ∈ maximalIdeal R
    (IsRegularLocalRing R ∧ ringKrullDim R = 1) ∨ extension := by
  sorry

end IsLocalRing
