/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.Depth
public import Mathlib.RingTheory.KrullDimension.Module
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Regular.IsSMulRegular
import WeilConjectures.RingTheory.DepthLeSupportDimension
import WeilConjectures.RingTheory.IsSMulRegularOfGoodSequence
import WeilConjectures.RingTheory.CmModuleGoodElementSetup

/-!
# A dimension-cutting element on a Cohen–Macaulay module

An element cutting the support dimension of a nonzero finite Cohen–Macaulay module by one is a
nonzerodivisor on it, and the quotient is again Cohen–Macaulay.

## Implementation details

Dimension drops are written as successor equalities to avoid truncated subtraction at zero.
The proof is by induction on the dimension `d`. For `d ≥ 2`, prime avoidance gives an element
`h` of the maximal ideal avoiding the minimal primes of the relevant supports; then `h` is good
for a maximal regular sequence, induction applies to `g` on `M/hM`, and the regular sequence
`(h, g)` is permuted to show that `g` is regular on `M`. Prepending `h` to a regular sequence
on `M/(g,h)M` bounds the depth of `M/gM` from below.

## References

* [Stacks, Tag 00N5] (Algebra, Lemma 10.103.3)
* [Stacks, Tag 00N3] (Algebra, Definition 10.103.1)
-/

@[expose] public section

universe u v

namespace Module

/-- On a nonzero finite Cohen–Macaulay module over a Noetherian local ring, an element of the
maximal ideal that cuts the support dimension by one is a nonzerodivisor (`IsSMulRegular`), and
the quotient is Cohen–Macaulay of depth one less. Cohen–Macaulayness is written as the equality
of depth and support dimension; dimension drops are written as successor equalities. -/
theorem cm_module_good_element_nonzerodivisor
    {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M] [Nontrivial M]
    (hCM : (IsLocalRing.depth (R := R) M : WithBot ℕ∞) = supportDim R M)
    (g : R) (hg : g ∈ IsLocalRing.maximalIdeal R)
    (hdim : Order.krullDim (support R M ∩ PrimeSpectrum.zeroLocus ({g} : Set R) :
      Set (PrimeSpectrum R)) + 1 =
      supportDim R M) :
    IsSMulRegular M g ∧
      (IsLocalRing.depth (R := R) (QuotSMulTop g M) : WithBot ℕ∞) =
        supportDim R (QuotSMulTop g M) ∧
      IsLocalRing.depth (R := R) (QuotSMulTop g M) + 1 = IsLocalRing.depth (R := R) M :=
  by
    exact (exists_good_sequence_for_cm_element M hCM g hg hdim).elim (fun d hd =>
    hd.2.2.elim (fun fs hfs =>
      let T := isSMulRegular_of_good_sequence M d hd.1 hCM hd.2.1 fs hfs.1 hfs.2.1
        hfs.2.2.1 g hg hfs.2.2.2
      have hdepthM : IsLocalRing.depth (R := R) M = d := by
        simpa only [WithBot.coe_eq_coe] using hCM.trans hd.2.1
      ⟨T.1, T.2.1, by
        rw [T.2.2.1, hdepthM]
        simpa [Nat.cast_sub hd.1] using
          (tsub_add_cancel_of_le
            (Nat.cast_le.mpr hd.1 : (1 : ℕ∞) ≤ d))⟩))

end Module
