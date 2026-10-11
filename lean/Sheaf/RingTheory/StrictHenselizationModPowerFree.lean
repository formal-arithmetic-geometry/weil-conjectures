/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
import Sheaf.RingTheory.IsStrictHenselization
import Mathlib.RingTheory.AdicCompletion.Algebra
import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.LinearAlgebra.Finsupp.Defs

/-!
# Fixed bases for strict henselization quotients and their completed comparison

Source: Stacks Project, More on Algebra, Tag 07QM(4) and the proof of Tag 06LJ(c)
(blueprint: lem-sc-strict-henselization-mod-power-free).
-/

universe u

namespace Algebra

/-- There are fixed lifts in the strict henselization giving bases of every positive-power
quotient, and the induced compatible quotient isomorphisms identify its ring completion
with the module completion of the free module on those lifts.
Source: Stacks Project, Tag 07QM(4) and proof of Tag 06LJ(c)
(blueprint: lem-sc-strict-henselization-mod-power-free).

The quotient isomorphisms are written as `A`-linear equivalences. Both sides are annihilated
by the same power of the maximal ideal, so this is exactly linearity over the base quotient.
The final equality specifies the completed comparison at each positive-power coordinate;
it is therefore the canonical inverse-limit comparison induced by the quotient bases.
The target of that comparison is the ring completion itself, using `AdicCompletion` with
ideal `nC`. The source is the displayed inverse limit of the quotients of `X →₀ A`.

Proof:
1. Choose a basis of the separable residue-field closure over the residue field of `A`
and lift its vectors to `C`. Strict henselization is faithfully flat
(lem-sc-strict-henselization-faithfully-flat), and its maximal ideal and residue field are
`nC` and the chosen closure (lem-weil-pbc-strict-henselization-triples).
2. For every positive `r`, `(nC)^r = n^r C`. The quotient is flat over `A/n^r` by flat
base change (Stacks Tag 00HI). This base ring has nilpotent maximal ideal, and the chosen
lifts reduce to a residue-field basis. Apply lem-weil-pbc-local-artinian-basis-when-flat
(Stacks Tag 051F) to obtain the quotient basis on the same lifts for every `r`.
3. Sending each free generator to its fixed lift gives quotient isomorphisms commuting
with reduction. Their inverse limit is the indicated linear equivalence of completions.
The positive powers are cofinal in all natural powers, so the zero coordinate adds no data.
By def-weil-pbc-adic-completion, the target inverse limit is the ring completion at `nC`.
-/
theorem strictHenselization_mod_power_free
    (A K C : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [Field K]
    [Algebra (IsLocalRing.ResidueField A) K] [IsSepClosure (IsLocalRing.ResidueField A) K]
    [Algebra A K] [IsScalarTower A (IsLocalRing.ResidueField A) K]
    [CommRing C] [Algebra A C] (hC : IsStrictHenselization A K C) :
    ∃ (X : Type u) (x : X → C)
      (e : ∀ (r : ℕ), 1 ≤ r →
        (X →₀ A ⧸ (IsLocalRing.maximalIdeal A) ^ r) ≃ₗ[A]
          C ⧸ ((IsLocalRing.maximalIdeal A).map (algebraMap A C)) ^ r),
      (∀ (r : ℕ) (hr : 1 ≤ r) (i : X),
        e r hr (Finsupp.single i 1) =
          Ideal.Quotient.mk (((IsLocalRing.maximalIdeal A).map (algebraMap A C)) ^ r)
            (x i)) ∧
      ∃ E : AdicCompletion (IsLocalRing.maximalIdeal A) (X →₀ A) ≃ₗ[A]
          AdicCompletion ((IsLocalRing.maximalIdeal A).map (algebraMap A C)) C,
        ∀ (r : ℕ) (hr : 1 ≤ r)
          (z : AdicCompletion (IsLocalRing.maximalIdeal A) (X →₀ A)) (f : X →₀ A),
          AdicCompletion.eval (IsLocalRing.maximalIdeal A) (X →₀ A) r z =
            ((IsLocalRing.maximalIdeal A) ^ r •
              (⊤ : Submodule A (X →₀ A))).mkQ f →
          AdicCompletion.evalₐ ((IsLocalRing.maximalIdeal A).map (algebraMap A C)) r
              (E z) =
            e r hr (f.mapRange (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal A) ^ r))
              (map_zero (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal A) ^ r)))) := by
  sorry

end Algebra
