/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group X2
-/
module

public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Spectrum.Maximal.Defs

/-!
# Local charts of the finite algebra quotient

Source: Stacks Project, Tags 07N9, 00E3 and 00CT.
(blueprint: lem-weil-pbc-localized-finite-quotient-charts)
-/

@[expose] public section

universe u v
open scoped TensorProduct
namespace AdicCompletion

/-- The local factors of a positive finite-algebra quotient are its localizations.
Source: Stacks Project, Tag 07N9, prime correspondence in the proof;
Tags 00E3 (localization prime correspondence) and 00CT (quotients and localization).
(blueprint: lem-weil-pbc-localized-finite-quotient-charts)

Proof: The tensor algebra B is the localization of S at the image of R minus p.
Extension and contraction identify primes of B containing J with primes of S
whose contraction is p. Indeed their contraction contains p, and disjointness
from R minus p gives the reverse inclusion. A prime contains J^n exactly when
it contains J, since n is positive. The quotient correspondence therefore gives
an equivalence between Q and the primes of B/J^n. These primes are maximal:
B is finite over R_p, and the quotient is integral over the quotient of R_p
by its maximal-ideal power, which has only its maximal ideal as a prime.
The equivalence sends q to the quotient of its extension to B; its displayed
contraction formula determines it uniquely. Localizing B at that extension is
S_q: both invert precisely the elements outside q, by localization in stages.
The S-algebra property determines psi on S, and on inverses of the denominators,
so psi is this canonical localization map. Localization commutes with quotient,
and map preserves powers, giving the stated localization structure on S_q/K_q^n.
If Q is empty, B/J^n is the zero ring and both indexing types are empty. -/
theorem localized_finite_quotient_charts
    (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
    [Module.Finite R S] (p : Ideal R) [p.IsPrime] :
    let A := Localization.AtPrime p
    let B := A ⊗[R] S
    letI := Algebra.TensorProduct.rightAlgebra (R := R) (A := A) (B := S)
    let J := p.map (algebraMap R B)
    let Q := p.primesOver S
    ∀ (ψ : ∀ q : Q, B →ₐ[S] Localization.AtPrime q.1) (n : ℕ), n ≠ 0 →
      let K := fun q : Q ↦ J.map (ψ q).toRingHom
      ∃ e : Q ≃ MaximalSpectrum (B ⧸ J ^ n),
        (∀ q : Q, (e q).asIdeal.comap
          ((Ideal.Quotient.mk (J ^ n)).comp (algebraMap S B)) = q.1) ∧
        ∀ q : Q,
          let f : (B ⧸ J ^ n) →+* (Localization.AtPrime q.1 ⧸ (K q) ^ n) :=
            Ideal.quotientMap ((K q) ^ n) (ψ q).toRingHom (by
            rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow])
          letI := f.toAlgebra
          IsLocalization.AtPrime (Localization.AtPrime q.1 ⧸ (K q) ^ n) (e q).asIdeal := by
  sorry

end AdicCompletion
