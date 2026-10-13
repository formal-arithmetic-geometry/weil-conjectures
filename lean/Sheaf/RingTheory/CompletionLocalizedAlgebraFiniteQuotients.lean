/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F2
-/
module

public import Mathlib.Algebra.Ring.Pi
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.TensorProduct.Basic

import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Localization.Submodule
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.RingTheory.QuasiFinite.Basic
import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.Finiteness.Ideal
import Sheaf.RingTheory.LocalizationPrimeResidueFieldIso

@[expose] public section

universe u v
open scoped TensorProduct
namespace AdicCompletion

/-- The algebraic finite-quotient comparison for a localized finite algebra.
Source: Stacks Project, Algebra, Tag 07N9, second equality; Tags 00JA and 00CT.
Proof: Write A = R_p, B = A tensor_R S, and m = pA. B is finite over the
Noetherian local ring A. The primes of B above m correspond to Q, and their
local rings identify with S_q. The S-algebra property and the prescribed values
on A determine psi on pure tensors, hence identify psi with these localizations.
For n > 0, B/J^n is Artinian: it is finite over the Artinian ring A/m^n.
Its maximal ideals correspond to Q. The canonical product decomposition of an
Artinian ring into its localizations, followed by localization of quotients,
is exactly the displayed quotient map. Thus this map is bijective. At n = 0
both sides are zero rings, including when Q is empty.
In each S_q, the quotient by K_q is a localization of the finite-dimensional
fibre B/mB, hence Artinian local. Its only prime is its maximal ideal, so
radical K_q is the maximal ideal. Also K_q is contained in that maximal ideal.
S_q is Noetherian, so its maximal ideal is finitely generated. The radical
power lemma gives a power of this maximal ideal contained in K_q; increase the
exponent to at least one if necessary.
(blueprint: lem-weil-pbc-completion-localized-algebra-finite-quotients)
-/
theorem completion_localizedAlgebra_finite_quotients
    (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
    [IsNoetherianRing R] [Module.Finite R S] (p : Ideal R) [p.IsPrime] :
    let A := Localization.AtPrime p
    let B := A ⊗[R] S
    letI := Algebra.TensorProduct.rightAlgebra (R := R) (A := A) (B := S)
    let J := p.map (algebraMap R B)
    let Q := p.primesOver S
    ∀ (ψ : ∀ q : Q, B →ₐ[S] Localization.AtPrime q.1),
      (∀ (q : Q) (r : A), ψ q (r ⊗ₜ[R] (1 : S)) =
        Localization.localRingHom p q.1 (algebraMap R S)
          (Ideal.LiesOver.over (P := q.1) (p := p)) r) →
      let K := fun q : Q ↦ J.map (ψ q).toRingHom
      (∀ q : Q, K q ≤ IsLocalRing.maximalIdeal (Localization.AtPrime q.1) ∧
        ∃ c : ℕ, 1 ≤ c ∧
          (IsLocalRing.maximalIdeal (Localization.AtPrime q.1)) ^ c ≤ K q) ∧
      ∀ n : ℕ, Function.Bijective
        (RingHom.pi (fun q : Q ↦
          Ideal.quotientMap ((K q) ^ n) (ψ q).toRingHom (by
            rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow])) :
          (B ⧸ J ^ n) →+* (∀ q : Q, Localization.AtPrime q.1 ⧸ (K q) ^ n)) := by
  sorry

end AdicCompletion
