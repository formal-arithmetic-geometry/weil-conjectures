/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
module

public import Sheaf.RingTheory.QuasiFiniteAtPrime
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.Algebra.Algebra.Prod

/-!
# Quasi-finiteness along a finite quotient component

Source: Stacks Project, More on Algebra, proof of Lemma 15.11.5 (Tag 09XH), first sentence
(blueprint: lem-weil-pbc-integral-closure-finite-fibre-quasi-finite).
-/

@[expose] public section

universe u v w z

namespace Algebra

/-- A finite-type algebra is quasi-finite at every prime on a quotient component finite
 over the base quotient. Source: Stacks Project, proof of Tag 09XH, first sentence;
 quasi-finiteness is in the sense of Tags 00PL and 00PK (1)
 (blueprint: lem-weil-pbc-integral-closure-finite-fibre-quasi-finite).

The ring isomorphism `e` identifies `B/IB` with `C₁ × C₂`; `hcompat` says the
`A/I`-algebra structure on `C₁` is the one via `A/I → B/IB → C₁` (the spelling of the
landed sibling lem-weil-pbc-integral-closure-finite-fibre-image-clopen).
The idempotent in the statement is `e.symm (1, 0)`; projection onto `C₁` is multiplication
by that idempotent followed by the identification of its factor with `C₁`. Thus `π` below
is exactly the quotient projection in the node, and `T` is the image of `Spec C₁`.

Proof:
1. Write a prime of `T` as the inverse image of a prime of `C₁`. Its contraction `p` to
   `A` contains `I`. Choose `u` lifting `1 - ε`; then `u` belongs to this prime.
2. The map `B → F = p.Fiber B` kills `IB`, hence factors through `B/IB`. The image `e₀`
   of `ε` is idempotent, and `1 - e₀` is the image of `u`.
3. The fibre-prime correspondence (lem-weil-pbc-fibre-ring-primes-bijection) gives the
   unique prime `Q` over the chosen prime of `B`. It contains `1 - e₀`.
4. A finite generating family of `C₁` over `A/I` maps to a spanning family of
   `F/(1 - e₀)F` over `κ(p)`: every elementary tensor becomes a scalar multiple of an
   image from the first component. Hence that quotient is finite over the residue field.
5. By lem-weil-pbc-finite-over-zero-dim-local-discrete-spectrum its spectrum is finite
   and all its primes are maximal. Thus `V(1 - e₀)` is a finite set of closed points of `F`.
6. By lem-weil-pbc-spec-clopen-idempotent, `V(1 - e₀) = D(e₀)` is open. Removing its
   other finitely many closed points shows that `{Q}` is open.
7. By def-weil-pbc-ring-map-quasi-finite-at-prime this is quasi-finiteness at the chosen
   prime. The chosen prime of `T` was arbitrary. -/
theorem isQuasiFiniteAtPrime_of_finite_quotient_component
    (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B]
    [Algebra.FiniteType A B] (I : Ideal A)
    (C₁ : Type w) (C₂ : Type z) [CommRing C₁] [CommRing C₂]
    [Algebra (A ⧸ I) C₁] [Module.Finite (A ⧸ I) C₁]
    (e : (B ⧸ I.map (algebraMap A B)) ≃+* C₁ × C₂)
    (hcompat : ∀ a : A, algebraMap (A ⧸ I) C₁ (Ideal.Quotient.mk I a) =
      (e (Ideal.Quotient.mk _ (algebraMap A B a))).1) :
    let π : B →+* C₁ := (RingHom.fst C₁ C₂).comp
      (e.toRingHom.comp (Ideal.Quotient.mk (I.map (algebraMap A B))))
    let T : Set (PrimeSpectrum B) := Set.range (PrimeSpectrum.comap π)
    ∀ q : PrimeSpectrum B, q ∈ T → IsQuasiFiniteAtPrime A B q := by
  sorry

end Algebra
