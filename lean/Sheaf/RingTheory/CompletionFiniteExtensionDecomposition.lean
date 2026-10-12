module

public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.TensorProduct.Basic

@[expose] public section
universe u v
open scoped TensorProduct
namespace AdicCompletion

/-- The finite-prime decomposition and levelwise compatibility data in the completion theorem.
Source: Stacks Project, Algebra, Lemma 10.97.8 (Tag 07N9), steps 1--4.
(blueprint: lem-weil-pbc-completion-finite-extension-decomposition)

The proof follows Tag 07N9 as follows. Localize at `p`, identify the resulting
primes over the maximal ideal with `p.primesOver S`, and use finite generation and
Noetherianity to obtain finiteness. At every level `n`, the quotient by the `n`th
power of the maximal ideal is a finite zero-dimensional local algebra. The product
of its localizations at its maximal ideals is therefore an isomorphism (with the
empty product interpreted as the zero ring). Localization at a prime of a quotient
identifies each factor with the corresponding quotient of `Localization.AtPrime q`.
Passing to compatible inverse-limit sequences gives the displayed algebra equivalence
`e`; the induced maps from `C` are the ring homomorphisms `g`, and the quotient
identifications give the displayed levelwise equation. Evaluating the product
equivalence on `a ⊗ 1` gives the final compatibility equation. -/
theorem completion_finite_extension_decomposition
    (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
    [IsNoetherianRing R] [Module.Finite R S] (p : Ideal R) [p.IsPrime] :
    let A := Localization.AtPrime p
    let m := IsLocalRing.maximalIdeal A
    let C := AdicCompletion m A
    let B := A ⊗[R] S
    letI := Algebra.TensorProduct.rightAlgebra (R := R) (A := A) (B := S)
    let J := p.map (algebraMap R B)
    let Q := p.primesOver S
    let D := fun q : Q ↦
      AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime q.1))
        (Localization.AtPrime q.1)
    letI := Algebra.TensorProduct.rightAlgebra (R := R) (A := C) (B := S)
    Finite Q ∧
      ∃ (e : (C ⊗[R] S) ≃ₐ[S] (∀ q : Q, D q))
        (g : ∀ q : Q, C →+* D q),
        (∀ (q : Q) (n : ℕ) (a : C) (r : A),
          AdicCompletion.evalₐ m n a = Ideal.Quotient.mk (m ^ n) r →
          AdicCompletion.evalₐ
              (IsLocalRing.maximalIdeal (Localization.AtPrime q.1)) n (g q a) =
            Ideal.Quotient.mk
              ((IsLocalRing.maximalIdeal (Localization.AtPrime q.1)) ^ n)
              (Localization.localRingHom p q.1 (algebraMap R S)
                (Ideal.LiesOver.over (P := q.1) (p := p)) r)) ∧
        (∀ (a : C) (q : Q), e (a ⊗ₜ[R] (1 : S)) q = g q a) := by
  sorry
end AdicCompletion
