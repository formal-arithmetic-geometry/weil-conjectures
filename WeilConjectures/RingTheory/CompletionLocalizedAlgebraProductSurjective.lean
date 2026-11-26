/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.TensorProduct.Basic
import WeilConjectures.Algebra.ChangeIdealCompletion
import WeilConjectures.RingTheory.CompletionLocalizedAlgebraFiniteQuotients

/-!
# Interpolation in the completion of a localized finite algebra

For a finite algebra `S` over a Noetherian ring `R` and a prime `p`, the completion of
`R_p ⊗[R] S` maps onto the product of the completions of the `S_q` over the primes `q`
above `p`.

## Implementation details

The finite-quotient comparison gives bijections `B ⧸ J^n ≃ ∏ q, S_q ⧸ K_q^n` with `K_q`
cofinal with the maximal ideal `M_q`. A target tuple is transported from the `M_q`-adic to the
`K_q`-adic completions via `changeIdealCompletionRing`, the inverse bijections give compatible
coordinates in `B ⧸ J^n`, and `liftRingHom` assembles a preimage.

## References

* [Stacks, Tag 07N9], second equality, before the use of [Stacks, Tag 00MA]
* [Stacks, Tag 0394]
-/

@[expose] public section

universe u v
open scoped TensorProduct
namespace AdicCompletion

/-- The completion of the localized algebra maps onto its local completion product: any ring
map `g` from the `J`-adic completion of `R_p ⊗[R] S` to `∏ q, S_q^∧` that is levelwise induced
by maps `ψ q` extending the local maps is surjective. -/
theorem completion_localizedAlgebra_product_surjective
    (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
    [IsNoetherianRing R] [Module.Finite R S] (p : Ideal R) [p.IsPrime] :
    let A := Localization.AtPrime p
    let B := A ⊗[R] S
    letI := Algebra.TensorProduct.rightAlgebra (R := R) (A := A) (B := S)
    let J := p.map (algebraMap R B)
    let Q := p.primesOver S
    let D := fun q : Q ↦
      AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime q.1))
        (Localization.AtPrime q.1)
    ∀ (ψ : ∀ q : Q, B →ₐ[S] Localization.AtPrime q.1),
      (∀ (q : Q) (r : A), ψ q (r ⊗ₜ[R] (1 : S)) =
        Localization.localRingHom p q.1 (algebraMap R S)
          (Ideal.LiesOver.over (P := q.1) (p := p)) r) →
      ∀ (g : AdicCompletion J B →+* (∀ q : Q, D q)),
        (∀ (q : Q) (n : ℕ) (x : AdicCompletion J B) (b : B),
          evalₐ J n x = Ideal.Quotient.mk (J ^ n) b →
          evalₐ (IsLocalRing.maximalIdeal (Localization.AtPrime q.1)) n (g x q) =
            Ideal.Quotient.mk
              ((IsLocalRing.maximalIdeal (Localization.AtPrime q.1)) ^ n) (ψ q b)) →
        Function.Surjective g := by
  classical
  dsimp
  intro ψ hψ g hg y
  let A := Localization.AtPrime p
  let B := A ⊗[R] S
  let := Algebra.TensorProduct.rightAlgebra (R := R) (A := A) (B := S)
  let J := p.map (algebraMap R B)
  let Q := p.primesOver S
  let C := fun q : Q ↦ Localization.AtPrime q.1
  let M := fun q : Q ↦ IsLocalRing.maximalIdeal (C q)
  let K := fun q : Q ↦ J.map (ψ q).toRingHom
  obtain ⟨hcofinal, hbij⟩ := completion_localizedAlgebra_finite_quotients R S p ψ hψ
  have hcomp (q : Q) : ∃ e : AdicCompletion (K q) (C q) ≃+*
      AdicCompletion (M q) (C q),
      ∀ (z : AdicCompletion (K q) (C q)) (n : ℕ),
        (e z).val n = Submodule.factor (powerReductionJI (M q) (K q) 1 n (C q)
          (by rw [pow_one]; exact (hcofinal q).1)) (z.val (1 * n)) := by
    obtain ⟨c, hc, hpow⟩ := (hcofinal q).2
    exact changeIdealCompletionRing (M q) (K q) c 1 hc (by omega) hpow
      (by rw [pow_one]; exact (hcofinal q).1)
  let e := fun q : Q ↦ Classical.choose (hcomp q)
  have he := fun q : Q ↦ Classical.choose_spec (hcomp q)
  let T := ∀ q : Q, AdicCompletion (K q) (C q)
  let z : T := fun q ↦ (e q).symm (y q)
  let F (n : ℕ) : (B ⧸ J ^ n) →+* (∀ q : Q, C q ⧸ (K q) ^ n) :=
    RingHom.pi (fun q : Q ↦
      Ideal.quotientMap ((K q) ^ n) (ψ q).toRingHom (by
        rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow]))
  let E (n : ℕ) := RingEquiv.ofBijective (F n) (hbij n)
  let f (n : ℕ) : T →+* B ⧸ J ^ n := (E n).symm.toRingHom.comp
    (RingHom.pi fun q ↦ (evalₐ (K q) n).toRingHom.comp (Pi.evalRingHom _ q))
  have hfn (n : ℕ) (t : T) (q : Q) :
      F n (f n t) q = evalₐ (K q) n (t q) := by
    exact congrFun ((E n).apply_symm_apply _) q
  have hf {i j : ℕ} (hij : i ≤ j) :
      (Ideal.Quotient.factorPow J hij).comp (f j) = f i := by
    ext t
    apply (hbij i).1
    funext q
    change F i (Ideal.Quotient.factorPow J hij (f j t)) q = F i (f i t) q
    obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective (f j t)
    have hnat : F i (Ideal.Quotient.factorPow J hij (f j t)) q =
        Ideal.Quotient.factorPow (K q) hij (F j (f j t) q) := by
      rw [← hb]
      simp only [F, RingHom.pi_apply]
      rfl
    rw [hnat, hfn, hfn]
    -- Completion coordinates are compatible with quotient reduction.
    have hv := (t q).property hij
    have hj := factor_evalₐ_eq_eval (K q) (n := j) (t q) (by simp)
    have hi := factor_eval_eq_evalₐ (K q) (n := i) (t q) (by simp)
    obtain ⟨s, hs⟩ := Ideal.Quotient.mk_surjective (evalₐ (K q) j (t q))
    rw [← hs] at hj
    have hvj : (t q).val j = Submodule.Quotient.mk s := hj.symm
    rw [hvj] at hv
    rw [show eval (K q) (C q) i (t q) = Submodule.Quotient.mk s from hv.symm] at hi
    simp [← hs, ← hi]
  let x := liftRingHom J f (fun hij ↦ hf hij) z
  refine ⟨x, ?_⟩
  funext q
  apply ext_evalₐ
  intro n
  obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective (evalₐ J n x)
  have hx : evalₐ J n x = Ideal.Quotient.mk (J ^ n) b := hb.symm
  rw [hg q n x b hx]
  have hK : evalₐ (K q) n (z q) = Ideal.Quotient.mk ((K q) ^ n) (ψ q b) := by
    have hn := hfn n z q
    rw [← evalₐ_liftRingHom J f (fun hij ↦ hf hij) n z, hx] at hn
    change Ideal.quotientMap ((K q) ^ n) (ψ q).toRingHom (by
      rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow])
      (Ideal.Quotient.mk (J ^ n) b) = evalₐ (K q) n (z q) at hn
    rw [Ideal.quotientMap_mk] at hn
    exact hn.symm
  have hv : (z q).val n = Submodule.Quotient.mk (ψ q b) := by
    have h := factor_evalₐ_eq_eval (K q) (n := n) (z q) (by simp)
    rw [hK] at h
    exact h.symm
  have hval := he q (z q) n
  have hv1 : (z q).val (1 * n) = Submodule.Quotient.mk (ψ q b) := by
    convert hv using 1
    · simp
    · exact congr_arg_heq (z q).val (Nat.one_mul n)
    · exact congr_arg_heq
        (fun k ↦ (Submodule.Quotient.mk (ψ q b) : C q ⧸ (K q) ^ k • ⊤))
        (Nat.one_mul n)
  rw [hv1] at hval
  have hy : e q (z q) = y q := (e q).apply_symm_apply (y q)
  rw [hy] at hval
  have h := factor_eval_eq_evalₐ (M q) (n := n) (y q) (by simp)
  rw [show eval (M q) (C q) n (y q) = Submodule.Quotient.mk (ψ q b) from hval] at h
  exact h


end AdicCompletion
