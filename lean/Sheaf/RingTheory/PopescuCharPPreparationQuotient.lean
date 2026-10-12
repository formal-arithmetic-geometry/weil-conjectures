/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V3
-/
module
public import Sheaf.RingTheory.PopescuResolution
public import Sheaf.RingTheory.StrictlyStandardElement
public import Sheaf.RingTheory.EssentiallySmooth
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic

/-!
# Popescu characteristic-p preparation: quotient descent

Source: Stacks Project, Smoothing Ring Maps, Lemma 07FJ.
-/

@[expose] public section
universe u v w
open scoped TensorProduct
namespace Algebra

-- Previous interface: STATEMENT-DISPUTED because zero parameters satisfy hparam without
-- cutting the target localization to dimension zero. The power bound below repairs it.
/-- Descend the auxiliary thickening factorization to the eighth-power quotient and derive
the dimension and minimal-prime alternative.
Source: Stacks Project, Smoothing Ring Maps, proof of Lemma 07FJ, construction and
quotient steps (with n=N+de).
(blueprint: popescu-char-p-preparation-quotient).

Proof:
1. Let R=k[X_1,…,X_m], J=(π_i^8), J_C=JC and J_Λ=JΛ. Membership of the parameter images in q
   gives J_Λ⊆q. The quotient universal property gives γ₀:C/JC→Λ/JΛ; the quotient prime
   correspondence gives q₀=q/JΛ. Both satisfy the displayed commutative squares. C/JC is
   finitely presented over R/J by base change. Put Q=R_(q∩R), L=Λ_q. Localization of a quotient
   identifies P=(R/J)_(q₀∩(R/J)) with Q/JQ and L₀=(Λ/JΛ)_q₀ with L/JL. These identifications
   preserve the structure maps.

2. The supplied positive n and containment m_L^n⊆JL imply that the maximal ideal of L/JL is
   nilpotent. L is Noetherian since Λ is Noetherian. Thus the nonzero quotient L/JL is Artinian
   local by the power bound, and has Krull dimension zero. If popescuIdeal γ₀ is not contained
   in q₀ choose the first alternative. Otherwise any prime containing popescuIdeal γ₀ and
   contained in q₀ localizes to a prime of L₀, hence its unique prime. The prime correspondence
   for localization then makes it equal to q₀. This proves minimality. Neither dimension nor
   minimality is inferred from the annihilator equalities.

3. Use the supplied I⊆JQ, K⊆JL, IL⊆K, f:Q⊗_R C→D and g:D→L/K, with D essentially smooth over
   Q/I. The first containment defines Q/I→P; the second defines L/K→L₀. Set E=P⊗_(Q/I)D. Tensor
   universality gives E→L₀ from the compatible maps. The map Q⊗_R C→D→E kills JC since J is zero
   in P, hence descends to P⊗_(R/J)(C/JC)→E. On pure tensors the composite is the required
   tensor lift, by the supplied equation gf composed with L/K→L₀. Pure tensors generate, so this
   is the required algebra-homomorphism equality.

4. Present D as a localization of a smooth Q/I-algebra S. Base change S to P; it is smooth over
   P. Localization base change identifies E with its localization at the image of the
   multiplicative subset. Thus E is essentially smooth over P. The carriers Q,P,D live in
   Type(max u v) or smaller, so their tensor product E has a representative there; transport
   structures and maps along this representative. Combine this factorization with the dimension
   and minimality from step 2 to obtain the second alternative.
-/
theorem popescu_char_p_preparation_quotient
    {k : Type u} {A : Type v} {Λ : Type w}
    [Field k] [CommRing A] [CommRing Λ] [Algebra k A] [Algebra k Λ]
    [FinitePresentation k A] [IsNoetherianRing Λ]
    (p : ℕ) [CharP k p] (hp : 0 < p)
    (α : A →ₐ[k] Λ) (q : PrimeSpectrum Λ)
    (m : ℕ) [Algebra (MvPolynomial (Fin m) k) Λ]
      [IsScalarTower k (MvPolynomial (Fin m) k) Λ]
    (C : Type (max u v)) [CommRing C] [Algebra k C]
      [Algebra (MvPolynomial (Fin m) k) C]
      [IsScalarTower k (MvPolynomial (Fin m) k) C]
      [FinitePresentation (MvPolynomial (Fin m) k) C]
    (β : A →ₐ[k] C) (γ : C →ₐ[MvPolynomial (Fin m) k] Λ)
    (r : ℕ) (π : Fin r → MvPolynomial (Fin m) k)
    (hbase : (γ.restrictScalars k).comp β = α ∧ popescuIdeal α ≤ popescuIdeal γ)
    (hparam : 1 ≤ r ∧
      (∀ i, algebraMap (MvPolynomial (Fin m) k) Λ (π i) ∈ q.asIdeal) ∧
      (∀ (i : Fin r)
        (x : MvPolynomial (Fin m) k ⧸ Ideal.span
          {y | ∃ j : Fin r, j.val < i.val ∧ y = π j ^ 8}),
        π i • x = 0 ↔ π i ^ 2 • x = 0) ∧
      (∀ (i : Fin r)
        (x : Λ ⧸ Ideal.span
          {y | ∃ j : Fin r, j.val < i.val ∧
            y = algebraMap (MvPolynomial (Fin m) k) Λ (π j) ^ 8}),
        π i • x = 0 ↔ π i ^ 2 • x = 0) ∧
      (∀ i, IsStrictlyStandardElement
        (R := MvPolynomial (Fin m) k)
        (algebraMap (MvPolynomial (Fin m) k) C (π i))))
    (hconstruction :
    let R := MvPolynomial (Fin m) k
    let J := Ideal.span (Set.range (fun i : Fin r ↦ π i ^ 8))
    let Q := Localization.AtPrime (q.asIdeal.under R)
    let L := Localization.AtPrime q.asIdeal
    letI := Localization.AtPrime.algebraOfLiesOver (q.asIdeal.under R) q.asIdeal
    let JQ := J.map (algebraMap R Q)
    let JL := (J.map (algebraMap R Λ)).map (algebraMap Λ L)
    ∃ (n : ℕ), 0 < n ∧ IsLocalRing.maximalIdeal L ^ n ≤ JL ∧
      ∃ (I : Ideal Q) (K : Ideal L),
        I ≤ JQ ∧ K ≤ JL ∧ I.map (algebraMap Q L) ≤ K ∧
        ∃ (D : Type (max u v)) (_ : CommRing D) (_ : Algebra Q D)
          (_ : Algebra (Q ⧸ I) D) (_ : IsScalarTower Q (Q ⧸ I) D),
          EssentiallySmooth (Q ⧸ I) D ∧
          ∃ (f : Q ⊗[R] C →ₐ[Q] D) (g : D →ₐ[Q] L ⧸ K),
            g.comp f = Algebra.TensorProduct.lift (Algebra.ofId Q (L ⧸ K))
              ((Ideal.Quotient.mkₐ R K).comp
                ((IsScalarTower.toAlgHom R Λ L).comp γ))
              (fun _ _ ↦ Commute.all _ _)) :
    let R := MvPolynomial (Fin m) k
    let J := Ideal.span (Set.range (fun i : Fin r ↦ π i ^ 8))
    let J_C := J.map (algebraMap R C)
    let J_Λ := J.map (algebraMap R Λ)
    let R₀ := R ⧸ J
    let C₀ := C ⧸ J_C
    let Λ₀ := Λ ⧸ J_Λ
    ∃ (_ : FinitePresentation R₀ C₀) (γ₀ : C₀ →ₐ[R₀] Λ₀)
      (q₀ : PrimeSpectrum Λ₀),
      γ₀.toRingHom.comp (Ideal.Quotient.mk J_C) =
        (Ideal.Quotient.mk J_Λ).comp γ.toRingHom ∧
      PrimeSpectrum.comap (Ideal.Quotient.mk J_Λ) q₀ = q ∧
      (¬ popescuIdeal γ₀ ≤ q₀.asIdeal ∨
        q₀.asIdeal ∈ (popescuIdeal γ₀).minimalPrimes ∧
        ringKrullDim (Localization.AtPrime q₀.asIdeal) = 0 ∧
        let P := Localization.AtPrime (q₀.asIdeal.under R₀)
        let L := Localization.AtPrime q₀.asIdeal
        letI := Localization.AtPrime.algebraOfLiesOver
          (q₀.asIdeal.under R₀) q₀.asIdeal
        ∃ (E : Type (max u v)) (_ : CommRing E) (_ : Algebra P E),
          EssentiallySmooth P E ∧
          ∃ (f : P ⊗[R₀] C₀ →ₐ[P] E) (g : E →ₐ[P] L),
            g.comp f = Algebra.TensorProduct.lift (Algebra.ofId P L)
              ((IsScalarTower.toAlgHom R₀ Λ₀ L).comp γ₀)
              (fun _ _ ↦ Commute.all _ _)) := by
  sorry

end Algebra
