/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.Algebra.MvPolynomial.Rename
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! # Evaluation and finite presentations of an increasing filtered module

Source: Stacks Project, Tags 053E (proof of (2)) and 052N (module homogenization).
(blueprint: lem-trf-filtered-module-evaluation-presentation)

The evaluation maps and relation submodule below are actual constructions. The action
existence statement supplies the polynomial module structures specified by the generators.
The main statement works with any structures having those prescribed actions. Additive
quotient equivalences are accompanied by explicit scalar compatibility, expressing the
claimed Q-linearity without choosing a second module instance on a quotient.
-/

@[expose] public section

universe u v

open scoped DirectSum

namespace Module

/-- Evaluation of the finite-support direct sum by adding its components.
Source: Stacks Project, Tags 053E (2) and 052N, explicit dehomogenization construction.
(blueprint: lem-trf-filtered-module-evaluation-presentation) -/
def filteredModuleEvaluation (A : Type u) [CommRing A]
    (M : Type v) [AddCommGroup M] [Module A M] (F : ℕ → Submodule A M) :
    (⨁ d, F d) →ₗ[A] M :=
  DirectSum.toModule A ℕ M (fun d ↦ (F d).subtype)

/-- Substitution of one for the distinguished variable and retention of all other variables.
Source: Stacks Project, Tag 052N, polynomial dehomogenization in the proof.
(blueprint: lem-trf-filtered-module-evaluation-presentation) -/
noncomputable def filteredPolynomialEvaluation (A : Type u) [CommRing A] (n : ℕ) :
    MvPolynomial (Option (Fin n)) A →+* MvPolynomial (Fin n) A :=
  MvPolynomial.eval₂Hom MvPolynomial.C (fun i ↦ i.elim 1 MvPolynomial.X)

/-- The submodule (X₀ - 1)N, written as the span of its scalar-multiplication image.
Source: Stacks Project, Tags 053E (2) and 052N, explicit evaluation-kernel calculation.
(blueprint: lem-trf-filtered-module-evaluation-presentation) -/
noncomputable def filteredModuleEvaluationRelations (A : Type u) [CommRing A]
    (M : Type v) [AddCommGroup M] [Module A M] (n : ℕ)
    (F : ℕ → Submodule A M) [Module (MvPolynomial (Option (Fin n)) A) (⨁ d, F d)] :
    Submodule (MvPolynomial (Option (Fin n)) A) (⨁ d, F d) :=
  Submodule.span _ (Set.range (fun y : ⨁ d, F d ↦
    (MvPolynomial.X none - 1 : MvPolynomial (Option (Fin n)) A) • y))

/-- The commuting shifts give precisely the prescribed polynomial module structures.
Source: Stacks Project, Tags 053E (2) and 052N.
(blueprint: lem-trf-filtered-module-evaluation-presentation)

Proof (step 1 of the node): include each F_d in degree d+1 for X₀, and compose
T_i with the degree-(d+1) inclusion for X_i. These maps are A-linear and commute,
as is checked on each direct-sum summand. Finite monomial sums therefore define
the P-action. The identical monomial construction from the commuting T_i gives
the Q-action on M. Constants act through the original A-module structures. -/
theorem filteredModulePolynomialActions
    (A : Type u) [CommRing A] (M : Type v) [AddCommGroup M] [Module A M]
    (n : ℕ) (T : Fin n → M →ₗ[A] M) (F : ℕ → Submodule A M)
    (hF : Monotone F) (hEx : ∀ x : M, ∃ d, x ∈ F d)
    (hcomm : ∀ i j, Commute (T i) (T j))
    (hT : ∀ i d, ∀ x ∈ F d, T i x ∈ F (d + 1))
    : ∃ (modN : Module (MvPolynomial (Option (Fin n)) A) (⨁ d, F d))
        (modM : Module (MvPolynomial (Fin n) A) M),
        (∀ (a : A) (z : (⨁ d, F d)),
          @SMul.smul _ _ modN.toSMul (MvPolynomial.C a) z = a • z) ∧
        (∀ (d : ℕ) (x : F d),
          @SMul.smul _ _ modN.toSMul (MvPolynomial.X none)
            (DirectSum.of (fun d ↦ F d) d x) =
              DirectSum.of (fun d ↦ F d) (d + 1) ⟨x, hF (Nat.le_succ d) x.property⟩) ∧
        (∀ (i : Fin n) (d : ℕ) (x : F d),
          @SMul.smul _ _ modN.toSMul (MvPolynomial.X (some i))
            (DirectSum.of (fun d ↦ F d) d x) =
              DirectSum.of (fun d ↦ F d) (d + 1) ⟨T i x, hT i d x x.property⟩) ∧
        (∀ (a : A) (x : M), @SMul.smul _ _ modM.toSMul (MvPolynomial.C a) x = a • x) ∧
        (∀ (i : Fin n) (x : M), @SMul.smul _ _ modM.toSMul (MvPolynomial.X i) x = T i x) := by
  sorry

/-- Evaluation has kernel (X₀-1)N, identifies the quotient Q-linearly with M, and
specializes every finite presentation, with the indicated evaluated matrix and augmentation.
Source: Stacks Project, Tags 053E (2) and 052N.
(blueprint: lem-trf-filtered-module-evaluation-presentation)

Proof, following the six elementary steps of the accepted node:
1. The shifts defining the polynomial actions commute on every summand.
2. Adding components commutes with X₀ as identity and with X_i as T_i; expand
   monomials to obtain P-linearity relative to substitution. Exhaustiveness gives
   a lift of every m in some F_d, hence surjectivity.
3. For a finite sum with sum of components zero, let y_d=-sum_{i<=d}x_i.
   Increasingness puts y_d in F_d. Consecutive differences, including the last
   component by the zero-sum relation, give z=(X₀-1)y. For support in degree zero
   the sum is zero itself. The reverse kernel containment follows by evaluation.
4. Write p=sum q_k X₀^k. The geometric-sum identity makes p-s(p(1,X)) a multiple
   of X₀-1. It gives the ring quotient isomorphism. The evaluation-kernel equality
   gives the module coset equivalence; its formula on s(q)z gives Q-linearity.
5. For an exact presentation, evaluate its matrix entries and send each generator
   to the evaluation of its image under pi. Finite basis expansion gives both
   compatibility identities and surjectivity of the evaluated augmentation.
6. Lift a relation a to w over P. Then pi(w)=(X₀-1)y. Lift y to c in P^v and write
   w-(X₀-1)c=Hb using exactness. Evaluation yields a=H(1,X)b(1,X). Thus the
   evaluated sequence is exact. Choose any finite presentation when N is finitely
   presented to conclude finite presentation of M. All arguments include n=0,
   zero modules, and empty finite sets of generators or relations. -/
theorem filteredModuleEvaluationPresentation
    (A : Type u) [CommRing A] (M : Type v) [AddCommGroup M] [Module A M]
    (n : ℕ) (T : Fin n → M →ₗ[A] M) (F : ℕ → Submodule A M)
    (hF : Monotone F) (hEx : ∀ x : M, ∃ d, x ∈ F d)
    (hcomm : ∀ i j, Commute (T i) (T j))
    (hT : ∀ i d, ∀ x ∈ F d, T i x ∈ F (d + 1))
    [Module (MvPolynomial (Option (Fin n)) A) (⨁ d, F d)] [Module (MvPolynomial (Fin n) A) M]
    (hNC : ∀ (a : A) (z : (⨁ d, F d)),
      (MvPolynomial.C a : MvPolynomial (Option (Fin n)) A) • z = a • z)
    (hN0 : ∀ (d : ℕ) (x : F d),
      (MvPolynomial.X none : MvPolynomial (Option (Fin n)) A) • DirectSum.of (fun d ↦ F d) d x =
        DirectSum.of (fun d ↦ F d) (d + 1) ⟨x, hF (Nat.le_succ d) x.property⟩)
    (hNi : ∀ (i : Fin n) (d : ℕ) (x : F d),
      (MvPolynomial.X (some i) : MvPolynomial (Option (Fin n)) A) • DirectSum.of (fun d ↦ F d) d x =
        DirectSum.of (fun d ↦ F d) (d + 1) ⟨T i x, hT i d x x.property⟩)
    (hMC : ∀ (a : A) (x : M), (MvPolynomial.C a : MvPolynomial (Fin n) A) • x = a • x)
    (hMi : ∀ (i : Fin n) (x : M), (MvPolynomial.X i : MvPolynomial (Fin n) A) • x = T i x) :
    Function.Surjective (filteredModuleEvaluation A M F) ∧
    (∀ (p : MvPolynomial (Option (Fin n)) A) (z : (⨁ d, F d)),
      filteredModuleEvaluation A M F (p • z) =
        filteredPolynomialEvaluation A n p • filteredModuleEvaluation A M F z) ∧
    (∀ z : (⨁ d, F d), filteredModuleEvaluation A M F z = 0 ↔
      ∃ y : (⨁ d, F d), z = (MvPolynomial.X none - 1 : MvPolynomial (Option (Fin n)) A) • y) ∧
    (∃ r : ((MvPolynomial (Option (Fin n)) A) ⧸ Ideal.span
        {(MvPolynomial.X none - 1 : MvPolynomial (Option (Fin n)) A)}) ≃+* (MvPolynomial (Fin n) A),
      ∀ p : MvPolynomial (Option (Fin n)) A,
        r (Ideal.Quotient.mk _ p) = filteredPolynomialEvaluation A n p) ∧
    (∃ e : ((⨁ d, F d) ⧸ filteredModuleEvaluationRelations A M n F) ≃+ M,
      (∀ z : (⨁ d, F d), e (Submodule.mkQ _ z) = filteredModuleEvaluation A M F z) ∧
      (∀ (q : MvPolynomial (Fin n) A) (z : (⨁ d, F d)),
        e (Submodule.mkQ _ ((MvPolynomial.rename some q) • z)) =
          q • e (Submodule.mkQ _ z))) ∧
    (Module.FinitePresentation (MvPolynomial (Option (Fin n)) A) (⨁ d, F d) →
      Module.FinitePresentation (MvPolynomial (Fin n) A) M) ∧
    (∀ (a b : ℕ)
      (H : (Fin a → MvPolynomial (Option (Fin n)) A) →ₗ[MvPolynomial (Option (Fin n)) A]
        (Fin b → MvPolynomial (Option (Fin n)) A))
      (π : (Fin b → MvPolynomial (Option (Fin n)) A) →ₗ[MvPolynomial (Option (Fin n)) A]
        (⨁ d, F d)),
      Function.Exact H π → Function.Surjective π →
      ∃ (H' : (Fin a → MvPolynomial (Fin n) A) →ₗ[MvPolynomial (Fin n) A]
          (Fin b → MvPolynomial (Fin n) A))
        (π' : (Fin b → MvPolynomial (Fin n) A) →ₗ[MvPolynomial (Fin n) A] M),
        (∀ (x : Fin a → MvPolynomial (Fin n) A) (i : Fin b),
          H' x i = ∑ j, filteredPolynomialEvaluation A n (H (Pi.single j 1) i) * x j) ∧
        (∀ x : Fin b → MvPolynomial (Fin n) A,
          π' x = ∑ j, x j • filteredModuleEvaluation A M F (π (Pi.single j 1))) ∧
        Function.Exact H' π' ∧ Function.Surjective π') := by
  sorry

end Module
