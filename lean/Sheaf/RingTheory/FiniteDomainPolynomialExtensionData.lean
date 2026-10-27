module

public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.FinitePresentation
import Mathlib.RingTheory.Polynomial.IsIntegral
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic

/-!
# Polynomial extension data for a finite inclusion of domains

Source: Stacks Project, algebra.tex, Tags 030A, 00FN, 00FP (3), 00GK; the finite affine
polynomial calculation used with more-morphisms.tex, Tag 0F32
(blueprint: lem-sfb-finite-domain-polynomial-extension-data).
-/

@[expose] public section

universe u v

namespace MvPolynomial

/-- Polynomial extension preserves the prescribed finite module generators of an injective
extension of domains over a normal Noetherian domain. Algebra generation is expressed by
surjectivity of evaluation at these same constant polynomials, over the coefficient map.

Source: Stacks Project, algebra.tex, Tags 030A (`lemma-polynomial-domain-normal`), 00FN
(`lemma-Noetherian-permanence`), 00FP (3)
(`lemma-Noetherian-finite-type-is-finite-presentation`), 00GK (`lemma-finite-is-integral`);
finite affine polynomial calculation for more-morphisms.tex, Tag 0F32
(`lemma-quasi-finite-Noetherian-universally-open`).
(blueprint: lem-sfb-finite-domain-polynomial-extension-data)

Proof plan:
1. Compare every coefficient and use injectivity of `φ` to prove injectivity of `map φ`.
   This is the finite monomial description of `def-weil-pbc-mv-polynomial-ring`.
2. Regroup monomials to identify adjoining `m + 1` variables with adjoining one variable
   to the polynomial ring in `m` variables. Leading coefficients give the domain property
   for both polynomial rings. Induction using `lem-weil-pbc-polynomial-ring-normal-domain`
   (030A) gives integral closedness of the polynomial ring over `A`.
3. The variables generate that ring over `A`; apply
   `lem-weil-pbc-finite-type-algebra-noetherian` (00FN).
4. Expand each of the finitely many coefficients of `f` using the given family `c`.
   For each `j`, assemble its expansion coefficients into a polynomial `a j` over `A`.
   Distributing finite sums gives `f = ∑ j, map φ (a j) * C (c j)`. Any subalgebra
   containing the same constants contains these sums, so evaluation is surjective.
   This calculation uses `def-weil-pbc-mv-polynomial-ring`, and includes zero variables.
5. Apply `lem-weil-pbc-finite-type-noetherian-finite-presentation` (00FP (3)) to the
   finite type algebra from step 4 over the Noetherian base from step 3. Apply
   `lem-weil-pbc-finite-algebra-is-integral` (00GK) to the module generators from step 4.
   Its conclusion says every element satisfies a monic equation over the given map. -/
theorem finite_domain_polynomial_extension_data
    {A : Type u} {C : Type v} [CommRing A] [CommRing C] [IsDomain A] [IsDomain C]
    [IsNoetherianRing A] [IsIntegrallyClosed A]
    (φ : A →+* C) (hφ : Function.Injective φ) (r : ℕ) (c : Fin r → C)
    (hc : ∀ x : C, ∃ a : Fin r → A, x = ∑ j, φ (a j) * c j) (n : ℕ) :
    Function.Injective (map (σ := Fin n) φ) ∧
      IsNoetherianRing (MvPolynomial (Fin n) A) ∧
      IsDomain (MvPolynomial (Fin n) A) ∧
      IsIntegrallyClosed (MvPolynomial (Fin n) A) ∧
      IsDomain (MvPolynomial (Fin n) C) ∧
      (∀ f : MvPolynomial (Fin n) C, ∃ a : Fin r → MvPolynomial (Fin n) A,
        f = ∑ j, map φ (a j) * MvPolynomial.C (c j)) ∧
      Function.Surjective
        (eval₂Hom (map (σ := Fin n) φ) (fun j : Fin r ↦ MvPolynomial.C (c j))) ∧
      (map (σ := Fin n) φ).FinitePresentation ∧
      (map (σ := Fin n) φ).IsIntegral := by
  sorry

end MvPolynomial
