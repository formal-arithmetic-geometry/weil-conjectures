module

public import Mathlib.RingTheory.DividedPowers.DPMorphism
public import Mathlib.LinearAlgebra.Basis.Basic
import Sheaf.RingTheory.DividedPowersFactorialCriterion
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.RingTheory.DividedPowers.SubDPIdeal
import Mathlib.RingTheory.Flat.Basic
import Sheaf.RingTheory.DividedPowersFlatExtension
import Sheaf.RingTheory.DividedPowersGlueIdeals

/-!
# Ordinary divided-power polynomial extension

Source: Stacks Project, Tag 07H5 (lemma-divided-power-polynomial-algebra), existence,
uniqueness and universal property (blueprint: lem-sfb-ordinary-pd-polynomial-extension).

The structure below records the free divided-power polynomial algebra, its augmentation
ideal and the universal property asserted by the source.  The theorem asserts existence
of this data; its proof is postponed to stage 3.
-/

@[expose] public section

set_option autoImplicit false

universe u w

namespace DividedPowers

/-- Data of the ordinary divided-power polynomial extension.

Source: Stacks Project, Tag 07H5 (lemma-divided-power-polynomial-algebra)
(blueprint: lem-sfb-ordinary-pd-polynomial-extension).
-/
structure OrdinaryPDPolynomialExtensionData
    (C : Type u) [CommRing C] (I : Ideal C) (γ : DividedPowers I) (t : ℕ)
    (ht : 1 ≤ t) where
  P : Type u
  [commRingP : CommRing P]
  [algebraCP : Algebra C P]
  basis : Module.Basis (Fin t →₀ ℕ) C P
  basis_zero : basis 0 = 1
  basis_mul : ∀ (α β : Fin t →₀ ℕ),
    basis α * basis β =
      (∏ j : Fin t, (Nat.choose (α j + β j) (α j) : C)) • basis (α + β)
  positive : Ideal P
  positive_eq : positive = Ideal.span {x | ∃ α : Fin t →₀ ℕ, α ≠ 0 ∧ x = basis α}
  K : Ideal P
  K_eq : K = Ideal.map (algebraMap C P) I ⊔ positive
  δ : DividedPowers K
  restrict : ∀ (n : ℕ) (x : C), x ∈ I →
    δ.dpow n (algebraMap C P x) = algebraMap C P (γ.dpow n x)
  generators : ∀ (n : ℕ) (j : Fin t), 1 ≤ n →
    δ.dpow n (basis (Finsupp.single j 1)) =
      basis (n • Finsupp.single j 1)
  unique : ∀ (δ' : DividedPowers K),
    (∀ (n : ℕ) (x : C), x ∈ I →
      δ'.dpow n (algebraMap C P x) = algebraMap C P (γ.dpow n x)) →
    (∀ (n : ℕ) (j : Fin t), 1 ≤ n →
      δ'.dpow n (basis (Finsupp.single j 1)) =
        basis (n • Finsupp.single j 1)) →
    δ' = δ
  universal :
    ∀ (D : Type (max u w)) [CommRing D] (L : Ideal D) (η : DividedPowers L)
      (f : C →+* D), IsDPMorphism γ η f →
      (z : Fin t → D) → (∀ j : Fin t, z j ∈ L) →
      ∃ F : P →+* D,
        F.comp (algebraMap C P) = f ∧ IsDPMorphism δ η F ∧
        (∀ (j : Fin t), F (basis (Finsupp.single j 1)) = z j) ∧
        (∀ (α : Fin t →₀ ℕ),
          F (basis α) = ∏ j : Fin t, η.dpow (α j) (z j)) ∧
        ∀ G : P →+* D,
          G.comp (algebraMap C P) = f → IsDPMorphism δ η G →
          (∀ (j : Fin t), G (basis (Finsupp.single j 1)) = z j) → G = F

attribute [instance] OrdinaryPDPolynomialExtensionData.commRingP
  OrdinaryPDPolynomialExtensionData.algebraCP

/-- The ordinary divided-power polynomial extension exists.

Source: Stacks Project, Tag 07H5 (lemma-divided-power-polynomial-algebra), existence,
uniqueness and universal property.
(blueprint: lem-sfb-ordinary-pd-polynomial-extension).

Proof:
1. On the free module with basis e_α, extend the displayed binomial multiplication
   bilinearly. Associativity is the coordinatewise multinomial identity, symmetry
   gives commutativity, and e_0 is the unit. The positive basis span is an ideal.
2. For α ≠ 0 put c(n,α) = ∏j (nα_j)! / (n! ∏j (α_j!)^n). This is an integer:
   simultaneous permutation of n block labels acts freely on tuples of decompositions
   of labelled sets into blocks of sizes α_j. Repeated multiplication gives
   e_α^n = n! c(n,α) e_(nα). Over a torsion-free coefficient ring, apply
   lem-sfb-pd-torsionfree-factorial-criterion to obtain the augmentation structure θ,
   with θ_n(e_α) = c(n,α)e_(nα). In particular θ_n(X_j) = X_j^[n].
3. Take the torsion-free polynomial cover ℤ[T_c : c ∈ C] → C, using
   def-weil-pbc-mv-polynomial-ring. Its induced coefficientwise surjection has kernel
   consisting of expansions with coefficients in the coefficient kernel. Expansion
   by addition and scalar axioms shows its intersection with the positive ideal is
   stable: each positive-degree term has a positive power of a kernel coefficient.
   Apply lem-sfb-pd-surjective-descent to obtain θ over C with the same formulas.
4. The free basis implies flatness (lem-weil-pbc-projective-module-flat), so
   lem-sfb-pd-flat-extension gives divided powers on IP. Coefficientwise,
   IP ∩ P₊ = IP · P₊. The product-agreement and gluing assertions of
   lem-sfb-pd-glue-ideals give δ on K, extending γ and normalized on each X_j.
5. For any competing δ' and α ≠ 0, choose j with m = α_j > 0, write
   e_α = (∏k ≠ j X_k^[α_k]) δ'_m(X_j), and apply the scalar and composition
   axioms. Repeated basis multiplication gives δ'_n(e_α) = c(n,α)e_(nα).
   Thus δ' agrees with δ on I and every positive basis element. Scalar and addition
   axioms extend this equality to their ideal span K, proving uniqueness.
6. Define F(∑α a_α e_α) = ∑α f(a_α) ∏j η_(α_j)(z_j). Additivity and the
   constant formula give extension and the unit; the product axiom for η gives
   multiplicativity on basis pairs and hence on all finite sums. Positive monomials
   have a positive-index factor in L, so F(K) ⊆ L, and F(X_j) = z_j.
7. The scalar and composition axioms as in step 5 show preservation of divided powers
   on positive basis elements; on I it is the hypothesis on f. Scalar and addition
   axioms extend preservation to K. Any competing map G must send
   X_j^[r] = δ_r(X_j) to η_r(z_j). Multiplying these values determines G on every
   basis element; coefficient extension and additivity then force G = F.
-/
theorem ordinary_pd_polynomial_extension
    (C : Type u) [CommRing C] (I : Ideal C) (γ : DividedPowers I)
    (t : ℕ) (ht : 1 ≤ t) :
    Nonempty (OrdinaryPDPolynomialExtensionData.{u, w} C I γ t ht) := by
  sorry

end DividedPowers
