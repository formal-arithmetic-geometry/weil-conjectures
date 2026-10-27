module

public import Sheaf.RingTheory.PolynomialModuleGoodLocus
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.GroupTheory.MonoidLocalization.Away
public import Mathlib.Algebra.Module.LocalizedModule.Basic

import Mathlib.Algebra.Module.LocalizedModule.Exact

/-!
# Extensions of polynomial modules preserve the good locus

Source: Stacks Project, Algebra, Tag 051W (lemma-generic-flatness-locus-extension),
specialized to polynomial algebras; equations equation-flat-and-finitely-presented and
 equation-good-locus (blueprint: lem-sfb-polynomial-good-locus-extension).
-/

@[expose] public section

set_option autoImplicit false

universe u v₁ v₂ v₃

namespace MvPolynomial

/-- In a short exact sequence of polynomial modules, the intersection of the outer good
loci lies in the middle good locus. Freeness allows infinite and empty bases.

Source: Stacks Project, Algebra, Tag 051W (lemma-generic-flatness-locus-extension),
specialized to polynomial algebras (blueprint: lem-sfb-polynomial-good-locus-extension).

Proof:
1. For a prime in both outer loci, choose witnesses `a` and `b` outside the prime and put
   `f = a * b`. Primality gives that `f` is outside the prime.
2. Identify successive localizations at `a` and `b` with localization at `f`, using the
   fraction maps `(m/a^i)/b^j ↦ a^(k-i)b^(k-j)m/f^k` for `k ≥ i,j` and inverse
   `m/f^k ↦ (m/a^k)/b^k`. The fraction relations make these inverse maps well-defined.
   The maps commute with base scalars and the polynomial variables. Localizing polynomial
   coefficients at a constant agrees with the polynomial ring over the localized base,
   since the finitely many coefficient denominators have a common power denominator.
3. Localizing bases of the outer modules preserves freeness: localized coordinates give
   spanning, and clearing a common denominator in a finite relation gives independence.
   This applies to arbitrary, including empty, bases (def-weil-pbc-free-module).
4. Finite presentation of the outer modules persists after the further localization
   (lem-trf-localization-preserves-finite-presentation), now over the polynomial ring
   `B = R_f[x_1, ..., x_n]` by the identifications in step 2.
5. Localize the short exact sequence (lem-sc-p1-localization-short-exact). The localized
   maps commute with the variables, so it is short exact over both `R_f` and `B`.
6. Lift each basis vector of the localized quotient to the middle module. These lifts,
   together with the image of a basis of the localized submodule, form a basis: subtract
   the lifted quotient coordinates to prove spanning; apply the quotient map and then
   injectivity to prove independence (def-weil-pbc-free-module).
7. Identify the kernel of the localized surjection with the localized first module. Its
   finite presentation and that of the quotient imply finite presentation of the middle
   module over `B` (lem-trf-module-finite-presentation-of-kernel).
8. Thus `f` witnesses membership of the prime in the middle good locus. -/
theorem polynomialModuleGoodLocus_inter_subset_of_exact
    (R : Type u) [CommRing R] (n : ℕ)
    (M₁ : Type v₁) [AddCommGroup M₁] [Module (MvPolynomial (Fin n) R) M₁]
    (M₂ : Type v₂) [AddCommGroup M₂] [Module (MvPolynomial (Fin n) R) M₂]
    (M₃ : Type v₃) [AddCommGroup M₃] [Module (MvPolynomial (Fin n) R) M₃]
    (u : M₁ →ₗ[MvPolynomial (Fin n) R] M₂)
    (v : M₂ →ₗ[MvPolynomial (Fin n) R] M₃)
    (hu : Function.Injective u) (hv : Function.Surjective v) (h : Function.Exact u v) :
    polynomialModuleGoodLocus R n M₁ ∩ polynomialModuleGoodLocus R n M₃ ⊆
      polynomialModuleGoodLocus R n M₂ := by
  sorry

end MvPolynomial
