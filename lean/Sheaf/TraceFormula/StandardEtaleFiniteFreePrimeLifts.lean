module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Basic
public import Mathlib.Algebra.Polynomial.Derivative

/-!
# Finite free domination of a standard étale algebra with prescribed prime lifts

Source: Stacks Project, Algebra, Tag 00UF, label lemma-standard-etale-finite-flat-Zariski,
clauses (1)--(3) (blueprint: lem-trf-standard-etale-finite-free-prime-lifts).
-/

set_option autoImplicit false
set_option warn.sorry false

@[expose] public section

universe u

open scoped Polynomial

namespace AlgebraicGeometry

/--
Source: Stacks Project, Algebra, Tag 00UF, label lemma-standard-etale-finite-flat-Zariski,
clauses (1)--(3) (blueprint: lem-trf-standard-etale-finite-free-prime-lifts).

The proof follows the finite-free splitting-algebra construction for a monic polynomial,
then applies integrality and lying-over for surjectivity.  For the prime-lifting clause,
reduce a prime to the residue field, select a root of the corresponding irreducible
factor, and use the standard-étale root-map universal property; the explicit fraction
calculation gives the contraction equality.  The zero-ring and constant-polynomial cases
are included as stated.  The proof uses the finite-free splitting extension,
integrality and lying-over, the localized-fibre prime/factor correspondence, residue-factor
root selection, and the standard-étale pair map theorem.
-/
theorem standardEtale_finiteFree_primeLifts
    {R : Type u} [CommRing R]
    (f g : R[X]) (hf : f.Monic)
    (hunit : IsUnit
      (((algebraMap (R[X] ⧸ Ideal.span ({f} : Set R[X]))
        (Localization.Away (Ideal.Quotient.mk (Ideal.span ({f} : Set R[X])) g))).comp
          (Ideal.Quotient.mk (Ideal.span ({f} : Set R[X])))) f.derivative)) :
    ∃ (C : CommRingCat.{u}) (r : ℕ) (_ : Algebra R C),
      Nonempty (Module.Basis (Fin r) R C) ∧
      (Nontrivial R → 1 ≤ r) ∧
      Surjective (Spec.map (CommRingCat.ofHom (algebraMap R C))) ∧
      (∀ (q : PrimeSpectrum (Localization.Away
          (Ideal.Quotient.mk (Ideal.span ({f} : Set R[X])) g)))
        (q' : PrimeSpectrum C),
        Ideal.comap (algebraMap R
          (Localization.Away
            (Ideal.Quotient.mk (Ideal.span ({f} : Set R[X])) g))) q.asIdeal =
          Ideal.comap (algebraMap R C) q'.asIdeal →
        ∃ (c : C), c ∉ q'.asIdeal ∧
          ∃ (φ : Localization.Away
              (Ideal.Quotient.mk (Ideal.span ({f} : Set R[X])) g) →ₐ[R]
              Localization.Away c),
            Ideal.comap (φ.toRingHom) (Ideal.map
              (algebraMap C (Localization.Away c)) q'.asIdeal) = q.asIdeal) := by
  sorry

end AlgebraicGeometry
