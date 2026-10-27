/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N7
-/
module

public import Sheaf.AlgebraicGeometry.StackPolynomialReesData
public import Sheaf.AlgebraicGeometry.StackQcqsMorphism

import Sheaf.AlgebraicGeometry.StackQcohAbelian
import Mathlib.RingTheory.ReesAlgebra

/-! # Polynomial sections and the graded ideal-power presentation on a stack

Source: Alper, Adequate moduli spaces and geometrically reductive group schemes,
Lemma 5.2.1, p.507, and Lemma 4.1.8, p.503
(blueprint: lem-sfb-stack-polynomial-rees-calculus).

The system gives every small-variable polynomial algebra and the Rees presentation
for every generating family. All algebra maps are unital, including degree zero.
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open AlgebraicGeometry

namespace CategoryTheory

/-- Polynomial sections and the Rees presentation, without any Noetherian or
finite-generation assumption. Source: Alper, proofs of Lemmas 4.1.8 and 5.2.1
(blueprint: lem-sfb-stack-polynomial-rees-calculus).

Proof:
1. For each small L, take the coproduct of copies of B indexed by finitely supported
   exponent functions L →₀ ℕ (lem-sfb-stack-qcoh-direct-sums). Define multiplication
   on the α,β summands using multiplication in B and the α+β summand. The unit is
   the zero-exponent summand. Tensor products are quasi-coherent by
   lem-sfb-stack-qcoh-flat-atlas-exactness. Scheme restriction identifies this with
   ordinary polynomial convolution (lem-sfb-stack-quasi-coherent-scheme-restriction,
   def-weil-pbc-mv-polynomial-ring). A faithful smooth atlas detects the ring identities.
2. Quasi-compactness of p gives a quasi-compact source, by its identity affine base
   test (def-sfb-stack-qcqs-morphism). The direct-sum comparison of global sections
   identifies polynomial coefficients; multiplication agrees on every summand.
   Coefficient homomorphisms commute with this construction, giving naturality.
3. A sheaf-surjective coefficient map lifts finitely many polynomial coefficients
   after finitely many refinements of fppf covers. Thus its polynomial map is locally
   surjective; no surjectivity of global sections is claimed.
4. In the abelian category QCoh (lem-sfb-stack-qcoh-abelian), take the image of
   the map from the coproduct of copies of B given by multiplication by a_j.
   Smooth exact restriction (lem-sfb-stack-smooth-qcoh-exact) identifies this image
   with the extended ideal. Its cokernel is B/J and is quasi-coherent by
   lem-sfb-stack-qcoh-flat-atlas-exactness; the ideal property gives the quotient algebra.
5. In degree m take the image of the analogous coproduct indexed by monomials of
   total degree m, with coefficient maps multiplication by a^α. Smooth exactness
   identifies it with J^m. Degree zero is B, and factoring a positive-degree
   monomial by one generator gives J^(m+1) = J J^m. Faithful atlas restriction
   detects these equalities; it does not assert inclusions on nonflat tests.
6. Take the coproduct of all degree pieces, including zero. Their products give
   the graded algebra. Smooth restrictions identify it with Mathlib reesAlgebra
   (def-nagata-rees-algebra). Define q on each monomial by multiplication by a^α
   in degree |α|. This fixes the coefficient identity and x_j ↦ a_j T.
7. The map in each degree is the epimorphism onto the image just defined.
   lem-sfb-stack-qcoh-flat-atlas-exactness makes it a local sheaf surjection.
   Every section of the coproduct is locally a finite sum, so a common refinement
   lifts its finitely many homogeneous pieces and proves surjectivity of q.
8. Apply lem-sfb-stack-qcoh-direct-sums to the powers. Global sections of each
   QCoh monomorphism inject, since sections are maps from O_X. The direct sum
   therefore embeds coefficientwise in B[T], with the stated multiplication and
   image criterion. The definition of q gives precisely finite polynomial
   evaluation at a_j T. No absolute diagonal separation is used. -/
theorem exists_moduliPolynomialReesCalculus {k : Type u} [Field k]
    {P : Type u} [CommRing P] [Algebra k P]
    (X : BasedCategory.{v, w} (Over (Spec (.of k)))) (hX : IsAlgebraicModuliStack X)
    (p : BasedFunctor X (discreteModuli
      (yoneda.obj (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k P)))))))
    (_hpqc : IsQuasiCompactAlgebraicModuliMap.{u, v, w, u, u + 1, 0, 0} p)
    (_hpqs : IsQuasiSeparatedAlgebraicModuliMap p) :
    ∃ polynomial : ∀ L : Type (max (u + 1) v w), ModuliPolynomialSystem X hX.1.1 L,
      ∀ (B : ModuliAlgebraSheaf X hX.1.1) (hB : IsQuasicoherentModuliAlgebra B)
        (J : Type (max (u + 1) v w)) (I : Ideal P) (a : J → P),
        Ideal.span (Set.range a) = I →
          Nonempty (ModuliReesPresentation p B hB J I a (polynomial J)) := by
  sorry

end CategoryTheory
