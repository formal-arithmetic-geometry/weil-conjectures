module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import WeilConjectures.RingTheory.ColimitFinitelyPresentedAlgebras
import WeilConjectures.RingTheory.FilteredColimitAlgebrasTensorElementwise

/-!
# Finite-presentation approximation of a missing fibre

Source: Stacks Project, `limits.tex`, Tag 05BD, Lemma `lemma-separate`,
specialized to an affine base and the polynomial quotients in its proof
(blueprint: lem-sfb-missing-fibre-finite-presentation-approximation).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A closed subscheme missing a fibre admits an affine finite-presentation approximation.

Source: Stacks Project, `limits.tex`, Tag 05BD, Lemma `lemma-separate` and its proof
(blueprint: lem-sfb-missing-fibre-finite-presentation-approximation).

Proof, following the seven steps of the node:
1. Choose an affine neighbourhood V = Spec B of t. Quasi-compactness of f over Spec A
   gives a finite affine cover U_i = Spec C_i of X
   (lem-pqf-finite-affine-cover-qc-open). The affine fibre-product formula
   (lem-weil-pbc-fibre-product-affine-spectra) identifies the restrictions of Z with
   Spec D_i for D_i = (C_i tensor_A B)/I_i. Their fibres at t are empty.
2. Use lem-weil-pbc-fibre-ring-localization-quotient and the empty-family case of
   lem-weil-pbc-spec-basic-opens-unit-ideal-quasi-compact to see that each fibre ring
   is zero. Clearing denominators gives x_i + sum_j f_ij c_ij = g_i, with x_i in I_i,
   f_ij in the prime q of t, and g_i outside q. Empty sums cause no exception.
3. Apply lem-weil-pbc-algebra-colimit-fp-algebras-over-it to the set of explicit
   finite polynomial quotients over A. It presents B as a small filtered colimit of
   such algebras B_lambda, in a common universe containing the finitely many C_i.
4. Apply lem-weil-pbc-filtered-colimit-algebras-tensor-elementwise to lift the finitely
   many coefficients and tensor elements. Filteredness gives one common stage.
   The inverse-image prime q_lambda contains the lifted f_ij and avoids the lifted g_i.
5. The eventual-zero clause of that same tensor-colimit lemma imposes the finitely
   many relations at a later common stage. Ring-homomorphism transition maps preserve
   all relations already imposed; injectivity of stage maps is unnecessary.
6. Set T' = Spec B_lambda and a = Spec(B_lambda to B). This is over Spec A.
   The morphism Z_V to X_{T'} is affine by lem-weil-pbc-morphism-affine-schemes-affine,
   lem-weil-pbc-affine-morphism-permanence and lem-weil-pbc-affine-composition.
   Take its closed scheme-theoretic image using lem-weil-pbc-scheme-image-qc-kernel.
   Its ideal on the i-th affine chart is the kernel of C_i tensor_A B_lambda to D_i,
   hence contains the lifted x_i.
7. In the fibre at a(t), each lifted x_i and f_ij vanishes. The descended relation
   kills g_i, which is invertible since it avoids q_lambda
   (def-weil-pbc-localization-at-prime). Every fibre chart is therefore empty.
   The scheme-image factorization gives the stated containment of underlying images.
   No quasi-separatedness or finite-type hypothesis on X or T is used.
-/
theorem exists_missingFibre_finitePresentationApproximation
    (A : Type u) [CommRing A] {X T Z : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of A)) [QuasiCompact f]
    (g : T ⟶ Spec (CommRingCat.of A)) (t : T)
    (i : Z ⟶ pullback f g) [IsClosedImmersion i]
    (ht : IsEmpty ((i ≫ pullback.snd f g).fiber t)) :
    ∃ (V : T.Opens) (htV : t ∈ V) (r m : ℕ)
      (q : Fin m → MvPolynomial (Fin r) A)
      (a : V.toScheme ⟶ Spec (CommRingCat.of
        (MvPolynomial (Fin r) A ⧸ Ideal.span (Set.range q))))
      (ha : a ≫ Spec.map (CommRingCat.ofHom
        (algebraMap A (MvPolynomial (Fin r) A ⧸ Ideal.span (Set.range q)))) = V.ι ≫ g)
      (Z' : Scheme.{u})
      (i' : Z' ⟶ pullback f (Spec.map (CommRingCat.ofHom
        (algebraMap A (MvPolynomial (Fin r) A ⧸ Ideal.span (Set.range q)))))),
      IsAffineOpen V ∧ IsClosedImmersion i' ∧
        IsEmpty ((i' ≫ pullback.snd f (Spec.map (CommRingCat.ofHom
          (algebraMap A (MvPolynomial (Fin r) A ⧸ Ideal.span (Set.range q)))))).fiber
            (a ⟨t, htV⟩)) ∧
        Set.range (pullback.map (i ≫ pullback.snd f g) V.ι f
          (Spec.map (CommRingCat.ofHom
            (algebraMap A (MvPolynomial (Fin r) A ⧸ Ideal.span (Set.range q)))))
          (i ≫ pullback.fst f g) a g
          (by simp only [Category.assoc, pullback.condition]) ha.symm) ⊆ Set.range i' := by
  sorry

end AlgebraicGeometry
