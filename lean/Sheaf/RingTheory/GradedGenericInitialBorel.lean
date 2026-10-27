module

public import Sheaf.RingTheory.GradedLexInitialIdeal
public import Mathlib.RingTheory.Nullstellensatz
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Order.WellFoundedSet

/-! # Generic graded initial ideals and triangular substitutions

Source: generic-coordinate input recalled in Bierstone--Milman 1997, §8 and before
Theorem 9.6; Bayer--Stillman 1987, Proposition 1, with the least fixed-degree
lexicographic convention (blueprint: lem-trf-graded-generic-initial-borel).
The affine open `U` represents the required open by intersection with the nonzero-determinant
locus. A point over the algebraic closure expresses geometric nonemptiness.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u

namespace MvPolynomial

/-- Generic graded initial ideals are fixed by the indicated triangular substitutions.
Source: BM 1997, §8 and before Theorem 9.6; Bayer--Stillman 1987, Proposition 1
(blueprint: lem-trf-graded-generic-initial-borel).

Proof plan (the node's direct finite-matrix argument):
1. For no variables, the zero ideal, or the unit ideal, use the whole general linear group.
2. Row elimination in each finite homogeneous piece identifies its least monomials with
its pivot columns. Multiplication by monomials makes the set of pivot exponents upward
closed, and the initial ideal has the same dimension in each degree as the original ideal.
3. Apply the independent generic matrix over the rational function field. Dickson finiteness
(lem-trf-monomial-upper-set-finite-basis) gives finitely many minimal pivot exponents.
4. Normalize homogeneous witnesses for these generators and clear their finitely many
rational denominators together with the determinant. Their nonvanishing defines one
geometrically nonempty open for all degrees. Specializing the witnesses gives inclusion
of the fixed monomial ideal in every initial ideal on this open; equality of degreewise
dimensions gives equality.
5. Characteristic zero makes the ground field infinite, so choose a rational point of the
open. In degree q, its pivot minor gives rational normalized rows regular at that point.
6. For i < j, choose weights (q+1)^(n-h) increasing with lexicographic exponent in degree q.
Conjugate the transvection by the diagonal one-parameter substitution; the conjugate tends
to the identity. Its product with the chosen point stays regular at parameter zero.
7. Scale each pivot row by its pivot weight. The tails vanish at zero, leaving the pivot
monomials. The transvection applied to the fixed scaled rows leaves the transvection of
those monomials. These two families span the same space over the rational function field.
8. An invertible minor at zero makes their change-of-basis matrix regular there. Reduction
gives inclusion of the two limiting degree spaces; equal dimensions give equality.
9. Apply this in every positive degree and use the trivial degree-zero case. The open and
the monomial ideal are fixed throughout, although the weights depend on the degree. -/
theorem gradedGenericInitialBorel {L : Type u} [Field L] [CharZero L] (n : ℕ)
    (J : Ideal (MvPolynomial (Fin n) L))
    (hJ : ∀ p ∈ J, ∀ q : ℕ, homogeneousComponent q p ∈ J) :
    ∃ (U : TopologicalSpace.Opens (PrimeSpectrum (MvPolynomial (Fin n × Fin n) L)))
      (B : Ideal (MvPolynomial (Fin n) L)),
      (∃ S : Set (Fin n →₀ ℕ),
        B = Ideal.span ((fun α : Fin n →₀ ℕ ↦ monomial α (1 : L)) '' S)) ∧
      (∃ g : Matrix (Fin n) (Fin n) (AlgebraicClosure L),
        g.det ≠ 0 ∧ pointToPoint (k := L) (fun ij : Fin n × Fin n ↦ g ij.1 ij.2) ∈ U) ∧
      (∀ g : Matrix (Fin n) (Fin n) L, g.det ≠ 0 →
        pointToPoint (k := L) (fun ij : Fin n × Fin n ↦ g ij.1 ij.2) ∈ U →
        gradedLexInitialIdeal (J.map
          (aeval (fun i ↦ ∑ j : Fin n, C (g i j) * X j)).toRingHom) = B) ∧
      ∀ (i j : Fin n), i < j → ∀ c : L,
        B.map (aeval (fun h : Fin n ↦
          if h = i then X i + C c * X j else X h)).toRingHom = B :=
  sorry

end MvPolynomial
