module

public import Sheaf.AlgebraicGeometry.AbelianVariety.PolarizationCalculusOverField
public import Mathlib.RingTheory.Adjoin.Polynomial.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Data.Real.Basic

import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Sheaf.AlgebraicGeometry.AbelianVariety.FieldExtension
import Sheaf.AlgebraicGeometry.SchemeRelativeAmpleBaseChange
import Sheaf.AlgebraicGeometry.AbelianVariety.TateActionSaturation
import Sheaf.AlgebraicGeometry.AbelianVariety.HomFiniteFree
import Sheaf.AlgebraicGeometry.AmpleOfAffineGeneratingLoci
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Sheaf.AlgebraicGeometry.AbelianVariety.PolarizationCalculus
import WeilConjectures.AlgebraicGeometry.AbelianVariety.Isogeny
import Sheaf.AlgebraicGeometry.AbelianVariety.LineBundleDegreeSquare
import Sheaf.AlgebraicGeometry.AbelianVariety.RationalTateCharpoly
import Mathlib.LinearAlgebra.Charpoly.Basic

/-! # Positive real spectrum of a comparison of ample polarizations

Source: Milne, Abelian Varieties, I Proposition 14.2, Theorem 14.3, Theorem 11.1,
and Proposition 10.20 (blueprint: lem-sfb-ample-polarization-positive-spectrum).

The algebra `E` is identified linearly with the recorded rational Hom space, with
unit and multiplication specified on pure tensors. All maps below are pinned by
composition or Poincare classifiers. Real scalar extension is written with the
real factor first, canonically exchanging the two factors of the node's tensor.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits MonoidalCategory MonObj
open scoped TensorProduct

namespace AlgebraicGeometry

open Scheme.Modules

/-- The comparison of two ample line polarizations is Rosati fixed and generates a
finite-dimensional commutative rational algebra whose real scalar extension is a
product of copies of the reals, with strictly positive comparison coordinates.
Source: Milne AV I Proposition 14.2 and Theorem 14.3, pp.61–62, Theorem 11.1, p.54,
and Proposition 10.20, pp.50–52
(blueprint: lem-sfb-ample-polarization-positive-spectrum).

Proof:
1. Pass to an algebraic closure (def-weil-algebraic-closure). Field extension preserves
abelian varieties and dimension (lem-sfb-abelian-field-extension) and ampleness
(lem-trf-scheme-relative-ample-base-change). The normalized Poincare universal property
(def-sfb-abelian-dual-poincare-datum) identifies duals and the classifiers after base change.
Tate faithfulness (lem-sfb-abelian-tate-action-saturation), after clearing denominators,
makes rational endomorphism base change injective.
2. Finite freeness of Hom (lem-sfb-abelian-hom-finite-free) makes E and its generated
subalgebra finite dimensional. The affine-locus criterion (lem-pc-ample-affine-loci-criterion)
and Rosati positivity (lem-sfb-rosati-trace-positive) give a positive definite symmetric
trace form. In dimension zero Tate faithfulness gives E = 0; take d = 0.
3. The alternating Weil pairings for L and M (lem-sfb-abelian-weil-pairing) show that
u is self-adjoint for the nondegenerate L pairing. The dagger formula from
lem-sfb-polarization-calculus-over-field and Tate faithfulness give dagger u = u.
4. Dagger fixes polynomials in u. Multiplication by u on C is symmetric for the positive
trace form. Choose a rational orthogonal basis
(lem-sfb-rational-symmetric-form-orthogonal-basis); its positive diagonal coefficients
remain positive over the reals. Apply lem-sfb-real-symmetric-orthonormal-eigenbasis.
5. Every element of the real extension is a polynomial in u. Evaluation at the distinct
real eigenvalues is injective, since the regular representation sends 1 to the element
itself, and surjective by Lagrange interpolation. This is the required algebra equivalence.
6. Clear the denominator of the rational inverse of lambda. Surjectivity of [n]
(lem-sc-mult-n-isogeny), torsion freeness of Hom, dual dimension
(lem-sfb-abelian-polarization-calculus), and lem-sfb-equal-dimension-isogeny-criterion
show that lambda is an isogeny.
7. Expand Q(T) = sum binomial(g,i) (L^i M^(g-i))/g! T^i using
lem-sfb-top-intersection-multilinear. The relative Tate determinant
(lem-sfb-isogeny-relative-tate-determinant) and the degree-square formula
(lem-sfb-abelian-line-bundle-degree-square) give P(n) = Q(n)^2/b^2 for all nonnegative
integers n, where b = (L^g)/g! > 0 and P is the rational characteristic polynomial of -u
(lem-sfb-abelian-tate-charpoly). Infinitely many n give the polynomial identity.
8. All mixed intersections are positive (lem-sfb-ample-mixed-intersection-positive),
so P(t) > 0 for real t >= 0. Cayley--Hamilton (lem-weil-cayley-hamilton-free-module)
and Tate faithfulness give P(-u) = 0. Each coordinate a of u therefore satisfies
P(-a) = 0, forcing a > 0. Injective base change descends the assertions to k. -/
theorem IsAbelianVariety.ample_polarization_positive_spectrum
    {k : Type u} [Field k] (A : Over (Spec (.of k)))
    [GrpObj A] [IsAbelianVariety A]
    (L M : A.left.Modules) [hL : L.IsInvertible] [hM : M.IsInvertible]
    (hLamp : IsAmple A.left L) (hMamp : IsAmple A.left M)
    (c : ∀ (B C F : Over (Spec (.of k)))
      [GrpObj B] [GrpObj C] [GrpObj F]
      [IsAbelianVariety B] [IsAbelianVariety C] [IsAbelianVariety F],
      abelianRationalHom B C →ₗ[ℚ]
        abelianRationalHom C F →ₗ[ℚ] abelianRationalHom B F)
    (hc : ∀ (B C F : Over (Spec (.of k)))
      [GrpObj B] [GrpObj C] [GrpObj F]
      [IsAbelianVariety B] [IsAbelianVariety C] [IsAbelianVariety F]
      (r s : ℚ) (f : abelianHom B C) (g : abelianHom C F),
      c B C F (r ⊗ₜ[ℤ] f) (s ⊗ₜ[ℤ] g) = (r * s) ⊗ₜ[ℤ] abelianHomComp f g)
    (D : AbelianDualPoincareDatum A)
    (φL φM : abelianHom A D.dual)
    (hφL : ClassifiesAbelianDifference D L (abelianHomMap φL))
    (hφM : ClassifiesAbelianDifference D M (abelianHomMap φM))
    (dQ : abelianRationalHom A A →ₗ[ℚ] abelianRationalHom D.dual D.dual)
    (hdQ : ∀ (r : ℚ) (b : abelianHom A A), ∃ db : abelianHom D.dual D.dual,
      Nonempty
        ((Scheme.Modules.pullback (abelianHomMap b ▷ D.dual).left).obj D.poincare ≅
          (Scheme.Modules.pullback (A ◁ abelianHomMap db).left).obj D.poincare) ∧
      dQ (r ⊗ₜ[ℤ] b) = r ⊗ₜ[ℤ] db)
    (invLambda : abelianRationalHom D.dual A)
    (hinv : c A D.dual A (abelianHomToRational φL) invLambda =
      abelianHomToRational (abelianHomId A))
    (hinv' : c D.dual A D.dual invLambda (abelianHomToRational φL) =
      abelianHomToRational (abelianHomId D.dual))
    (E : Type v) [Ring E] [Algebra ℚ E]
    (e : E ≃ₗ[ℚ] abelianRationalHom A A)
    (hone : e 1 = abelianHomToRational (abelianHomId A))
    (hmul : ∀ x y : E, e (x * y) = c A A A (e y) (e x))
    (u : E) (hu : e u = c A D.dual A (abelianHomToRational φM) invLambda)
    (dagger : E →ₗ[ℚ] E)
    (hdagger : ∀ x : E, e (dagger x) = c A D.dual A
      (c A D.dual D.dual (abelianHomToRational φL) (dQ (e x))) invLambda) :
    dagger u = u ∧ FiniteDimensional ℚ (Algebra.adjoin ℚ {u}) ∧
      ∃ (d : ℕ) (ρ : (ℝ ⊗[ℚ] Algebra.adjoin ℚ {u}) ≃ₐ[ℝ] (Fin d → ℝ)),
        ∀ i : Fin d, 0 < ρ (1 ⊗ₜ[ℚ] ⟨u, Algebra.self_mem_adjoin_singleton ℚ u⟩) i := by
  sorry

end AlgebraicGeometry
