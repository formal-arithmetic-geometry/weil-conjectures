module

public import Sheaf.AlgebraicGeometry.AbelianVariety.DualPoincareDatum
public import Sheaf.AlgebraicGeometry.AbelianVariety.RationalHomTateAction
public import WeilConjectures.AlgebraicGeometry.Modules.VeryAmple
public import Mathlib.LinearAlgebra.Trace

import WeilConjectures.AlgebraicGeometry.AbelianVariety.Basic
import Sheaf.AlgebraicGeometry.NonzeroSectionIntegralCartier
import WeilConjectures.AlgebraicGeometry.EffectiveCartier
import Sheaf.AlgebraicGeometry.AbelianVariety.PolarizationCalculus
import Sheaf.AlgebraicGeometry.AbelianVariety.WeilPairing
import Sheaf.AlgebraicGeometry.AbelianVariety.TateActionSaturation
import Sheaf.AlgebraicGeometry.AbelianVariety.RationalTateCharpoly
import Sheaf.AlgebraicGeometry.AbelianVariety.TraceIntersection
import WeilConjectures.AlgebraicGeometry.Modules.Ample
import Sheaf.AlgebraicGeometry.IntersectionNumber
import WeilConjectures.AlgebraicGeometry.DensePoints
import Sheaf.AlgebraicGeometry.IntersectionEffectiveCartier
import Sheaf.AlgebraicGeometry.SnapperNumericalPolynomial

/-! # Positive Rosati trace pairing

Source: Milne, Abelian Varieties, I section 14, pp.61–62, Theorem 14.3;
section 11, p.53; Proposition 10.20, pp.50–52.
(blueprint: lem-sfb-rosati-trace-positive)

The rational Hom spaces use the canonical tensor symmetry to place the rational
factor first. Composition is in categorical order and is specified on pure tensors.
The dual and polarization maps are specified by the normalized Poincare family.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct

namespace AlgebraicGeometry

/-- An ample line polarization has a rational inverse, and its Rosati involution
has a symmetric positive rational trace form, compatible with every allowable Tate trace.

Source: Milne AV I section 14, pp.61–62, Theorem 14.3; section 11, p.53;
Proposition 10.20, pp.50–52 (blueprint: lem-sfb-rosati-trace-positive).

Proof plan:
1. Choose a very ample positive power L^r (def-sc-ample) and a nonzero coordinate
section. The variety is integral (lem-sc-abelian-variety-characterization), so its
zero scheme F is Cartier (lem-pc-nonzero-section-integral-cartier). The local
coefficient description identifies O(F) with L^r (def-pc-divisor-line-bundle).
The criterion lem-sfb-abelian-polarization-calculus makes phi_(L^r) = r lambda
an isogeny. A quasi-inverse h with both composites [n], n > 0, from
lem-sfb-simple-isogeny-decomposition gives mu = (r/n) h. Empty F is allowed
in dimension zero. Extend composition bilinearly on the actual tensor products.
2. Pullback duality is additive and contravariant (lem-sfb-abelian-weil-pairing).
Extend it rationally and define dagger by lambda, duality and mu in that order.
The inverse identities give rational linearity and reversal of multiplication.
The perfect Weil pairing composed with lambda is alternating and nondegenerate;
its adjoint identity gives dagger squared equal to the identity on Tate modules.
Clear denominators and use lem-sfb-abelian-tate-action-saturation to descend this
equality to rational homomorphisms.
3. In positive dimension define Tr(u) as minus the coefficient of degree 2g-1
of the rational polynomial from lem-sfb-abelian-tate-charpoly. The coefficient
of a determinant polynomial is minus the matrix diagonal sum
(def-weil-endomorphism-trace), so this realizes every Tate trace. The injective
rational embedding descends additivity and scalar linearity, and Tate rank 2g
gives Tr(1) = 2g. In dimension zero Tate faithfulness gives E = 0; use zero trace.
4. In a basis the adjoint is J^(-1) U^t J. Conjugation invariance and equality
of the diagonal sums of U and U^t give Tr(u dagger) = Tr(u). Thus
Tr(u dagger v) = Tr(v dagger u). Distributivity gives rational bilinearity.
5. For nonzero u clear denominators to n u = f with n > 0 and integral f != 0,
using Tate faithfulness for torsion-freeness. By
lem-sfb-abelian-trace-intersection, B(f,f) is 2g times the mixed intersection
(L^(g-1), f*L) divided by (L^g). The denominator is positive by
lem-sc-positive-ample-hilbert-degree and def-sc-intersection-number.
6. A nonzero f has a rational point x with f(x) != 0: otherwise density
(lem-pc-rational-points-dense), separatedness and reducedness force f = 0.
A hyperplane for L^r through 0 but not f(x) pulls back to a section of (f*L)^r
vanishing at 0 but not x. Its zero scheme H is nonempty Cartier by
lem-pc-nonzero-section-integral-cartier. By lem-sc-intersection-effective-cartier,
its dimension is g-1, L restricts amply, and its positive ample Hilbert degree
(lem-sc-positive-ample-hilbert-degree) is ((f*L)^r, L^(g-1)), including g = 1.
7. The polynomial definition def-sc-intersection-number and the total-degree
bound lem-sc-snapper-numerical-polynomial show symmetry and that replacing a
slot by its r-th tensor power multiplies the intersection by r. Thus the mixed
intersection in step 5 is positive. Divide the resulting B(f,f) > 0 by n^2
to obtain B(u,u) > 0. Dimension zero has no nonzero u. -/
theorem IsAbelianVariety.exists_rosati_trace_positive
    {k : Type u} [Field k] [IsAlgClosed k]
    (A : Over (Spec (.of k))) [GrpObj A] [IsAbelianVariety A]
    (L : A.left.Modules) [L.IsInvertible] (hL : IsAmple A.hom L) :
    ∃ c : ∀ (B C F : Over (Spec (.of k)))
        [GrpObj B] [GrpObj C] [GrpObj F]
        [IsAbelianVariety B] [IsAbelianVariety C] [IsAbelianVariety F],
        abelianRationalHom B C →ₗ[ℚ]
          abelianRationalHom C F →ₗ[ℚ] abelianRationalHom B F,
      (∀ (B C F : Over (Spec (.of k)))
        [GrpObj B] [GrpObj C] [GrpObj F]
        [IsAbelianVariety B] [IsAbelianVariety C] [IsAbelianVariety F]
        (r s : ℚ) (f : abelianHom B C) (g : abelianHom C F),
          c B C F (r ⊗ₜ[ℤ] f) (s ⊗ₜ[ℤ] g) =
            (r * s) ⊗ₜ[ℤ] abelianHomComp f g) ∧
      ∃ (D : AbelianDualPoincareDatum A) (lambda : abelianHom A D.dual)
        (d : abelianHom A A →+ abelianHom D.dual D.dual)
        (dQ : abelianRationalHom A A →ₗ[ℚ] abelianRationalHom D.dual D.dual),
        ClassifiesAbelianDifference D L (abelianHomMap lambda) ∧
        (∀ (f : abelianHom A A) (g : abelianHom D.dual D.dual),
          Nonempty
            ((Scheme.Modules.pullback (abelianHomMap f ▷ D.dual).left).obj D.poincare ≅
              (Scheme.Modules.pullback (A ◁ abelianHomMap g).left).obj D.poincare) ↔
            g = d f) ∧
        (∀ (r : ℚ) (f : abelianHom A A), dQ (r ⊗ₜ[ℤ] f) = r ⊗ₜ[ℤ] d f) ∧
        ∃ (mu : abelianRationalHom D.dual A)
          (dagger : abelianRationalHom A A →ₗ[ℚ] abelianRationalHom A A)
          (tr : abelianRationalHom A A →ₗ[ℚ] ℚ)
          (B : abelianRationalHom A A →ₗ[ℚ] abelianRationalHom A A →ₗ[ℚ] ℚ),
          c A D.dual A (abelianHomToRational lambda) mu =
            abelianHomToRational (abelianHomId A) ∧
          c D.dual A D.dual mu (abelianHomToRational lambda) =
            abelianHomToRational (abelianHomId D.dual) ∧
          (∀ v : abelianRationalHom A A,
            dagger v = c A D.dual A
              (c A D.dual D.dual (abelianHomToRational lambda) (dQ v)) mu) ∧
          Function.Involutive dagger ∧
          (∀ v w : abelianRationalHom A A,
            dagger (c A A A v w) = c A A A (dagger w) (dagger v)) ∧
          (∀ (ℓ : ℕ) [Fact ℓ.Prime], ℓ ≠ ringChar k →
            ∀ v : abelianRationalHom A A,
              algebraMap ℚ ℚ_[ℓ] (tr v) =
                LinearMap.trace ℚ_[ℓ] (IsAbelianVariety.rationalTateModule ℓ A)
                  (IsAbelianVariety.rationalHomTateMap ℓ v)) ∧
          tr (abelianHomToRational (abelianHomId A)) =
            (2 * IsAbelianVariety.dim A : ℕ) ∧
          (∀ v w : abelianRationalHom A A, B v w = tr (c A A A w (dagger v))) ∧
          (∀ v w : abelianRationalHom A A, B v w = B w v) ∧
          ∀ v : abelianRationalHom A A, v ≠ 0 → 0 < B v v := by
  sorry

end AlgebraicGeometry
