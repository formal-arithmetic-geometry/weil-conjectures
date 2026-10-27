module

public import Sheaf.AlgebraicGeometry.AbelianVariety.PolarizationCalculus
public import Sheaf.AlgebraicGeometry.AbelianVariety.RationalHomTateAction
public import Sheaf.AlgebraicGeometry.IntersectionNumber
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import Mathlib.LinearAlgebra.Trace

import WeilConjectures.AlgebraicGeometry.Modules.Ample

/-! # Trace of an adjoint product and intersections

Source: Milne, Abelian Varieties, I Theorem 14.3, p.62, and Proposition 10.20,
pp.50–52 (blueprint: lem-sfb-abelian-trace-intersection).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory MonoidalCategory CartesianMonoidalCategory

namespace AlgebraicGeometry

/-- The trace/intersection identity, including nonvanishing of the denominator.
Positive dimension is written as `g + 1`; no endomorphism is required to be an
isogeny. The Poincare pullback identity specifies the actual dual of `f`.

Source: Milne AV I Theorem 14.3, p.62; Proposition 10.20, pp.50–52
(blueprint: lem-sfb-abelian-trace-intersection).

Proof plan:
1. Set `S = (L^(g+1) · A)` and `M = f*L`. Choose a very ample power of `L`
using def-sc-ample. By lem-sfb-projective-hilbert-polynomial-dimension its Hilbert
polynomial has degree `g+1`. By lem-sc-positive-ample-hilbert-degree and
 def-sc-hilbert-degree, `S` is positive. The coefficient definition
 def-sc-intersection-number identifies this Hilbert degree with `S`.
By lem-sfb-top-intersection-multilinear, the polynomial
`H(X) = sum_j choose(g+1,j) X^(g+1-j) (L^(g+1-j) M^j · A)` evaluates at every
integer `r` to `((L^r tensor M)^(g+1) · A)`. Its two leading coefficients are
`S` and `(g+1) (L^g M · A)`.
2. Put `v = mu fDual lambda f`. The pullback and tensor identities in
lem-sfb-abelian-polarization-calculus give
`phi_(L^r tensor M) = r lambda + fDual lambda f`.
By lem-sfb-abelian-line-bundle-degree-square for `L`, lambda is an isogeny of
degree `(S/(g+1)!)^2`.
3. By prop-av-tate-rank, the rational Tate module has dimension `2(g+1)`.
The componentwise action sk-def-av-tate and its rational-linear extension
preserve the displayed sums and compositions. Apply
lem-sfb-isogeny-relative-tate-determinant and
lem-sfb-abelian-line-bundle-degree-square to obtain
`det(r I + V(v)) = H(r)^2/S^2` for every integer `r`. Polynomial identity over
the characteristic-zero field of l-adic numbers gives the same identity in `X`.
4. Compare coefficients of `X^(2(g+1)-1)`: the determinant coefficient is the
ordinary trace def-weil-endomorphism-trace, while the other coefficient is
`2 S (g+1) (L^g M · A)/S^2`. Cancel `S`, which is nonzero by step 1.
The zero and non-isogeny cases of `f` were retained throughout. -/
theorem IsAbelianVariety.trace_adjoint_product_eq_intersection
    {k : Type u} [Field k] [IsAlgClosed k]
    (A : Over (Spec (.of k))) [GrpObj A] [IsAbelianVariety A]
    (g : ℕ)
    (hd : topologicalKrullDim A.left = (((g + 1 : ℕ) : ℕ∞) : WithBot ℕ∞))
    (D : AbelianDualPoincareDatum A)
    (L : A.left.Modules) [L.IsInvertible] (hL : IsAmple A.hom L)
    (lambda : A ⟶ D.dual) [IsMonHom lambda] (hlambda : ClassifiesAbelianDifference D L lambda)
    (mu : abelianRationalHom D.dual A)
    (hmulambda : IsAbelianVariety.rationalHomPrecomp lambda mu =
      abelianHomToRational (abelianHomId A))
    (hlambdamu : IsAbelianVariety.rationalHomPostcomp lambda mu =
      abelianHomToRational (abelianHomId D.dual))
    (f : A ⟶ A) [IsMonHom f]
    (fDual : D.dual ⟶ D.dual) [IsMonHom fDual]
    (hfDual : Nonempty
      ((Scheme.Modules.pullback (f ▷ D.dual).left).obj D.poincare ≅
        (Scheme.Modules.pullback (A ◁ fDual).left).obj D.poincare))
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : (ℓ : k) ≠ 0) :
    (@Scheme.Modules.selfIntersectionNumber k _ A.left ⟨A.hom⟩
      (IsAbelianVariety.toIsProper (A := A)) A.left inferInstance (𝟙 A.left)
        inferInstance (g + 1) hd L inferInstance) ≠ 0 ∧
      LinearMap.trace ℚ_[ℓ] (IsAbelianVariety.rationalTateModule ℓ A)
        (IsAbelianVariety.rationalHomTateMap ℓ
          (IsAbelianVariety.rationalHomPrecomp (f ≫ lambda ≫ fDual) mu)) =
        algebraMap ℚ ℚ_[ℓ]
          ((2 * (g + 1 : ℚ) *
            @Scheme.Modules.intersectionNumber k _ A.left ⟨A.hom⟩
              (IsAbelianVariety.toIsProper (A := A)) A.left inferInstance (𝟙 A.left)
              inferInstance (g + 1) hd
              (Fin.cons ((Scheme.Modules.pullback f.left).obj L)
                (fun _ : Fin g ↦ L))
              (fun j ↦ Fin.cases
                (by simpa only [Fin.cons_zero] using
                  (inferInstance : ((Scheme.Modules.pullback f.left).obj L).IsInvertible))
                (fun i ↦ by simpa only [Fin.cons_succ] using
                  (inferInstance : L.IsInvertible)) j)) /
            @Scheme.Modules.selfIntersectionNumber k _ A.left ⟨A.hom⟩
              (IsAbelianVariety.toIsProper (A := A)) A.left inferInstance (𝟙 A.left)
              inferInstance (g + 1) hd L inferInstance) := by
  sorry

end AlgebraicGeometry
