/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q84
-/
module

public import WeilConjectures.AlgebraicGeometry.AbelianVariety.Basic
public import WeilConjectures.AlgebraicGeometry.GroupScheme.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
import WeilConjectures.AlgebraicGeometry.AbelianVariety.Projective
import WeilConjectures.AlgebraicGeometry.Modules.VeryAmple
import Sheaf.AlgebraicGeometry.IntersectionNumber
import WeilConjectures.AlgebraicGeometry.Modules.Ample
import Sheaf.AlgebraicGeometry.TopIntersectionPullback
import WeilConjectures.AlgebraicGeometry.AbelianVariety.Isogeny
import WeilConjectures.AlgebraicGeometry.AbelianVariety.Cube
import Mathlib.RingTheory.Localization.BaseChange
import WeilConjectures.AlgebraicGeometry.Modules.Invertible

/-! # Isogeny degree on finite rational endomorphism subspaces

Source: Milne, Abelian Varieties, Chapter I, Remark 10.11 and Proposition 10.13,
printed pp.47–48; the degree convention preceding Theorem 10.9, printed p.46
(blueprint: lem-sfb-abelian-degree-polynomial).

The additive group `Additive (Grp.mk A ⟶ Grp.mk A)` is the group of group-scheme
endomorphisms, with pointwise addition. We put the rational factor first in its
rationalization, using the canonical tensor symmetry to identify this with End(A) ⊗ ℚ.
-/

@[expose] public section

universe u

open CategoryTheory MonObj
open scoped TensorProduct

namespace AlgebraicGeometry

/-- Degree, extended by zero away from isogenies, extends to rational endomorphisms and
is homogeneous polynomial of degree twice the dimension on every finite rational subspace.
Zero polynomials are allowed, including on the zero subspace.

Source: Milne, Abelian Varieties, Chapter I, Remark 10.11 and Proposition 10.13,
printed pp.47–48; the degree convention on printed p.46
(blueprint: lem-sfb-abelian-degree-polynomial).

Proof:
1. Choose an ample H by lem-sc-abelian-variety-projective and symmetrize it to N by
   lem-sc-ample-tensor. The variety is geometrically integral by
   lem-sc-abelian-variety-characterization. The top intersection c = (N^g . A) is positive
   by lem-sc-positive-ample-hilbert-degree and the Hilbert-degree coefficient formula.
   By lem-sfb-equal-dimension-isogeny-criterion, lem-sfb-top-intersection-pullback and
   lem-sc-isogeny-degree, ((a^* N)^g . A) = c d(a), also for nonisogenies, when both
   sides vanish.
2. lem-sc-mult-n-pullback and lem-sfb-top-intersection-multilinear give
   d(n a) = n^(2g) d(a). Symmetry gives d(-a) = d(a); the constant zero map pulls N
   back to a trivial module, whose top intersection vanishes because g > 0.
3. By lem-sfb-rational-tensor-fractions write v = j(a)/n, n > 0, and set
   d0(v) = d(a)/n^(2g). For two such fractions there is c' > 0 with c' m a = c' n b.
   Step 2 makes the two values equal. This also gives d0(j(a)) = d(a) and
   d0(t v) = t^(2g) d0(v) for every rational t, including zero.
4. Pull thm-sc-theorem-of-cube back along (n a + b, a, a). In the additive group of
   invertible-module classes put C_n = [(n a + b)^* N] and B = [(2a)^* N] - 2[a^* N].
   The seven terms give C_(n+2) - 2 C_(n+1) + C_n = B. Two-sided induction gives
   C_n = binomial(n,2) B + n C_1 - (n-1) C_0 for every integer n.
5. Expand its g-fold intersection using lem-sfb-top-intersection-multilinear and divide
   by c. This gives Q_(a,b)(T) of degree at most 2g with Q_(a,b)(n) = d(n a + b).
   Step 2 gives Q_(a,m b)(m T) = m^(2g) Q_(a,b)(T), first at all integers and then as
   a polynomial identity. Fractions and a common denominator therefore show that
   t ↦ d0(t v + w) is polynomial on ℚ of degree at most 2g for every v,w.
6. Apply lem-sfb-bounded-line-polynomial-interpolation to obtain a polynomial in every
   ordered finite basis, including the empty basis, with total degree at most 2g.
7. Step 3 gives P(t x) = t^(2g) P(x). Polynomial determination by rational values,
   also in the extra variable t, and coefficient comparison imply that every nonzero
   monomial has degree 2g. Thus P(0) = 0. For an isogeny the kernel has positive
   order: it contains the identity and its finite coordinate algebra has nonzero unit.
   Hence its degree is a positive integer, and step 3 identifies it with d0(j(a)). -/
theorem IsAbelianVariety.exists_degree_polynomial
    {k : Type u} [Field k] (A : Over (Spec (.of k))) [GrpObj A]
    [IsAbelianVariety A] (hg : 0 < IsAbelianVariety.dim A) :
    ∃ (d : Additive (Grp.mk A ⟶ Grp.mk A) → ℚ)
      (d0 : ℚ ⊗[ℤ] Additive (Grp.mk A ⟶ Grp.mk A) → ℚ),
      (∀ a : Additive (Grp.mk A ⟶ Grp.mk A),
        (IsIsogeny a.toMul.hom.hom → d a = (isogenyDegree a.toMul.hom.hom : ℚ)) ∧
        (¬ IsIsogeny a.toMul.hom.hom → d a = 0)) ∧
      (∀ a : Additive (Grp.mk A ⟶ Grp.mk A), d0 (1 ⊗ₜ[ℤ] a) = d a) ∧
      (∀ (v : ℚ ⊗[ℤ] Additive (Grp.mk A ⟶ Grp.mk A)) (n : ℕ), 0 < n →
        ∀ a : Additive (Grp.mk A ⟶ Grp.mk A),
          n • v = 1 ⊗ₜ[ℤ] a → d0 v = ((n : ℚ) ^ (2 * IsAbelianVariety.dim A))⁻¹ * d a) ∧
      (∀ (V : Submodule ℚ (ℚ ⊗[ℤ] Additive (Grp.mk A ⟶ Grp.mk A)))
        [FiniteDimensional ℚ V] (r : ℕ) (e : Module.Basis (Fin r) ℚ V),
        ∃ P : MvPolynomial (Fin r) ℚ,
          P.IsHomogeneous (2 * IsAbelianVariety.dim A) ∧
          (∀ x : Fin r → ℚ, d0 (V.subtype (∑ i : Fin r, x i • e i)) =
            MvPolynomial.eval x P) ∧
          MvPolynomial.eval (0 : Fin r → ℚ) P = 0) ∧
      (∀ a : Additive (Grp.mk A ⟶ Grp.mk A), IsIsogeny a.toMul.hom.hom →
        d0 (1 ⊗ₜ[ℤ] a) = (isogenyDegree a.toMul.hom.hom : ℚ) ∧
          0 < isogenyDegree a.toMul.hom.hom) := by
  sorry

end AlgebraicGeometry
