module

public import Sheaf.AlgebraicGeometry.AbelianVariety.PolarizationCalculus
public import Sheaf.AlgebraicGeometry.IntersectionNumber

/-! # Degree of a line-bundle homomorphism from its top intersection

Source: Milne, Abelian Varieties, Chapter I, Theorem 11.1(a),(b), printed p.54,
with the zero-degree convention preceding Theorem 10.9, printed p.46.
(blueprint: lem-sfb-abelian-line-bundle-degree-square)
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- For an arbitrary invertible module on a positive-dimensional abelian variety, the
zero-extended degree of its homomorphism to the dual is the square of its top self-intersection
number divided by the dimension factorial. The dual datum and the classifying predicate are
those of `lem-sfb-abelian-polarization-calculus`; no ampleness or isogeny hypothesis is imposed.
The conditional uses the existing kernel-coordinate-algebra degree for isogenies and zero
otherwise, including homomorphisms with positive-dimensional kernel.

Source: Milne, Abelian Varieties, I, Theorem 11.1(a),(b), printed p.54, and the degree
convention preceding Theorem 10.9, printed p.46.
(blueprint: lem-sfb-abelian-line-bundle-degree-square)

Proof plan:
1. Put c = chi(A,N). By `lem-sfb-abelian-euler-tensor-homogeneity`, the Euler
characteristic of N to any integer tensor power m is m^g c. Thus the Euler function of
N to the powers n_1,...,n_g tensored together is c (n_1 + ... + n_g)^g.
2. Apply `def-sc-intersection-number` to the identity closed immersion of A and g copies
of N. Equality on the integer lattice determines a polynomial over Q, by the univariate
infinite-root argument in each variable. Its coefficient of n_1 ... n_g is g! c:
each of the g factors contributes a different variable, in g! possible orders. Hence
(N^g . A) = g! c and c = (N^g . A)/g!, since g! is nonzero in Q.
3. By `lem-sfb-abelian-euler-degree-square`, the zero-extended kernel degree of the same
classifying homomorphism is c^2. This includes non-isogenies, without assuming ampleness.
4. Cast the integer degree equality into Q and substitute the expression for c from step 2.
-/
theorem IsAbelianVariety.line_bundle_degree_square
    {k : Type u} [Field k] [IsAlgClosed k]
    (A : Over (Spec (.of k))) [GrpObj A] [IsAbelianVariety A]
    (g : ℕ) (_hg : 1 ≤ g)
    (hA : topologicalKrullDim A.left = ((g : ℕ∞) : WithBot ℕ∞))
    (D : AbelianDualPoincareDatum A) (N : A.left.Modules) [N.IsInvertible]
    (φ : A ⟶ D.dual) [IsMonHom φ] (_hφ : ClassifiesAbelianDifference D N φ) :
    @ite ℚ (IsIsogeny φ) (Classical.propDecidable _) (isogenyDegree φ : ℚ) 0 =
      (@Scheme.Modules.selfIntersectionNumber k _ A.left ⟨A.hom⟩
        (inferInstance : IsProper A.hom)
        A.left inferInstance (𝟙 A.left) inferInstance g hA N inferInstance /
        (Nat.factorial g : ℚ)) ^ 2 := by
  sorry

end AlgebraicGeometry
