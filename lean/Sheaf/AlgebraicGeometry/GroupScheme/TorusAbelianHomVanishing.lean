module

public import WeilConjectures.AlgebraicGeometry.AbelianVariety.Defs
public import Sheaf.AlgebraicGeometry.ToriMultiplicativeType
import Sheaf.AlgebraicGeometry.MultiplicativeTypeLargestSubtorus
import Sheaf.AlgebraicGeometry.GroupScheme.HomomorphismFactorization
import Sheaf.AlgebraicGeometry.GroupScheme.AffineNormalQuotientGeometry
import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Reduced
import Sheaf.AlgebraicGeometry.ProperReducedGlobalSectionsProduct
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
import Mathlib.AlgebraicGeometry.Pullbacks

/-! # No homomorphisms between split tori and abelian varieties

Source: Milne, Algebraic Groups (2017), Proposition 8.1(b) and Example 8.4,
p.149; Section 8(e), p.151; Theorem 5.39, pp.108--109
(blueprint: lem-sfb-torus-abelian-hom-vanishing).

The zero homomorphism is written as the structure map followed by the target's
identity section. Equalities are equalities of morphisms over Spec k, hence of
scheme morphisms, rather than just equalities on k-points.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- Every homomorphism between a split torus and an abelian variety, in either
 direction, is the zero homomorphism, including the rank-zero torus.
Source: Milne, Algebraic Groups (2017), Proposition 8.1(b), Example 8.4, p.149,
Section 8(e), p.151, and Theorem 5.39, pp.108--109
(blueprint: lem-sfb-torus-abelian-hom-vanishing).

Proof:
1. The split torus T is affine and of finite type by its Laurent coordinates and
   the affine fibre-product formula (lem-weil-pbc-fibre-product-affine-spectra).
   It is smooth and connected by lem-sfb-multiplicative-type-largest-subtorus,
   and separated by lem-weil-pbc-affine-source-morphism-separated. The same
   assertions hold for rank zero. A is proper, smooth and connected by definition.
2. For f : T -> A, lem-sfb-algebraic-group-homomorphism-factorization gives a
   quotient q : T -> I followed by a closed immersion i : I -> A. Its kernel N
   is affine: its inclusion is affine by def-weil-closed-immersion, and apply
   lem-weil-pbc-affine-morphism-permanence. The quotient geometry theorem
   lem-sfb-affine-normal-quotient-geometry makes I affine, smooth and connected;
   no smoothness of N is required. Quotient uniqueness identifies the two models.
3. The closed immersion makes I proper (lem-weil-pbc-closed-immersion-proper).
   Smoothness makes I reduced (sbc-lem-smooth-geometrically-reduced). Its identity
   section makes I nonempty. Apply
   lem-weil-pbc-proper-reduced-algclosed-global-sections-product to get Gamma(I)=k.
4. Since I is affine, lem-weil-pbc-morphism-into-affine-scheme identifies its
   identity map with its structure map followed by its identity section: their
   k-algebra maps on global sections are both the identity of k. Substitution in
   f=q followed by i, using preservation of identity sections and structure maps,
   gives f equal to the zero homomorphism as an actual scheme morphism.
5. For g : A -> T, the same smoothness and constant-global-sections theorems
   give Gamma(A)=k. Since T is affine, the affine-target bijection expresses g
   as the structure map followed by a k-point c of T. Composing with the identity
   section of A shows c is the identity of T, since g is a homomorphism.
   Thus g is zero as well, and both Hom groups are trivial. -/
theorem torus_abelian_hom_vanishing (k : Type u) [Field k] [IsAlgClosed k]
    (A : Over (Spec (.of k))) [GrpObj A] [IsAbelianVariety A] (r : ℕ) :
    (∀ (f : (MultiplicativeType.splitTorus k r).X ⟶ A) [IsMonHom f],
      f = CartesianMonoidalCategory.toUnit _ ≫ MonObj.one) ∧
    (∀ (g : A ⟶ (MultiplicativeType.splitTorus k r).X) [IsMonHom g],
      g = CartesianMonoidalCategory.toUnit _ ≫ MonObj.one) := by
  sorry

end AlgebraicGeometry
