module

public import Sheaf.AlgebraicGeometry.GroupScheme.Semisimple
public import Sheaf.AlgebraicGeometry.ToriMultiplicativeType
public import Sheaf.AlgebraicGeometry.FiniteDiagonalizableGroupScheme
public import Sheaf.AlgebraicGeometry.GroupScheme.AffineNormalQuotientGeometry
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
import Sheaf.AlgebraicGeometry.GroupScheme.SmoothConnectedDerivedSubgroup
import Sheaf.AlgebraicGeometry.GroupScheme.SemisimplePerfect
import Sheaf.AlgebraicGeometry.GroupScheme.AffineHomRationalPoints

/-! # Multiplication by a central torus and the derived subgroup

Source: Milne, Algebraic Groups (2017), Proposition 12.46(a),(b), pp.245--246;
Proposition 19.21(b),(c), pp.401--402; proof of Proposition 21.60, p.442.
(blueprint: lem-sfb-central-torus-semisimple-derived-product)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open scoped MonObj

namespace AlgebraicGeometry

/-- If a smooth connected affine group has a central split torus with semisimple fppf
quotient, its derived subgroup is semisimple. Multiplication from the torus times this
subgroup is faithfully flat with finite central diagonalizable kernel. The kernel is
identified with the scheme-theoretic intersection by the inverse diagonal, with its
inclusion in the product specified as an equality of morphisms.

Source: Milne, Algebraic Groups (2017), Proposition 12.46(a),(b), pp.245--246;
Corollary 21.50, p.440; Proposition 19.21(b),(c), pp.401--402; proof of Proposition
21.60(b) implies (c), p.442; Theorem 12.9(c), pp.233--234.
(blueprint: lem-sfb-central-torus-semisimple-derived-product)

Proof:
1. By lem-sfb-affine-normal-quotient-geometry the quotient projection q is faithfully
   flat with kernel R. By lem-sfb-smooth-connected-derived-subgroup, the derived groups
   of G and Q are smooth connected affine groups of finite type, and their F-points
   are the abstract commutator subgroups. By lem-sfb-semisimple-group-perfect, Q is
   perfect. The rational-point criterion lem-sfb-affine-group-homomorphism-image
   makes q surjective on F-points. Lift the entries in a product of commutators of
   Q(F) to G(F); their commutator product lies in D(F). Thus D(F) maps onto Q(F),
   and the same criterion makes D to Q faithfully flat.
2. By lem-sfb-central-torus-faithful-weight-blocks choose a faithful representation
   with nonzero R-weight blocks V_i, characters chi_i and dimensions n_i. The block
   determinants are characters of G, so are trivial on D by
   lem-sfb-smooth-connected-derived-subgroup. On K = R intersect D this gives
   chi_i raised to n_i equal to one as a morphism, over every scalar algebra.
3. The character tuple embeds K in the product of the groups mu_(n_i). In coordinates,
   F[K] is a quotient of F[z_i,z_i^{-1}]/(z_i^{n_i}-1). This algebra is spanned by
   the finitely many monomials with exponents between zero and n_i-1. Hence F[K]
   is finite-dimensional, including when the characteristic divides some n_i.
4. The kernel of D to Q is D times over G with R, by the quotient kernel square in
   lem-sfb-affine-normal-quotient-geometry. It is finite by step 3. Apply
   lem-sfb-semisimple-isogeny-source to the faithfully flat map D to Q to deduce
   that D is semisimple.
5. Centrality of R makes (t,d) to td a homomorphism. Given g in G(F), lift q(g) to
   d in D(F) by step 1. Then t = gd^{-1} lies in R(F), and g = td. Thus multiplication
   is onto on F-points. Its target is smooth, so
   lem-sfb-affine-group-homomorphism-image makes it faithfully flat.
6. Over every scalar algebra, td = 1 exactly when d = t^{-1}. Thus the inverse diagonal
   a to (a,a^{-1}) identifies K with the kernel. The maps use the pullback projections
   and inversion, so are morphisms, inverse functorially on all points. Both components
   are central, proving centrality in the product on every test scheme.
7. By lem-sfb-split-torus-subgroups-diagonalizable, the closed subgroup K of a split
   torus is D(M). Step 3 makes M finite. The isomorphism in step 6 therefore makes
   the kernel finite diagonalizable, equivalently finite of multiplicative type over F.
-/
theorem centralTorus_semisimple_derived_product {F : Type u} [Field F] [IsAlgClosed F]
    (G R Q : Grp (Over (Spec (.of F))))
    [Smooth G.X.hom] [ConnectedSpace G.X.left] [IsAffine G.X.left]
    [LocallyOfFiniteType G.X.hom] [QuasiCompact G.X.hom]
    (i : R ⟶ G) [IsClosedSubgroupScheme i.hom.hom]
    (hR : ∃ r : ℕ, Nonempty (R ≅ MultiplicativeType.splitTorus F r))
    (hcentral : ∀ (T : Over (Spec (.of F))) (t : T ⟶ R.X) (g : T ⟶ G.X),
      (t ≫ i.hom.hom) * g = g * (t ≫ i.hom.hom))
    (q : G ⟶ Q) (hquot : IsFppfGroupQuotient i q)
    (hQ : IsSemisimpleGroupScheme Q.X) :
    ∃ (D : Grp (Over (Spec (.of F)))) (d : D ⟶ G) (m : R.X ⊗ D.X ⟶ G.X) (_ : IsMonHom m),
      IsDerivedGroupScheme d.hom.hom ∧ IsSemisimpleGroupScheme D.X ∧
      m = (fst R.X D.X ≫ i.hom.hom) * (snd R.X D.X ≫ d.hom.hom) ∧
      m.left.appTop.hom.FaithfullyFlat ∧
      IsFinite (GrpObj.ker m).hom ∧
      IsFiniteDiagonalizableGroupScheme (GrpObj.ker m) ∧
      (∀ (T : Over (Spec (.of F))) (a : T ⟶ GrpObj.ker m)
        (x : T ⟶ R.X ⊗ D.X),
        (a ≫ GrpObj.kerι m) * x = x * (a ≫ GrpObj.kerι m)) ∧
      ∃ e : pullback i.hom.hom d.hom.hom ≅ GrpObj.ker m,
        e.hom ≫ GrpObj.kerι m =
          lift (pullback.fst i.hom.hom d.hom.hom)
            ((pullback.snd i.hom.hom d.hom.hom)⁻¹) := by
  sorry

end AlgebraicGeometry
