module

public import Sheaf.AlgebraicGeometry.ReductiveTorusCentralizerTerminology
import Sheaf.AlgebraicGeometry.SmoothAmbientNormalityGeometric
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

/-! # Connected normal subgroups of reductive groups

Source: Milne, Algebraic Groups (2017), Corollary 21.53, printed p.441, and
Section 6.46, printed p.135 (blueprint: lem-sfb-connected-normal-subgroup-reductive).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A smooth connected closed normal subgroup of a reductive group is reductive.
Source: Milne, Algebraic Groups (2017), Corollary 21.53, printed p.441
(blueprint: lem-sfb-connected-normal-subgroup-reductive).

Proof:
1. Write the affine group G as Spec A. Finite type makes A a finitely generated
   F-algebra (lem-weil-pbc-lft-affine-pairs). The closed subgroup M is Spec (A/I)
   (def-weil-closed-immersion), hence affine of finite type since the images of
   generators of A generate A/I (def-weil-finite-type-morphism). Apply
   lem-sfb-unipotent-radical-existence to the smooth connected group M to obtain
   its largest smooth connected closed normal unipotent subgroup U. The composite
   inclusion U -> M -> G is closed, and U is affine of finite type.
2. For g in G(F), normality of M gives an automorphism c_g of M. The subgroup
   c_g(U) is closed, smooth and connected. It is normal in M because
   m c_g(u) m^{-1} = c_g(c_g^{-1}(m) u c_g^{-1}(m)^{-1}) on every F-algebra.
   Transporting a faithful representation of U along c_g^{-1} proves unipotence
   with the same geometric matrices (def-sfb-solvable-group-structure).
   The largest-subgroup property gives c_g(U) contained in U. Repeating this
   with g^{-1} gives equality as subgroup schemes, not just on geometric points.
3. Apply lem-sfb-smooth-ambient-normality-geometric to U inside G, using F as
   its own algebraic closure. The ambient G is smooth affine of finite type,
   and step 2 supplies scheme-theoretic conjugation stability. Thus U is normal
   in G on all commutative F-algebras, including nonreduced ones.
4. Because F is algebraically closed, its algebraic closure is isomorphic to F
   over F (def-weil-algebraic-closure): every element is algebraic, and its
   polynomial splits over F. Scalar extension along this isomorphism preserves
   the subgroup properties and the faithful geometric matrix representations.
   Reductivity of G (def-sfb-reductive-torus-centralizer-terminology) now makes
   U trivial. Any smooth connected closed normal unipotent subgroup W of M is
   contained in U by lem-sfb-unipotent-radical-existence, so W is trivial too.
   Together with smoothness, connectedness and affine finite type this is the
   same reductivity predicate for M. For M = 1 it gives U = W = 1 as well. -/
theorem isReductive_of_smooth_connected_closed_normal_subgroup
    {F : Type u} [Field F] [IsAlgClosed F]
    (G M : Grp (Over (Spec (.of F))))
    (hG : ReductiveTorusCentralizer.IsReductive G)
    [Smooth M.X.hom] [ConnectedSpace M.X.left]
    (i : M ⟶ G) [IsClosedSubgroupScheme i.hom.hom]
    [IsNormalSubgroupScheme i.hom.hom] :
    ReductiveTorusCentralizer.IsReductive M := by
  sorry

end AlgebraicGeometry
