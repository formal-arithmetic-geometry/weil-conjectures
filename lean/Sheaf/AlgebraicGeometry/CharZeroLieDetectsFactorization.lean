module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.Topology.Connected.Basic
public import WeilConjectures.AlgebraicGeometry.GroupScheme.Defs
public import WeilConjectures.AlgebraicGeometry.GroupScheme.Lie.Differential
public import WeilConjectures.AlgebraicGeometry.GroupScheme.LieIdentityTangentEquiv
public import WeilConjectures.AlgebraicGeometry.SchemeTangentSpace
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Sheaf.AlgebraicGeometry.AffineFiniteTypeAlgebra
import WeilConjectures.AlgebraicGeometry.GroupScheme.Cartier

/-!
# Lie containment detects factorization in characteristic zero

Source: Milne, Algebraic Groups (2017), 10.14, Proposition 10.15, pp.190-191,
and Cartier's Theorem 3.23, p.71
(blueprint: lem-sfb-charzero-lie-detects-factorization).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A homomorphism from a smooth connected affine group of finite type in characteristic zero
factors uniquely through a closed subgroup if its differential lands in that subgroup's Lie
algebra. The containment is written on the recorded scheme tangent spaces, using the canonical
`GrpObj.lieIdentityTangentEquiv` to apply the existing differential. Equality of the images in
`GrpObj.Lie H` is equivalent to equality in the tangent space at the identity of `H`.

Source: Milne, Algebraic Groups (2017), 10.14 and Proposition 10.15, pp.190-191,
and Theorem 3.23, p.71 (blueprint: lem-sfb-charzero-lie-detects-factorization).

Proof for stage 3:
1. Form the fibre product P = G times_H K (def-pc-fibre-product). The componentwise group
   operations give its group structure and make both projections homomorphisms
   (def-sc-group-scheme). The projection p : P to G is a closed immersion by
   lem-weil-pbc-closed-immersion-base-change. The affine closed-immersion description
   (def-weil-closed-immersion) makes P affine. Its coordinate algebra is a quotient of the
   finite-type coordinate algebra of G (lem-pc-affine-finite-type-algebra), so P is finite
   type over k (def-weil-finite-type-morphism).
2. For each identity tangent vector v of G, containment supplies a tangent vector w of K
   with the same image in H. The fibre-product property gives a unique tangent vector of P
   projecting to v and w (def-sc-scheme-tangent-space, def-pc-fibre-product). Thus dp is
   surjective. It is injective because the closed subgroup inclusion is injective on
   dual-number points (def-sc-group-scheme-subgroup).
3. Cartier's theorem (lem-sfb-cartier-characteristic-zero-smooth) makes P smooth. Apply
   lem-sfb-smooth-subgroup-full-tangent to p : P to G, with G affine, finite type and
   connected, P smooth, and dp surjective, to conclude that p is an isomorphism.
4. Define the factor as p inverse followed by q : P to K. It is a group homomorphism and
   its composite with i is f by the pullback relation. Any other homomorphism h gives
   the lift (id_G,h) : G to P, which must be p inverse; projecting to K gives uniqueness
   (def-pc-fibre-product, def-sc-group-scheme).
-/
theorem existsUnique_factorization_of_lie_containment_of_charZero
    (k : Type u) [Field k] [CharZero k]
    (G H K : Over (Spec (.of k))) [GrpObj G] [GrpObj H] [GrpObj K]
    [IsAffine G.left] [IsAffine H.left]
    [LocallyOfFiniteType G.hom] [QuasiCompact G.hom]
    [LocallyOfFiniteType H.hom] [QuasiCompact H.hom]
    [Smooth G.hom] [ConnectedSpace G.left]
    (i : K ⟶ H) [IsClosedSubgroupScheme i] (f : G ⟶ H) [IsMonHom f]
    (hLie : ∀ v : schemeTangentSpace k G.left G.hom
        (GrpObj.unitSection G (IsLocalRing.closedPoint k)),
      ∃ w : schemeTangentSpace k K.left K.hom
          (GrpObj.unitSection K (IsLocalRing.closedPoint k)),
        GrpObj.differential f ((GrpObj.lieIdentityTangentEquiv G).symm v) =
          GrpObj.differential i ((GrpObj.lieIdentityTangentEquiv K).symm w)) :
    ∃! g : G ⟶ K, IsMonHom g ∧ g ≫ i = f := by
  sorry

end AlgebraicGeometry
