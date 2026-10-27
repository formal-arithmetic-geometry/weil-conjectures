module

public import Mathlib.AlgebraicGeometry.Scheme
public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
public import Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties
import Sheaf.AlgebraicGeometry.AlgebraicSpaceAffineEtaleCover
import Sheaf.AlgebraicGeometry.AlgebraicSpacePointOpenCalculus

/-! # Universal closedness of algebraic spaces tested on affine schemes

Source: Stacks Project, Morphisms of Spaces, Tag 03IT,
`lemma-universally-closed-local`, implication (3) implies (1)
(blueprint: lem-sfb-space-universally-closed-affine-tests).

The affine-test image is pulled back along the residue-field point map of `T`.
It is thus a subset of the underlying scheme `T`, with its usual topology.
The conclusion uses the existing universal-closedness predicate for algebraic spaces.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- A morphism of algebraic spaces is universally closed if all its base changes to
an affine scheme are closed on points. In the hypothesis, the inverse image along
`schemePointMap (𝟙 (yoneda.obj T))` identifies the projection image with a subset of
`T.left`, without choosing representatives or an inverse to the scheme point map.

Source: Stacks Project, Morphisms of Spaces, Tag 03IT,
`lemma-universally-closed-local`, implication (3) implies (1)
(blueprint: lem-sfb-space-universally-closed-affine-tests).

Proof:
1. Fix an algebraic space Z over S and a morphism Z → Y. Form P = X ×_Y Z and its
   projection p by lem-trf-space-fibre-products-etale-covers. Choose a surjective étale
   atlas W → Z with W a disjoint union of affine S-schemes W_i by
   lem-a1-space-affine-etale-cover. Its point map is a quotient map.
2. For a closed subset C of |P|, pull it back to C_i in |P ×_Z W_i|. The universal
   property of sheaf fibre products identifies P ×_Z W_i with X ×_Y W_i. The inverse
   morphisms induce a homeomorphism, since every point map is continuous by
   lem-a1-space-point-open-calculus. Thus C_i is closed, and the affine-test hypothesis
   says its projection image D_i in the ordinary point space |W_i| is closed.
3. Put D = |p|(C). For the atlas component q_i : W_i → Z, one has q_i⁻¹(D) = D_i.
   Commutativity gives one inclusion. Conversely, if w and x ∈ C have the same image
   in |Z|, the point-fibre-product surjectivity in lem-a1-space-point-open-calculus
   lifts the pair (x,w) to a point of P ×_Z W_i, which belongs to C_i. This uses only
   surjectivity onto the set-theoretic fibre product, without asserting injectivity.
4. The complement of the inverse image of D in |W| is the union of the open
   complements |W_i| \ D_i in the disjoint open summands. Hence that inverse image
   is closed. Descend closedness along the quotient point map |W| → |Z| from
   lem-a1-space-affine-etale-cover. Its quotient topology is the final topology of
   def-a1-space-point-topology: the atlas is one of the defining étale tests, and
   every étale scheme-source map is continuous for the atlas topology. Thus D is
   closed. Since C and Z → Y were arbitrary, f is universally closed. -/
theorem mapIsUniversallyClosed_of_affine_tests {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (h : ∀ (T : Over S) (a : yoneda.obj T ⟶ Y.obj.obj), IsAffine T.left →
      ∀ C : Set (Point (Limits.pullback f.hom.hom a)), IsClosed C →
        IsClosed (schemePointMap (𝟙 (yoneda.obj T)) ⁻¹'
          (mapPoint (Limits.pullback.snd f.hom.hom a) '' C))) :
    MapIsUniversallyClosed f := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
