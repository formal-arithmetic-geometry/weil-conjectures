/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q122
-/
module

public import Sheaf.AlgebraicGeometry.SpaceCoverSheafDescent
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
import Sheaf.CategoryTheory.Sites.SheafificationPlusTheorem
import WeilConjectures.AlgebraicGeometry.SiteSheafificationSectionsLocal
import Mathlib.CategoryTheory.Sites.Sheafification

/-! # Sheaf realization of fppf algebraic-space descent data

Source: Stacks Project, Spaces, Descent, Tag 0ADT, equivalence and clause (1);
Topologies on Algebraic Spaces, Tag 03Y8
(blueprint: lem-sfb-fppf-space-datum-sheaf-realization).

The theorem concerns the specified canonical restriction functor. A datum isomorphism
includes all local identifications and their compatibility with the given transitions.
No algebraicity of the global sheaf is asserted.
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory

namespace AlgebraicGeometry.AlgebraicSpace

/-- Canonical restriction is an equivalence, every datum has a sheaf realization with
its given transitions, and restriction is bijective on morphisms.
Source: Stacks Project, Spaces, Descent, Tag 0ADT, equivalence and clause (1);
Topologies on Algebraic Spaces, Tag 03Y8
(blueprint: lem-sfb-fppf-space-datum-sheaf-realization).

Proof, following the nine steps of the node:
1. Restrict a sheaf `F → X` by pullback. Overlap transport keeps `F` fixed, hence satisfies
   the cocycle. Morphisms act on the `F` coordinate. The fibre products of algebraic
   spaces are algebraic by lem-trf-space-fibre-products-etale-covers.
2. A section of `X` over a scheme locally lifts to some `Xᵢ`: pull back the covering and
   take scheme étale atlases of the resulting algebraic spaces. The base-change,
   composition, étale and scheme clauses of lem-sfb-space-fppf-covering-calculus give an
   fppf scheme cover, without assuming that `Xᵢ → X` is representable.
3. For a datum, quotient the disjoint union of its local section sets by transport.
   The cocycle makes this an equivalence relation, preserved by restrictions. Identity
   and reverse transport follow from the invertible cocycle. This gives a presheaf `P`
   with a map to `X`.
4. Sheafify `P` by the double-plus construction, using
   lem-weil-pbc-sheafification-plus-theorem and def-weil-pbc-sheafification. The universal
   property extends `P → X` to `F → X`. The maps `v ↦ (bᵢ(v), [i,v])` define local
   comparisons `Vᵢ → Xᵢ ×_X F`.
5. These comparisons are injective on sections: equality after sheafification is locally
   equality in the quotient by lem-weil-pbc-site-sheafification-sections-local. At the
   same base coordinate transport is the identity, so the sheaf axiom gives equality.
6. They are surjective: represent a section of `F` locally by `[j,v]`, transport it to
   the prescribed `Xᵢ` coordinate, and glue these preimages. Injectivity makes them agree
   on overlaps. Thus they are local isomorphisms and `F` belongs to the full subcategory.
7. The quotient relation shows these isomorphisms induce exactly the original overlap
   transports. Compatible local maps descend to quotient presheaves and then sheafify,
   giving a functor back and a natural comparison on descent data.
8. For a sheaf `G → X`, forgetting the covering coordinate induces `Q R G → G`. Local
   lifting from step 2 makes it locally surjective. Common local quotient representatives
   with equal image are related by canonical transport, proving injectivity. The sheaf
   axiom then gives an isomorphism, natural by the sheafification universal property.
9. These two natural comparisons are quasi-inverses. They realize every datum with its
   specified transitions. Compatible maps glue by step 7, and two global maps agreeing
   locally agree by step 2 and separatedness. Hence restriction is bijective on maps.
   Empty families use the empty-cover sheaf axiom and cause no exception. The proof uses
   no global atlas or representable diagonal for `F`.
-/
theorem fppfSpaceDatumSheafRealization {S : Scheme.{u}} {I : Type w}
    {X : AlgebraicSpace S} {Xᵢ : I → AlgebraicSpace S} (a : ∀ i, Xᵢ i ⟶ X)
    (hflat : ∀ i, MapIsFlat (a i))
    (hlfp : ∀ i, MapIsLocallyOfFinitePresentation (a i))
    (hsurj : IsJointlySurjective (fun i ↦ (a i).hom.hom)) :
    (spaceCoverSheafRestriction a).IsEquivalence ∧
      (∀ D : SpaceCoverSheafDescent a,
        ∃ F : (IsLocallyAlgebraicSpaceSheaf a).FullSubcategory,
          Nonempty (D ≅ (spaceCoverSheafRestriction a).obj F)) ∧
      (∀ F G : (IsLocallyAlgebraicSpaceSheaf a).FullSubcategory,
        Function.Bijective
          ((spaceCoverSheafRestriction a).map : (F ⟶ G) →
            ((spaceCoverSheafRestriction a).obj F ⟶ (spaceCoverSheafRestriction a).obj G))) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
