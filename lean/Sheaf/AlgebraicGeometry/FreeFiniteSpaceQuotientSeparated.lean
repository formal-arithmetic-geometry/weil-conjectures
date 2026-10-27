module

public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Sheaf.TraceFormula.SpaceQCSeparatedEtaleLocal
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.CategoryTheory.Endomorphism
public import Mathlib.CategoryTheory.Limits.Types.Colimits
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Sites.Sheafification
import Sheaf.AlgebraicGeometry.EtaleRelationQuotient
import Sheaf.AlgebraicGeometry.SpaceChangeBase
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-! # Separatedness of free finite quotient algebraic spaces

Source: Stacks Project, Spaces, Tag 02Z4(2), with the action relation of Tag 02Z2
and change of base of Tag 03I4 (blueprint: lem-sfb-free-finite-space-quotient-separated).

The coproduct action relation includes locally constant group labels on disconnected
scheme tests. Its presheaf coequalizer is the orbit presheaf. The universal property
of sheafification specifies the given quotient without assuming a global small-valued
sheafification functor on the big site.

Absolute separatedness is expressed by the scheme-pair test: each U x_Q V is represented
and its canonical map to the absolute scheme product U x V is a closed immersion.
This is the test of Properties of Spaces, Tag 0AHS, with arbitrary scheme pairs;
the product is in Scheme, over Spec Z, even when S is not separated.
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- A free finite quotient of an absolutely separated scheme is absolutely separated,
and its structure map to the specified base is separated as well.
Source: Stacks, Spaces, Tag 02Z4(2); Tags 02Z2 and 03I4; Properties of Spaces, Tag 0AHS
(blueprint: lem-sfb-free-finite-space-quotient-separated).

Proof:
1. Put R = coproduct of G copies of W. The action and fold maps are an equivalence
   relation: on tests the labels are locally constant G-valued functions. The group
   laws give reflexivity, symmetry and transitivity, and the assumed monomorphism
   gives freeness. Each component of either projection is an isomorphism, hence etale.
2. Apply lem-trf-etale-relation-quotient to the presheaf coequalizer and its specified
   sheafification. This makes W -> Q representable, surjective and etale and identifies
   R with W x_Q W, compatibly with both projections.
3. Use lem-sfb-space-change-base-to-integers to view Q over Spec Z, retaining its atlas
   and this kernel pair. The pullback of its absolute diagonal to W x W is the map
   j : R -> W x W, (g,w) -> (gw,w). It is monic: equality of the two absolute maps
   to W forces agreement over S, where the assumed relative monomorphism applies.
4. Each component of j is the graph of an automorphism of W, a base change of the
   closed absolute diagonal of W, by lem-weil-pbc-closed-immersion-base-change.
   Distinct component images are disjoint: a shared point yields, over its residue
   field, two distinct labels with the same image, contradicting the monomorphism.
5. Finiteness of G makes the complements of unions of the other component images
   open. These opens and the complement of all images cover W x W. On each, j is
   a base change of one component, or the empty closed immersion. By the closed
   immersion clause of lem-weil-pbc-closed-finite-etale-zariski-local, j is closed.
6. Descend closed immersion along the atlas twice, using
   lem-trf-space-closed-immersion-cover-descent: first from W x W to W x Q, then to
   Q x Q. The representable diagonal and lem-trf-space-fibre-products-etale-covers
   supply the required pullbacks. Thus every scheme test of the absolute diagonal
   is closed. Testing on U x V gives exactly the first conjunct below; conversely
   arbitrary tests factor through such pair tests followed by the diagonal of their
   test scheme, so this conjunct is the full absolute condition.
7. The relative diagonal is a base change of this absolute diagonal along
   Q x_S Q -> Q x Q. Closed immersions persist under base change, proving the
   second conjunct in def-sfb-presheaf-map-separated-diagonal. No assumption on S,
   affine orbit neighborhoods, Noetherianity, or invertibility of the group order
   enters the argument. The empty scheme and trivial group are included. -/
theorem free_finite_space_quotient_separated {S : Scheme.{u}} (W : Over S)
    [W.left.IsSeparated] (G : Type v) [Group G] [Finite G] (a : G →* Aut W)
    [Mono (prod.lift (Sigma.desc (fun g : G ↦ (a g).hom))
      (Sigma.desc (fun _ : G ↦ 𝟙 W)))]
    (Q : AlgebraicSpace S)
    (η : coequalizer (yoneda.map (Sigma.desc (fun g : G ↦ (a g).hom)))
      (yoneda.map (Sigma.desc (fun _ : G ↦ 𝟙 W))) ⟶ Q.obj.obj)
    (hη : ∀ F : Sheaf (Scheme.fppfTopology.over S) (Type u),
      Function.Bijective (fun f : Q.obj.obj ⟶ F.obj ↦ η ≫ f)) :
    (∀ (U V : Over S) (b : yoneda.obj U ⟶ Q.obj.obj) (c : yoneda.obj V ⟶ Q.obj.obj),
      ∃ (P : Over S) (p : P ⟶ U) (q : P ⟶ V),
        IsPullback (yoneda.map p) (yoneda.map q) b c ∧
          IsClosedImmersion (prod.lift p.left q.left)) ∧
    IsSeparatedPresheafMap (terminal.from Q.obj.obj) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
