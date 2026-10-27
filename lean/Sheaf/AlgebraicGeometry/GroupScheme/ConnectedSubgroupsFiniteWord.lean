module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.RingTheory.Smooth.Basic
import WeilConjectures.AlgebraicGeometry.Regular
import Sheaf.AlgebraicGeometry.RegularClosedPointComponents
import WeilConjectures.Mathlib.RingTheory.Smooth.StandardSmoothOfFree
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Spectrum.Prime.Topology
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.Topology.KrullDimension
import Sheaf.AlgebraicGeometry.GroupScheme.AffinePointedMapGeneratedSubgroup

/-! # A finite dominant word in generating connected subgroups

Source: Milne, Algebraic Groups (2017), Corollary 17.92, p.382, and
Propositions 2.46--2.53, pp.54--56. The general maximal-dimension word argument is
agent supplied, rather than a verbatim result of Milne.
(blueprint: lem-sfb-connected-subgroups-finite-word)
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory Limits
open scoped MonObj

namespace AlgebraicGeometry

/-- A generating family of smooth geometrically connected closed subgroups admits
one nonempty ordered word whose multiplication morphism has dense Zariski image.

Source: the agent-supplied finite-word prerequisite for Milne, Corollary 17.92,
p.382, using Propositions 2.46--2.53, pp.54--56.
(blueprint: lem-sfb-connected-subgroups-finite-word)

The product implicit in `Pi.π` is the scheme product over `Spec k`. Multiplication
in the group of morphisms to `G` evaluates pointwise using the multiplication of
`G`, so `List.ofFn ... |>.prod` multiplies the factors in their displayed order.
For a closed subgroup inclusion `j`, `IsIso j` expresses equality with `G` as a
closed subgroup, without identifying different presentations of that subscheme.

Proof:
1. For each nonempty word v form its product P_v and word map w_v. Each factor is
   affine and finite type by def-weil-closed-immersion and
   def-weil-finite-type-morphism. The affine tensor-product description
   lem-weil-pbc-fibre-product-affine-spectra gives these properties for P_v.
   Use lem-weil-pbc-smooth-ring-map-iff-smooth-affine in both directions and
   lem-weil-pbc-smooth-ring-map-base-change-composition to make P_v smooth.
   The tuple of identities is a rational point. Induct with
   lem-weil-pbc-geometrically-connected-product-components to make P_v connected.
2. By lem-weil-pbc-smooth-scheme-over-field-regular and
   lem-wf-smooth-components-disjoint it is irreducible. Its smooth coordinate
   algebra is reduced by lem-sc-smooth-algebra-reduced-field. Thus P_v is integral
   by def-pc-integral-scheme, and its coordinate algebra is a domain.
3. In A = k[G], let J_v be the prime kernel of w_v on coordinates. By
   lem-weil-pbc-spec-irreducible-closed-subsets-primes the image closure is
   Z_v = V(J_v): the generic point of P_v maps to J_v. The dimension bound
   lem-kun-dimension-finite-type bounds all these irreducible closed subsets.
   Nonemptiness of I supplies a word, so choose v with maximal dimension.
4. Insert identity factors to include Z_v and Z_w in Z_vw. A proper inclusion
   Z_v < Z_vw would extend a maximal finite chain of irreducible closed subsets,
   contradicting maximality, by def-kun-topological-krull-dimension. Hence
   J_vw = J_v and J_v is contained in J_w. The same argument applies to any
   word containing v as a consecutive block.
5. On X = P_v × P_v take the pointed map φ(x,y) = w_v(x)w_v(y)⁻¹.
   Its image on every algebra is inverse stable by exchanging x and y.
   Reversing the factors of y and inverting each identifies φ with the word
   vv_rev. Its positive powers are words containing v, so all have kernel J_v.
6. By lem-sfb-affine-pointed-map-generated-subgroup the spectrum of the quotient
   by the intersection of these kernels is a closed subgroup. Since all kernels
   equal J_v, this is exactly Z_v, as a closed subscheme, not just on field points.
7. Each one-letter word factors through Z_v, since J_v is contained in its kernel.
   The quotient factorization uses def-weil-pbc-algebra-hom-quotient and
   def-weil-affine-spectrum. The generation hypothesis forces Z_v = G. Therefore
   the chosen nonempty word has dense image. No commutativity, normality,
   finiteness of I, infinitude of k, or perfectness of k is used.
-/
theorem exists_dominant_word_of_generating_connected_subgroups
    {k : Type u} [Field k] (G : Over (Spec (.of k))) [GrpObj G]
    [IsAffine G.left] [LocallyOfFiniteType G.hom] [QuasiCompact G.hom]
    [Smooth G.hom] [GeometricallyConnected G.hom]
    {I : Type v} [Nonempty I] (H : I → Over (Spec (.of k)))
    [∀ i : I, GrpObj (H i)] (inc : ∀ i : I, H i ⟶ G)
    [∀ i : I, IsClosedSubgroupScheme (inc i)]
    [∀ i : I, Smooth (H i).hom] [∀ i : I, GeometricallyConnected (H i).hom]
    (hgen : ∀ (K : Over (Spec (.of k))) [GrpObj K] (j : K ⟶ G),
      IsClosedSubgroupScheme j →
      (∀ i : I, ∃ f : H i ⟶ K, f ≫ j = inc i) → IsIso j) :
    ∃ n : ℕ, 1 ≤ n ∧ ∃ word : Fin n → I,
      IsDominant ((List.ofFn fun a : Fin n ↦
        Pi.π (fun b : Fin n ↦ H (word b)) a ≫ inc (word a)).prod).left := by
  sorry

end AlgebraicGeometry
