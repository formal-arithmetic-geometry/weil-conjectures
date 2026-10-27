module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.CategoryTheory.Monoidal.Grp
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import Mathlib.Topology.Irreducible

import Mathlib.AlgebraicGeometry.Geometrically.Integral
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.PullbackCarrier
import WeilConjectures.AlgebraicGeometry.ReductionUniversalHomeomorphism

/-! # Irreducible group schemes are quasi-compact

Source: Stacks Project, Groupoids, Tag 0B7P,
`lemma-irreducible-group-scheme-over-field-qc`
(blueprint: lem-sfb-irreducible-group-quasi-compact).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- An irreducible group scheme over a field is quasi-compact, without a finite-type,
smoothness or reducedness hypothesis.

Source: Stacks Project, Groupoids, Tag 0B7P
(blueprint: lem-sfb-irreducible-group-quasi-compact).

Proof:
1. Apply lem-sfb-scheme-large-algclosed-jacobson to choose an algebraically closed
   extension K/k such that G = H_K is Jacobson with K-rational closed points. Base change
   the group diagrams using def-sc-group-scheme and def-pc-fibre-product. By
   lem-sfb-group-local-minimal-prime the reduced identity component is geometrically
   irreducible; since H is irreducible it is H_red. Its base change maps homeomorphically
   to G by lem-weil-pbc-reduction-universal-homeomorphism, so G is irreducible
   (def-pc-geometrically-irreducible).
2. The shear (x,y) ↦ (xy,y) has inverse (z,y) ↦ (zy⁻¹,y), by def-sc-group-scheme.
   Multiplication is its composite with the first projection, which is open by
   lem-sc-scheme-over-field-universally-open. Thus multiplication is open.
3. Choose a nonempty affine open U in G using the unit and def-pc-scheme. Inversion is an
   isomorphism by the group diagrams. The open immersion of U ×_K U into G ×_K G
   (lem-weil-pbc-open-fibre-product), followed by id × inversion and multiplication,
   therefore has open image W. This map is d(u,v) = uv⁻¹.
4. For every g in G(K), gU and U intersect by def-weil-irreducible-components. The
   Jacobson property from step 1 supplies a rational closed point a in their intersection.
   Put b = g⁻¹a in U(K); then d(a,b) = g. Hence W contains every closed point, so its closed
   complement is empty by the Jacobson property. Thus d is surjective.
5. By lem-weil-pbc-fibre-product-affine-spectra, U ×_K U is affine, say Spec(A ⊗_K A).
   The map G → H is surjective by lem-weil-pbc-surjective-base-change, since Spec K → Spec k
   is surjective (both spectra are singletons, def-weil-affine-spectrum). Composing with d
   gives an affine-source surjection onto H. Apply lem-weil-pbc-quasicompact-affine-surjection
   to obtain precisely the finite-subcover property of H. -/
theorem compactSpace_of_irreducible_groupScheme {k : Type u} [Field k]
    (H : Over (Spec (CommRingCat.of k))) [GrpObj H] [IrreducibleSpace H.left] :
    CompactSpace H.left := by
  sorry

end AlgebraicGeometry
