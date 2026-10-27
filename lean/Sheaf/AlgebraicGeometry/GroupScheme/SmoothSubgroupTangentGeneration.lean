/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q60
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.CategoryTheory.Monoidal.Grp
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.Topology.Connected.Basic
public import WeilConjectures.AlgebraicGeometry.GroupScheme.Defs
public import WeilConjectures.AlgebraicGeometry.GroupScheme.Lie.Differential
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.AlgebraicGeometry.Properties
import Sheaf.AlgebraicGeometry.LocallyAlgebraicGroupIdentityComponent
import Sheaf.RingTheory.SmoothAlgebraReduced
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import WeilConjectures.AlgebraicGeometry.SchemeTangentSpace
import Sheaf.AlgebraicGeometry.RationalTangentCotangentDuality
import WeilConjectures.AlgebraicGeometry.GroupScheme.LieLocalDimension
import Sheaf.AlgebraicGeometry.GroupScheme.IdentityLocalDimension
import WeilConjectures.Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# Generation by smooth subgroups whose identity tangent spaces span

Source: Milne, Algebraic Groups (2017), Corollary 10.17 and Proposition 10.15,
printed pp.190–191, with the linear-span hypothesis
(blueprint: lem-sfb-smooth-subgroup-tangent-generation).
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory

namespace AlgebraicGeometry.GrpObj

/-- A closed subgroup containing smooth connected subgroups whose tangent images span is
the whole smooth connected affine group. The finite family may be empty, and the containing
subgroup need not be smooth or connected. Here `Lie` is the tangent space at the identity:
`lieCotangentDualEquiv` identifies it with the dual of the identity cotangent space, and
`differential` sends a dual-number tangent point to its composite with the homomorphism.
The supremum is taken in the lattice of linear subspaces, rather than Lie subalgebras.
For a closed-subgroup inclusion, being an isomorphism means equality as closed subschemes.

Source: Milne, Algebraic Groups (2017), Corollary 10.17 and Proposition 10.15,
printed pp.190–191 (blueprint: lem-sfb-smooth-subgroup-tangent-generation).

Proof for stage 3:
1. The closed subgroup K of the affine finite-type G is affine of finite type, by the
   quotient description of def-weil-closed-immersion. Apply
   lem-sfb-locally-algebraic-group-identity-component to K. Its identity component K0 is
   open and closed, and L = (K0)_red is a smooth connected integral group of finite type.
   Its inclusion in G is closed, by the nilradical ideal on K0 and the unit ideal on its
   complement, followed by composition of closed immersions.
2. Connectedness forces each H_i into K0: its inverse image is open and closed and contains
   the identity (def-weil-connected-scheme and def-weil-open-immersion). Smoothness over a
   field makes H_i reduced, by def-sbc-smooth-morphisms,
   lem-sfb-smooth-algebra-over-reduced-ring and def-pc-reduced-scheme. Then
   lem-weil-pbc-reduced-source-factors-through-closed-subscheme factors H_i through L.
   These factors are homomorphisms because they are so after the closed inclusion in G.
3. Functoriality of def-sc-scheme-tangent-space puts every differential image in the image
   of Lie(L) in Lie(G). The spanning hypothesis makes this image all of Lie(G). A closed
   immersion induces a surjection on cotangent spaces, so its tangent map is injective
   by lem-sc-rational-tangent-cotangent-duality. Thus Lie(L) and Lie(G) are isomorphic.
   This also treats the empty family, whose span is zero.
4. Apply lem-ag-smooth-lie-local-dimension and lem-ag-group-identity-local-dimension to
   L and G. Their dimensions equal their Lie dimensions, so dim L = dim G, in any
   characteristic.
5. G is reduced by lem-sfb-smooth-algebra-over-reduced-ring and is integral by
   lem-sfb-locally-algebraic-group-identity-component, since it is connected. By
   lem-wf-affine-dimension-drop a proper closed support of L would have smaller dimension.
   Hence L and G have the same support.
6. Apply lem-weil-pbc-reduced-source-factors-through-closed-subscheme to the identity of
   the reduced G. It factors through L, so L = G as closed subschemes. The defining ideals
   of L, K and G then force K = G. No regularity assumption on K was used.
-/
theorem isIso_of_iSup_range_differential_eq_top
    (F : Type u) [Field F] [IsAlgClosed F]
    (G : Over (Spec (.of F))) [GrpObj G]
    [IsAffine G.left] [Smooth G.hom] [ConnectedSpace G.left]
    [LocallyOfFiniteType G.hom] [QuasiCompact G.hom]
    (I : Type v) [Finite I] (H : I → Over (Spec (.of F)))
    [∀ i : I, GrpObj (H i)] (ι : ∀ i : I, H i ⟶ G)
    [∀ i : I, IsClosedSubgroupScheme (ι i)]
    [∀ i : I, Smooth (H i).hom] [∀ i : I, ConnectedSpace (H i).left]
    (hspan : (⨆ i : I, LinearMap.range (differential (ι i)).toLinearMap) = ⊤)
    (K : Over (Spec (.of F))) [GrpObj K] (j : K ⟶ G) [IsClosedSubgroupScheme j]
    (hfactor : ∀ i : I, ∃ f : H i ⟶ K, f ≫ j = ι i) :
    IsIso j := sorry

end AlgebraicGeometry.GrpObj
