/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.IntersectionSectionsFlatBaseChange
public import Mathlib.RingTheory.RingHom.Flat
import Mathlib.LinearAlgebra.TensorProduct.DirectLimit
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.CategoryTheory.Limits.Preserves.Basic

/-!
# Flat base change for sections on a pro-open intersection

Source: Stacks Project, More on Groupoids in Spaces, Tag 0APJ,
`lemma-affine-base-change` (blueprint: lem-sfb-proopen-sections-flat-base-change).

The section rings and the canonical map are the existing inverse-image-sheaf
constructions of `WeilConjectures.AlgebraicGeometry.IntersectionSectionsFlatBaseChange`.
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- The canonical map on inverse-image structure-sheaf sections over an intersection
of a nonempty family of quasi-compact opens is an isomorphism of B-algebras after
flat affine base change. The source has its B-algebra structure through the right
factor. By the definition of `intersectionBaseChangeMap`, it sends c tensor b to
pullback of c multiplied by the section pulled back from Spec B.

Source: Stacks Project, More on Groupoids in Spaces, Tag 0APJ,
`lemma-affine-base-change` (blueprint: lem-sfb-proopen-sections-flat-base-change).

Proof:
1. Index by the nonempty finite subsets F of I and set V_F to the intersection
   of their opens. Union makes this index directed. The compact-open intersection
   hypothesis makes V_F compact. The affine-cover criterion
   lem-weil-pbc-quasi-separated-affine-cover-criterion and
   lem-weil-pbc-affine-scheme-qcqs make these opens quasi-separated.
   Lem-weil-pbc-qcqs-morphism-permanence gives the required compactness of their
   inverse images and quasi-separatedness of the base-changed scheme.
2. By lem-weil-pbc-flat-ring-map-iff-flat-affine, Spec B to Spec R is flat.
   Apply lem-weil-pbc-flat-base-change-global-sections-qcqs to each V_F.
   Its canonical comparison is c tensor b mapping to pullback(c) times b;
   compatibility of the sheaf comorphism with restrictions makes these maps
   an isomorphism of diagrams.
3. Apply lem-sfb-qc-open-intersection-sections-colimit on both schemes to identify
   sections on the two subspace intersections with the colimits of the stage
   sections. The second colimit is also a colimit of R-modules, by representatives
   and eventual equality.
4. Lem-weil-pbc-tensor-commutes-with-colimits identifies the tensor of the first
   colimit with the colimit of the stage tensors. The stage comparisons give a
   bijection to the second colimit. Representing c at a stage shows that this
   bijection is precisely the specified pure-tensor map.
5. The two ring maps into the target agree on R. By
   lem-weil-pbc-algebra-tensor-pushout-universal-property their product map is a
   B-algebra homomorphism. Its bijectivity makes it an isomorphism of B-algebras.
   The empty scheme, empty intersection and zero ring are included. -/
theorem isIso_intersectionBaseChangeMap_of_flat
    {R B : CommRingCat.{u}} (r : R ⟶ B) (hr : r.hom.Flat)
    {Y : Scheme.{u}} (p : Y ⟶ Spec R) [QuasiSeparatedSpace Y]
    {I : Type v} [Nonempty I] (U : I → Y.Opens)
    (hqc : ∀ i : I, IsCompact (U i : Set Y)) :
    IsIso (intersectionBaseChangeMap r p U) := by
  sorry

end AlgebraicGeometry.Scheme
