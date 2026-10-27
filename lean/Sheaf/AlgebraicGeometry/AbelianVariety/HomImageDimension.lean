/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q24
-/
module

public import WeilConjectures.AlgebraicGeometry.AbelianVariety.Defs
public import WeilConjectures.AlgebraicGeometry.GroupScheme.Image
public import WeilConjectures.Mathlib.Topology.KrullDimension
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Proper
import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Reduced
import Sheaf.AlgebraicGeometry.GeometricallyReducedDominantDescent
import Mathlib.AlgebraicGeometry.Group.Smooth
import Mathlib.AlgebraicGeometry.Geometrically.Integral
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Sheaf.AlgebraicGeometry.FlatCompositeFibreDimensionAtPoint
import Sheaf.AlgebraicGeometry.FiniteTypeDimensionFormula
import Sheaf.AlgebraicGeometry.GroupScheme.IdentityLocalDimension

/-!
# Abelian images and the kernel dimension formula

Source: Milne, Algebraic Groups (2017), Theorem 1.72, printed pp.28–29, and
Theorem 5.39 and Remark 5.42, printed pp.108–109.
(blueprint: lem-sfb-abelian-hom-image-dimension)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- The scheme-theoretic image of an abelian-variety homomorphism is an abelian variety,
and the source dimension is the sum of the image and scheme-theoretic kernel dimensions.

Source: Milne, Algebraic Groups (2017), Theorem 1.72, printed pp.28–29, and
Theorem 5.39 and Remark 5.42, printed pp.108–109.
(blueprint: lem-sfb-abelian-hom-image-dimension)

Proof:
1. By `lem-sc-image-subgroup`, the actual scheme-theoretic image carries the subgroup
   structure induced from the target, and the map onto it is surjective. By
   `pqf-lem-image-proper`, both the image and the map onto it are proper. The latter is
   a homomorphism, by cancellation of the monomorphic image inclusion.
2. The source is geometrically reduced by `sbc-lem-smooth-geometrically-reduced`.
   The image factorization is scheme-theoretically dominant by
   `lemma-nagata-scheme-image-ideal-qc`. Apply
   `lem-sbc-geometrically-reduced-dominant-descent`, then
   `lem-sfb-geometrically-reduced-group-smooth`, to make the image smooth. It is connected
   as a continuous surjective image of the source. These properties give
   `def-sc-abelian-variety`; its group structure is the one already supplied in step 1.
3. Apply `lem-sfb-algebraic-group-homomorphism-factorization` to the map onto the image.
   Its closed-immersion factor is surjective onto a reduced scheme, so
   `lem-weil-pbc-reduced-source-factors-through-closed-subscheme` makes this factor an
   isomorphism. Thus the map onto the image is flat. Its fibre over the identity is
   `GrpObj.ker f`: the image inclusion is monomorphic and preserves the identity.
   By `lem-sc-kernel-subgroup`, this kernel is a closed finite-type subgroup of the source.
4. Apply `lem-sbc-flat-composite-fibre-dimension-at-point` to the flat map onto the image
   followed by its structure map, at the source identity. The dimension at this point is
   the sum of the dimensions at the kernel and image identities.
5. The three identities are rational. By `lem-kun-dimension-formula`, their dimensions at
   a point equal their local-ring dimensions, since the residue transcendence degrees
   vanish. By `lem-ag-group-identity-local-dimension`, these are the global dimensions.
   Substitute and commute the summands. This also applies to nonreduced kernels. -/
theorem isAbelianVariety_image_and_dimension
    {k : Type u} [Field k] {A B : Over (Spec (.of k))}
    [GrpObj A] [GrpObj B] [IsAbelianVariety A] [IsAbelianVariety B]
    (f : A ⟶ B) [IsMonHom f] :
    IsAbelianVariety (Over.mk (f.left.imageι ≫ B.hom)) ∧
      topologicalKrullDim A.left =
        topologicalKrullDim f.left.image + topologicalKrullDim (GrpObj.ker f).left := by
  sorry

end AlgebraicGeometry
