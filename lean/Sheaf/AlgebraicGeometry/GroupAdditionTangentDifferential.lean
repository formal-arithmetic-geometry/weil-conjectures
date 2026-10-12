/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
module

public import Sheaf.AlgebraicGeometry.SchemeTangentSpace
public import WeilConjectures.AlgebraicGeometry.GroupScheme.Basic
import Sheaf.AlgebraicGeometry.ProductTangentSpaceDirectSum
import Sheaf.AlgebraicGeometry.TangentMapLinear

/-!
# Differential of group addition at the identity

Source: Stacks Project, `groupoids.tex`, lemma-group-scheme-addition-tangent-vectors
(blueprint: lem-sc-group-addition-tangent-differential).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open scoped MonObj

namespace AlgebraicGeometry

/-- The differential of multiplication at the identity is addition on tangent vectors.
The equivalence `E` is the canonical product identification: its components are specified
by postcomposition with the projections. The final equality specifies postcomposition
with multiplication, hence its actual differential, rather than an arbitrary map.
The structural residue-field map at the unit is bijective because the unit is a k-point.
Dual-number spectra are transported along the resulting identification with the residue
field at the product unit. An additive equivalence suffices here: the projection formulas
uniquely identify it with the canonical k-linear equivalence of the product lemma.
Source: Stacks Project, `groupoids.tex`, lemma-group-scheme-addition-tangent-vectors
(blueprint: lem-sc-group-addition-tangent-differential).

Proof for stage 3:
1. The identity section is a k-rational point. Apply
   lem-sc-product-tangent-space-direct-sum to G and G at this point. The two projection
   differentials give the canonical direct-sum identification; its summand inclusions
   are induced by (1,e) and (e,1).
2. By the unit laws of def-sc-group-scheme, multiplication composed with either inclusion
   is the identity. Functoriality in lem-sc-tangent-map-linear therefore makes the
   differential of multiplication the identity on each summand.
3. By lem-sc-tangent-map-linear it is linear, so its value on (v,w) is its value on
   (v,0) plus its value on (0,w), namely v+w. The morphism equalities below express
   the projection differentials and this multiplication differential with the
   residue-field dual-number transport of def-sc-scheme-tangent-space.
-/
theorem group_addition_tangent_differential (k : Type u) [Field k]
    (G : Over (Spec (.of k))) [GrpObj G] :
    ∃ he : Function.Bijective
      (StructureSheaf.toStalk k (G.hom (GrpObj.onePoint G)) ≫
        G.hom.stalkMap (GrpObj.onePoint G) ≫ G.left.residue (GrpObj.onePoint G)).hom,
    ∃ E : schemeTangentSpace k (G ⊗ G).left (G ⊗ G).hom (GrpObj.onePoint (G ⊗ G)) ≃+
      (schemeTangentSpace k G.left G.hom (GrpObj.onePoint G) ×
        schemeTangentSpace k G.left G.hom (GrpObj.onePoint G)),
    ∀ t : schemeTangentSpace k (G ⊗ G).left (G ⊗ G).hom (GrpObj.onePoint (G ⊗ G)),
      (t.val ≫ (fst G G).left =
        Spec.map (CommRingCat.ofHom (DualNumber.mapRingHom
          ((StructureSheaf.toStalk k ((G ⊗ G).hom (GrpObj.onePoint (G ⊗ G))) ≫
            (G ⊗ G).hom.stalkMap (GrpObj.onePoint (G ⊗ G)) ≫
            (G ⊗ G).left.residue (GrpObj.onePoint (G ⊗ G))).hom.comp
            (RingEquiv.ofBijective
              (StructureSheaf.toStalk k (G.hom (GrpObj.onePoint G)) ≫
                G.hom.stalkMap (GrpObj.onePoint G) ≫
                G.left.residue (GrpObj.onePoint G)).hom he).symm.toRingHom))) ≫ (E t).1.val) ∧
      (t.val ≫ (snd G G).left =
        Spec.map (CommRingCat.ofHom (DualNumber.mapRingHom
          ((StructureSheaf.toStalk k ((G ⊗ G).hom (GrpObj.onePoint (G ⊗ G))) ≫
            (G ⊗ G).hom.stalkMap (GrpObj.onePoint (G ⊗ G)) ≫
            (G ⊗ G).left.residue (GrpObj.onePoint (G ⊗ G))).hom.comp
            (RingEquiv.ofBijective
              (StructureSheaf.toStalk k (G.hom (GrpObj.onePoint G)) ≫
                G.hom.stalkMap (GrpObj.onePoint G) ≫
                G.left.residue (GrpObj.onePoint G)).hom he).symm.toRingHom))) ≫ (E t).2.val) ∧
      (t.val ≫ (MonObj.mul (X := G)).left =
        Spec.map (CommRingCat.ofHom (DualNumber.mapRingHom
          ((StructureSheaf.toStalk k ((G ⊗ G).hom (GrpObj.onePoint (G ⊗ G))) ≫
            (G ⊗ G).hom.stalkMap (GrpObj.onePoint (G ⊗ G)) ≫
            (G ⊗ G).left.residue (GrpObj.onePoint (G ⊗ G))).hom.comp
            (RingEquiv.ofBijective
              (StructureSheaf.toStalk k (G.hom (GrpObj.onePoint G)) ≫
                G.hom.stalkMap (GrpObj.onePoint G) ≫
                G.left.residue (GrpObj.onePoint G)).hom he).symm.toRingHom))) ≫
          ((E t).1 + (E t).2).val) := by
  sorry

end AlgebraicGeometry
