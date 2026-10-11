/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G1
-/
import Sheaf.AlgebraicGeometry.SchemeTangentSpace
import WeilConjectures.PointCount
import Mathlib.AlgebraicGeometry.Pullbacks

/-!
# Tangent space of a product

Source: Stacks Project, Tag 0BEB, varieties-lemma-tangent-space-product, specialized to `Spec k`
(blueprint: lem-sc-product-tangent-space-direct-sum).
-/

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- The projection differentials identify the tangent space at a pair of rational points
with the direct sum of their tangent spaces. The points `x`, `y` are `k`-rational: the
structural maps `rX : k → κ(x)`, `rY : k → κ(y)` are bijective (the form of
`exists_rationalPoint_tangent_cotangent_linearEquiv`). `sx`, `sy` are the corresponding
`k`-points `Spec k ≅ Spec κ(x) → X`, `iX = (1, y)` and `iY = (x, 1)` the maps into the fibre
product `P = X ×_k Y`, and `z = iX x` the point `(x, y)`. The tangent spaces are `k`-vector
spaces through `rX`, `rY`, `rZ`. The finite direct sum is the product of vector spaces. The
maps `dZX`, `dZY` identify dual-number spectra through the residue-field isomorphisms over
`k`, so the morphism equalities express the projection and inclusion differentials.
Source: Stacks Project, Tag 0BEB (blueprint: lem-sc-product-tangent-space-direct-sum).

Proof for stage 3:
1. Compose tangent vectors with the projections of the fibre product (def-pc-fibre-product).
   The residue fields at the three rational points are k. The two differentials are linear
   by lem-sc-tangent-map-linear and hence give a k-linear map to the product.
2. Define the inverse on (v,w) as d(1,y)(v) + d(x,1)(w), using the addition of
   lem-sc-tangent-space-vector-space. Composing either inclusion with its own projection
   gives the identity; the other composite is constant and sends tangent vectors to zero,
   by the constant zero vector in def-sc-scheme-tangent-space. Linearity therefore shows
   that the projection map composed with this proposed inverse is the identity.
3. A morphism to the fibre product is determined by its projections (def-pc-fibre-product).
   Apply this uniqueness to a tangent vector and the proposed inverse of its projections
   to obtain the other inverse identity. The inverse on (v,0) and (0,w) is the respective
   inclusion differential since linear maps preserve zero (lem-sc-tangent-map-linear).
-/
theorem product_tangentSpace_directSum
    (k : Type u) [Field k] (X Y : Scheme.{u})
    (pX : X ⟶ Spec (.of k)) (pY : Y ⟶ Spec (.of k)) (x : X) (y : Y) :
    let rX : k →+* X.residueField x :=
      (StructureSheaf.toStalk k (pX x) ≫ pX.stalkMap x ≫ X.residue x).hom
    let rY : k →+* Y.residueField y :=
      (StructureSheaf.toStalk k (pY y) ≫ pY.stalkMap y ≫ Y.residue y).hom
    ∀ (hx : Function.Bijective rX) (hy : Function.Bijective rY),
    let eX := RingEquiv.ofBijective rX hx
    let eY := RingEquiv.ofBijective rY hy
    let sx : Spec (.of k) ⟶ X :=
      Spec.map (CommRingCat.ofHom eX.symm.toRingHom) ≫ X.fromSpecResidueField x
    let sy : Spec (.of k) ⟶ Y :=
      Spec.map (CommRingCat.ofHom eY.symm.toRingHom) ≫ Y.fromSpecResidueField y
    let P := pullback pX pY
    let prX := pullback.fst pX pY
    let prY := pullback.snd pX pY
    let pZ := prX ≫ pX
    let iX : X ⟶ P := pullback.lift (𝟙 X) (pX ≫ sy) (by
      have h : Y.fromSpecResidueField y ≫ pY = Spec.map (CommRingCat.ofHom rY) := by
        rw [← pY.specMap_residueFieldAlgebraMap]
        congr 2
        rw [Scheme.Hom.residueFieldAlgebraMap, Scheme.Spec.algebraMap_residueFieldIso_inv_assoc,
          Scheme.residue_residueFieldMap]
        rfl
      simp only [sy, Category.id_comp, Category.assoc, h, ← Spec.map_comp,
        ← CommRingCat.ofHom_comp,
        show eY.symm.toRingHom.comp rY = RingHom.id k from RingHom.ext eY.symm_apply_apply,
        CommRingCat.ofHom_id, Spec.map_id, Category.comp_id])
    let iY : Y ⟶ P := pullback.lift (pY ≫ sx) (𝟙 Y) (by
      have h : X.fromSpecResidueField x ≫ pX = Spec.map (CommRingCat.ofHom rX) := by
        rw [← pX.specMap_residueFieldAlgebraMap]
        congr 2
        rw [Scheme.Hom.residueFieldAlgebraMap, Scheme.Spec.algebraMap_residueFieldIso_inv_assoc,
          Scheme.residue_residueFieldMap]
        rfl
      simp only [sx, Category.id_comp, Category.assoc, h, ← Spec.map_comp,
        ← CommRingCat.ofHom_comp,
        show eX.symm.toRingHom.comp rX = RingHom.id k from RingHom.ext eX.symm_apply_apply,
        CommRingCat.ofHom_id, Spec.map_id, Category.comp_id])
    let z := iX x
    let rZ : k →+* P.residueField z :=
      (StructureSheaf.toStalk k (pZ z) ≫ pZ.stalkMap z ≫ P.residue z).hom
    let TX := schemeTangentSpace k X pX x
    let TY := schemeTangentSpace k Y pY y
    let TZ := schemeTangentSpace k P pZ z
    letI : Module k TX := Module.compHom TX rX
    letI : Module k TY := Module.compHom TY rY
    letI : Module k TZ := Module.compHom TZ rZ
    let dZX := Spec.map (CommRingCat.ofHom
      (DualNumber.mapRingHom (rZ.comp eX.symm.toRingHom)))
    let dZY := Spec.map (CommRingCat.ofHom
      (DualNumber.mapRingHom (rZ.comp eY.symm.toRingHom)))
    ∃ e : TZ ≃ₗ[k] (TX × TY),
      (∀ v : TZ, v.val ≫ prX = dZX ≫ (e v).1.val ∧
        v.val ≫ prY = dZY ≫ (e v).2.val) ∧
      (∀ v : TX, (e.symm (v, 0)).val = dZX ≫ v.val ≫ iX) ∧
      (∀ w : TY, (e.symm (0, w)).val = dZY ≫ w.val ≫ iY) := by
  sorry

end AlgebraicGeometry
