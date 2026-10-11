/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
import Sheaf.AlgebraicGeometry.TangentVectorsVectorSpace
import WeilConjectures.AlgebraicGeometry.DualNumbers

/-!
# Linearity of the map on dual-number tangent vectors

Source: Stacks Project, Tag 0B2F, with base `Spec k`
(blueprint: lem-sc-tangent-map-linear).
-/

universe u

open CategoryTheory

namespace AlgebraicGeometry

open Classical in
/-- Postcomposition with a morphism over `k` induces a linear map on tangent vectors when
its residue-field map is an isomorphism.
Source: Stacks Project, Tag 0B2F (blueprint: lem-sc-tangent-map-linear).

The additive groups and modules are selected from `exists_tangentVectors_vectorSpace`.
The target scalars are transported along the inverse residue-field isomorphism `e.symm`.
Likewise `d` identifies the two dual-number spectra, so `d ≫ θ.val ≫ f` is precisely
postcomposition with `f` after the residue fields have been identified.

Proof for stage 3:
1. Residue-field point naturality (lem-weil-pbc-residue-field-point-naturality) gives
   `Spec.map (f.residueFieldMap x) ≫ Y.fromSpecResidueField (f x) =
   X.fromSpecResidueField x ≫ f`. Hence the composite has the required closed point.
   Associativity and `hf` also show that it is a morphism over `k`.
2. By the scalar formula of lem-sc-tangent-space-vector-space, multiplication by a scalar
   is precomposition with the dual-number scaling map. Under `e`, these scaling maps
   agree. Precomposition commutes with postcomposition, including for the zero scalar.
3. By the pushout and addition formula of lem-sc-tangent-space-vector-space, two tangent
   vectors glue uniquely to a map from the two-direction square-zero spectrum. Composing
   this map with `f` gives the gluing of the two images, by uniqueness. Precomposition
   with the sum map therefore proves additivity. This and step 2 give the linear map.
-/
theorem exists_tangentMap_linear
    (k : Type u) [Field k] (X Y : Scheme.{u})
    (pX : X ⟶ Spec (.of k)) (pY : Y ⟶ Spec (.of k))
    (f : X ⟶ Y) (hf : f ≫ pY = pX) (x : X)
    (he : Function.Bijective (f.residueFieldMap x).hom) :
    let KX := X.residueField x
    let KY := Y.residueField (f x)
    let DX := Spec (.of (DualNumber KX))
    let DY := Spec (.of (DualNumber KY))
    let cX : Spec KX ⟶ DX :=
      Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom KX KX KX).toRingHom)
    let cY : Spec KY ⟶ DY :=
      Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom KY KY KY).toRingHom)
    let qX : DX ⟶ Spec KX :=
      Spec.map (CommRingCat.ofHom (TrivSqZeroExt.inlHom KX KX))
    let qY : DY ⟶ Spec KY :=
      Spec.map (CommRingCat.ofHom (TrivSqZeroExt.inlHom KY KY))
    let bX := X.fromSpecResidueField x
    let bY := Y.fromSpecResidueField (f x)
    let TX := {θ : DX ⟶ X // cX ≫ θ = bX ∧ θ ≫ pX = qX ≫ bX ≫ pX}
    let TY := {θ : DY ⟶ Y // cY ≫ θ = bY ∧ θ ≫ pY = qY ≫ bY ≫ pY}
    let hX := (exists_tangentVectors_vectorSpace k X pX x).2.2.2
    let hY := (exists_tangentVectors_vectorSpace k Y pY (f x)).2.2.2
    letI : AddCommGroup TX := Classical.choose hX
    letI : AddCommGroup TY := Classical.choose hY
    letI : Module KX TX := Classical.choose (Classical.choose_spec hX)
    letI : Module KY TY := Classical.choose (Classical.choose_spec hY)
    let e : KY ≃+* KX := RingEquiv.ofBijective (f.residueFieldMap x).hom he
    letI : Module KX TY := Module.compHom TY e.symm.toRingHom
    let d : DY ⟶ DX := Spec.map (CommRingCat.ofHom
      (DualNumber.mapRingHom e.symm.toRingHom))
    ∃ L : TX →ₗ[KX] TY, ∀ θ : TX, (L θ).val = d ≫ θ.val ≫ f := by
  sorry

end AlgebraicGeometry
