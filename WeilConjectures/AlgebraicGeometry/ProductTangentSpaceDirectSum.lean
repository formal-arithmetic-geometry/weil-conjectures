/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SchemeTangentSpace
public import WeilConjectures.PointCount
public import Mathlib.AlgebraicGeometry.Pullbacks
import WeilConjectures.AlgebraicGeometry.TangentMapLinear
import WeilConjectures.AlgebraicGeometry.TangentVectorsVectorSpace

/-!
# Tangent space of a product

Source: Stacks Project, Tag 0BEB, varieties-lemma-tangent-space-product, specialized to `Spec k`
(blueprint: lem-sc-product-tangent-space-direct-sum).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry


private noncomputable abbrev baseResidue (k : Type u) [Field k] (X : Scheme.{u})
    (p : X ⟶ Spec (.of k)) (x : X) : k →+* X.residueField x :=
  (StructureSheaf.toStalk k (p x) ≫ p.stalkMap x ≫ X.residue x).hom

private theorem point_base (k : Type u) [Field k] (X : Scheme.{u})
    (p : X ⟶ Spec (.of k)) (x : X) :
    X.fromSpecResidueField x ≫ p = Spec.map (CommRingCat.ofHom (baseResidue k X p x)) := by
  rw [← p.specMap_residueFieldAlgebraMap]
  congr 2
  rw [Scheme.Hom.residueFieldAlgebraMap, Scheme.Spec.algebraMap_residueFieldIso_inv_assoc,
    Scheme.residue_residueFieldMap]
  rfl

private theorem baseResidue_natural (k : Type u) [Field k] (X Y : Scheme.{u})
    (pX : X ⟶ Spec (.of k)) (pY : Y ⟶ Spec (.of k))
    (f : X ⟶ Y) (hf : f ≫ pY = pX) (x : X) :
    (f.residueFieldMap x).hom.comp (baseResidue k Y pY (f x)) =
      baseResidue k X pX x := by
  suffices h : CommRingCat.ofHom ((f.residueFieldMap x).hom.comp
      (baseResidue k Y pY (f x))) = CommRingCat.ofHom (baseResidue k X pX x) from
    congrArg CommRingCat.Hom.hom h
  apply Spec.map_inj.mp
  rw [CommRingCat.ofHom_comp, Spec.map_comp, ← point_base, ← Category.assoc]
  change (Spec.map (f.residueFieldMap x) ≫ Y.fromSpecResidueField (f x)) ≫ pY = _
  rw [Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField, Category.assoc, hf, point_base]

private theorem rational_image (k : Type u) [Field k] (X Y : Scheme.{u})
    (pX : X ⟶ Spec (.of k)) (pY : Y ⟶ Spec (.of k))
    (f : X ⟶ Y) (hf : f ≫ pY = pX) (x : X)
    (hx : Function.Bijective (baseResidue k X pX x)) :
    Function.Bijective (baseResidue k Y pY (f x)) := by
  refine ⟨(baseResidue k Y pY (f x)).injective, ?_⟩
  intro a
  obtain ⟨b, hb⟩ := hx.2 ((f.residueFieldMap x).hom a)
  refine ⟨b, (f.residueFieldMap x).hom.injective ?_⟩
  exact (DFunLike.congr_fun (baseResidue_natural k X Y pX pY f hf x) b).trans hb

private theorem rational_differential (k : Type u) [Field k] (X Y : Scheme.{u})
    (pX : X ⟶ Spec (.of k)) (pY : Y ⟶ Spec (.of k))
    (f : X ⟶ Y) (hf : f ≫ pY = pX) (x : X) (y : Y) (hxy : f x = y)
    (hx : Function.Bijective (baseResidue k X pX x))
    (hy : Function.Bijective (baseResidue k Y pY y)) :
    let rX := baseResidue k X pX x
    let rY := baseResidue k Y pY y
    let eX := RingEquiv.ofBijective rX hx
    letI : Module k (schemeTangentSpace k X pX x) :=
      Module.compHom (schemeTangentSpace k X pX x) rX
    letI : Module k (schemeTangentSpace k Y pY y) :=
      Module.compHom (schemeTangentSpace k Y pY y) rY
    ∃ L : schemeTangentSpace k X pX x →ₗ[k] schemeTangentSpace k Y pY y,
      ∀ v, (L v).val = Spec.map (CommRingCat.ofHom
        (DualNumber.mapRingHom (rY.comp eX.symm.toRingHom))) ≫ v.val ≫ f := by
  subst y
  dsimp only
  let rX := baseResidue k X pX x
  let rY := baseResidue k Y pY (f x)
  let : Module k (schemeTangentSpace k X pX x) :=
    Module.compHom (schemeTangentSpace k X pX x) rX
  let : Module k (schemeTangentSpace k Y pY (f x)) :=
    Module.compHom (schemeTangentSpace k Y pY (f x)) rY
  have hr (a : k) : (f.residueFieldMap x).hom (rY a) = rX a :=
    DFunLike.congr_fun (baseResidue_natural k X Y pX pY f hf x) a
  have he : Function.Bijective (f.residueFieldMap x).hom := by
    refine ⟨(f.residueFieldMap x).hom.injective, ?_⟩
    intro a
    obtain ⟨b, rfl⟩ := hx.2 a
    exact ⟨rY b, hr b⟩
  let e := RingEquiv.ofBijective (f.residueFieldMap x).hom he
  have her (a : k) : e.symm (rX a) = rY a := by
    apply e.injective
    rw [e.apply_symm_apply]
    exact (hr a).symm
  let : Module (X.residueField x) (schemeTangentSpace k Y pY (f x)) :=
    Module.compHom (schemeTangentSpace k Y pY (f x)) e.symm.toRingHom
  let L : schemeTangentSpace k X pX x →ₗ[X.residueField x]
      schemeTangentSpace k Y pY (f x) := schemeTangentMap k X Y pX pY f hf x he
  have hL (v : schemeTangentSpace k X pX x) : (L v).val =
      Spec.map (CommRingCat.ofHom (DualNumber.mapRingHom e.symm.toRingHom)) ≫ v.val ≫ f :=
    Classical.choose_spec (exists_tangentMap_linear k X Y pX pY f hf x he) v
  let L' : schemeTangentSpace k X pX x →ₗ[k] schemeTangentSpace k Y pY (f x) :=
    { toFun := L
      map_add' := L.map_add
      map_smul' := by
        intro a v
        change L (rX a • v) = rY a • L v
        rw [L.map_smul]
        change e.symm (rX a) • L v = rY a • L v
        rw [her] }
  refine ⟨L', ?_⟩
  intro v
  have hring : e.symm.toRingHom =
      rY.comp (RingEquiv.ofBijective rX hx).symm.toRingHom := by
    apply RingHom.ext
    intro a
    obtain ⟨b, rfl⟩ := hx.2 a
    change e.symm (rX b) = rY ((RingEquiv.ofBijective rX hx).symm (rX b))
    rw [show (RingEquiv.ofBijective rX hx).symm (rX b) = b from
      (RingEquiv.ofBijective rX hx).symm_apply_apply b]
    exact her b
  change (L v).val = _
  have H : (L v).val = Spec.map (CommRingCat.ofHom
      (DualNumber.mapRingHom e.symm.toRingHom)) ≫ v.val ≫ f := hL v
  exact H.trans (congrArg (fun g : X.residueField x →+* Y.residueField (f x) ↦
    Spec.map (CommRingCat.ofHom (DualNumber.mapRingHom g)) ≫ v.val ≫ f) hring)

private theorem dual_inverse {k A B : Type u} [Field k] [Field A] [Field B]
    (eA : k ≃+* A) (eB : k ≃+* B) :
    Spec.map (CommRingCat.ofHom
        (DualNumber.mapRingHom (eB.toRingHom.comp eA.symm.toRingHom))) ≫
      Spec.map (CommRingCat.ofHom
        (DualNumber.mapRingHom (eA.toRingHom.comp eB.symm.toRingHom))) =
      𝟙 (Spec (.of (DualNumber B))) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← DualNumber.mapRingHom_comp]
  have h : (eB.toRingHom.comp eA.symm.toRingHom).comp
      (eA.toRingHom.comp eB.symm.toRingHom) = RingHom.id B := by
    ext a
    simp
  rw [h, DualNumber.mapRingHom_id, CommRingCat.ofHom_id, Spec.map_id]

private theorem tangent_zero (k : Type u) [Field k] (X : Scheme.{u})
    (p : X ⟶ Spec (.of k)) (x : X) :
    (0 : schemeTangentSpace k X p x).val =
      Spec.map (CommRingCat.ofHom
        (TrivSqZeroExt.inlHom (X.residueField x) (X.residueField x))) ≫
        X.fromSpecResidueField x :=
  (Classical.choose_spec
    (Classical.choose_spec (exists_tangentVectors_vectorSpace k X p x).2.2.2)).1

private theorem constant_tangent (k : Type u) [Field k] (X Y : Scheme.{u})
    (pX : X ⟶ Spec (.of k)) (pY : Y ⟶ Spec (.of k)) (x : X) (y : Y)
    (hy : Function.Bijective (baseResidue k Y pY y))
    (v : schemeTangentSpace k X pX x) :
    let eY := RingEquiv.ofBijective (baseResidue k Y pY y) hy
    v.val ≫ pX ≫ Spec.map (CommRingCat.ofHom eY.symm.toRingHom) ≫
        Y.fromSpecResidueField y =
      Spec.map (CommRingCat.ofHom (DualNumber.mapRingHom
          ((baseResidue k X pX x).comp eY.symm.toRingHom))) ≫
        (0 : schemeTangentSpace k Y pY y).val := by
  dsimp only
  rw [← Category.assoc v.val pX, v.property.2, tangent_zero]
  let rX := baseResidue k X pX x
  let eY := RingEquiv.ofBijective (baseResidue k Y pY y) hy
  have H : Spec.map (CommRingCat.ofHom
      (TrivSqZeroExt.inlHom (X.residueField x) (X.residueField x))) ≫
      X.fromSpecResidueField x ≫ pX ≫ Spec.map (CommRingCat.ofHom eY.symm.toRingHom) =
      Spec.map (CommRingCat.ofHom (DualNumber.mapRingHom (rX.comp eY.symm.toRingHom))) ≫
        Spec.map (CommRingCat.ofHom
          (TrivSqZeroExt.inlHom (Y.residueField y) (Y.residueField y))) := by
    rw [← Category.assoc (X.fromSpecResidueField x) pX, point_base]
    rw [← Spec.map_comp, ← Spec.map_comp, ← Spec.map_comp]
    apply congrArg Spec.map
    apply CommRingCat.hom_ext
    change (TrivSqZeroExt.inlHom (X.residueField x) (X.residueField x)).comp
        (rX.comp eY.symm.toRingHom) =
      (DualNumber.mapRingHom (rX.comp eY.symm.toRingHom)).comp
        (TrivSqZeroExt.inlHom (Y.residueField y) (Y.residueField y))
    exact (DualNumber.mapRingHom_comp_inlHom _).symm
  simpa only [Category.assoc] using congrArg (fun g ↦ g ≫ Y.fromSpecResidueField y) H

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
  classical
  intro rX rY hx hy eX eY sx sy P prX prY pZ iX iY z rZ TX TY TZ
  let : Module k TX := Module.compHom TX rX
  let : Module k TY := Module.compHom TY rY
  let : Module k TZ := Module.compHom TZ rZ
  intro dZX dZY
  have hiXX : iX ≫ prX = 𝟙 X := pullback.lift_fst _ _ _
  have hiXY : iX ≫ prY = pX ≫ sy := pullback.lift_snd _ _ _
  have hiYX : iY ≫ prX = pY ≫ sx := pullback.lift_fst _ _ _
  have hiYY : iY ≫ prY = 𝟙 Y := pullback.lift_snd _ _ _
  have hsx : sx ≫ pX = 𝟙 _ := by
    dsimp only [sx]
    rw [Category.assoc, point_base, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have h : eX.symm.toRingHom.comp rX = RingHom.id k :=
      RingHom.ext eX.symm_apply_apply
    rw [h, CommRingCat.ofHom_id, Spec.map_id]
  have hsy : sy ≫ pY = 𝟙 _ := by
    dsimp only [sy]
    rw [Category.assoc, point_base, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have h : eY.symm.toRingHom.comp rY = RingHom.id k :=
      RingHom.ext eY.symm_apply_apply
    rw [h, CommRingCat.ofHom_id, Spec.map_id]
  have hiXp : iX ≫ pZ = pX := by
    simp [iX, pZ, prX, ← Category.assoc]
  have hiYp : iY ≫ pZ = pY := by
    change (iY ≫ prX) ≫ pX = pY
    rw [pullback.lift_fst, Category.assoc, hsx, Category.comp_id]
  have hzX : prX z = x := by
    change (iX ≫ prX) x = x
    simp [iX, prX]
  have hzY : prY z = y := by
    change (iX ≫ prY) x = y
    rw [pullback.lift_snd, Scheme.Hom.comp_apply]
    dsimp only [sy]
    exact Y.fromSpecResidueField_apply y _
  have hpoints : sx ≫ iX = sy ≫ iY := by
    apply pullback.hom_ext
    · change (sx ≫ iX) ≫ prX = (sy ≫ iY) ≫ prX
      simp only [Category.assoc, hiXX, hiYX, Category.comp_id]
      rw [← Category.assoc, hsy, Category.id_comp]
    · change (sx ≫ iX) ≫ prY = (sy ≫ iY) ≫ prY
      simp only [Category.assoc, hiXY, hiYY, Category.comp_id]
      rw [← Category.assoc, hsx, Category.id_comp]
  have hiy : iY y = z := by
    have hsxp (a : Spec (.of k)) : sx a = x := by
      exact X.fromSpecResidueField_apply x _
    have hsyp (a : Spec (.of k)) : sy a = y := by
      exact Y.fromSpecResidueField_apply y _
    have h := congrArg (fun f : Spec (.of k) ⟶ P ↦ f (IsLocalRing.closedPoint k))
      hpoints
    change iX (sx (IsLocalRing.closedPoint k)) = iY (sy (IsLocalRing.closedPoint k)) at h
    rw [hsxp, hsyp] at h
    exact h.symm
  have hz : Function.Bijective rZ := rational_image k X P pX pZ iX hiXp x hx
  obtain ⟨LX, hLX⟩ := rational_differential k P X pZ pX prX rfl z x hzX hz hx
  obtain ⟨LY, hLY⟩ := rational_differential k P Y pZ pY prY
    (pullback.condition (f := pX) (g := pY)).symm z y hzY hz hy
  obtain ⟨IX, hIX⟩ := rational_differential k X P pX pZ iX hiXp x z rfl hx hz
  obtain ⟨IY, hIY⟩ := rational_differential k Y P pY pZ iY hiYp y z hiy hy hz
  let eZ := RingEquiv.ofBijective rZ hz
  let dXZ := Spec.map (CommRingCat.ofHom
    (DualNumber.mapRingHom (rX.comp eZ.symm.toRingHom)))
  let dYZ := Spec.map (CommRingCat.ofHom
    (DualNumber.mapRingHom (rY.comp eZ.symm.toRingHom)))
  have hdX : dZX ≫ dXZ = 𝟙 _ := dual_inverse eX eZ
  have hdX' : dXZ ≫ dZX = 𝟙 _ := dual_inverse eZ eX
  have hdY : dZY ≫ dYZ = 𝟙 _ := dual_inverse eY eZ
  have hdY' : dYZ ≫ dZY = 𝟙 _ := dual_inverse eZ eY
  have : IsIso dZX := ⟨⟨dXZ, hdX, hdX'⟩⟩
  have : IsIso dZY := ⟨⟨dYZ, hdY, hdY'⟩⟩
  have hpX (v : TZ) : v.val ≫ prX = dZX ≫ (LX v).val := by
    rw [hLX]
    change v.val ≫ prX = dZX ≫ dXZ ≫ v.val ≫ prX
    rw [← Category.assoc dZX dXZ, hdX, Category.id_comp]
  have hpY (v : TZ) : v.val ≫ prY = dZY ≫ (LY v).val := by
    rw [hLY]
    change v.val ≫ prY = dZY ≫ dYZ ≫ v.val ≫ prY
    rw [← Category.assoc dZY dYZ, hdY, Category.id_comp]
  have hxi (v : TX) : LX (IX v) = v := by
    apply Subtype.ext
    rw [hLX, hIX]
    change dXZ ≫ (dZX ≫ v.val ≫ iX) ≫ prX = v.val
    simp only [Category.assoc, hiXX, Category.comp_id]
    rw [← Category.assoc dXZ dZX, hdX', Category.id_comp]
  have hyi (w : TY) : LY (IY w) = w := by
    apply Subtype.ext
    rw [hLY, hIY]
    change dYZ ≫ (dZY ≫ w.val ≫ iY) ≫ prY = w.val
    simp only [Category.assoc, hiYY, Category.comp_id]
    rw [← Category.assoc dYZ dZY, hdY', Category.id_comp]
  have hxj (w : TY) : LX (IY w) = 0 := by
    apply Subtype.ext
    apply (cancel_epi dZX).mp
    rw [← hpX, hIY]
    change (dZY ≫ w.val ≫ iY) ≫ prX = dZX ≫ (0 : TX).val
    simp only [Category.assoc, hiYX]
    rw [constant_tangent k Y X pY pX y x hx w]
    rw [← Category.assoc]
    congr 1
    dsimp only [dZY, dZX]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← DualNumber.mapRingHom_comp]
    congr 3
    ext a
    change rZ (eY.symm (rY (eX.symm a))) = rZ (eX.symm a)
    rw [show eY.symm (rY (eX.symm a)) = eX.symm a from eY.symm_apply_apply _]
  have hyj (v : TX) : LY (IX v) = 0 := by
    apply Subtype.ext
    apply (cancel_epi dZY).mp
    rw [← hpY, hIX]
    change (dZX ≫ v.val ≫ iX) ≫ prY = dZY ≫ (0 : TY).val
    simp only [Category.assoc, hiXY]
    rw [constant_tangent k X Y pX pY x y hy v]
    rw [← Category.assoc]
    congr 1
    dsimp only [dZX, dZY]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← DualNumber.mapRingHom_comp]
    congr 3
    ext a
    change rZ (eX.symm (rX (eY.symm a))) = rZ (eY.symm a)
    rw [show eX.symm (rX (eY.symm a)) = eY.symm a from eX.symm_apply_apply _]
  let F : TZ →ₗ[k] TX × TY := LX.prod LY
  let G : TX × TY →ₗ[k] TZ := IX.comp (LinearMap.fst k TX TY) +
    IY.comp (LinearMap.snd k TX TY)
  have hFG (v : TX × TY) : F (G v) = v := by
    apply Prod.ext
    · change LX (IX v.1 + IY v.2) = v.1
      rw [map_add, hxi, hxj, add_zero]
    · change LY (IX v.1 + IY v.2) = v.2
      rw [map_add, hyj, hyi, zero_add]
  have hFinj : Function.Injective F := by
    intro v w h
    apply Subtype.ext
    apply pullback.hom_ext
    · rw [hpX, hpX]
      exact congrArg (fun t : TX × TY ↦ dZX ≫ t.1.val) h
    · rw [hpY, hpY]
      exact congrArg (fun t : TX × TY ↦ dZY ≫ t.2.val) h
  let E : TZ ≃ₗ[k] TX × TY :=
    { F with
      invFun := G
      left_inv := fun v ↦ hFinj (hFG (F v))
      right_inv := hFG }
  refine ⟨E, fun v ↦ ⟨hpX v, hpY v⟩, ?_, ?_⟩
  · intro v
    change (IX v + IY 0).val = dZX ≫ v.val ≫ iX
    rw [map_zero, add_zero]
    exact hIX v
  · intro w
    change (IX 0 + IY w).val = dZY ≫ w.val ≫ iY
    rw [map_zero, zero_add]
    exact hIY w

end AlgebraicGeometry
