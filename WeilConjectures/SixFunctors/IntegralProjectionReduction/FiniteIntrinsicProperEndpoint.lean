/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralProjectionReduction.FiniteIntrinsicRealization.FiniteIntrinsicRealizationComparisons
import WeilConjectures.SixFunctors.IntegralProjectionReduction.FiniteProjectionCoordinateMate

/-! # Endpoint normalization for finite proper projection coordinates

Source: fix-prop-projection-formula.proof.md, coefficient realization endpoints.
(blueprint: lem-sf-finite-intrinsic-proper-endpoint).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale
namespace WeilConjectures.IntegralProjectionReduction
open CompactSupportFiniteProjection FiniteIntrinsicProjectionCoordinates

attribute [local irreducible] CategoryTheory.constantSheaf HasDerivedCategory.standard
  AlgebraicGeometry.Scheme.residueField integralDerivedPullback integralCompletedTensor
  pullbackTensorCalculus
attribute [local implicit_reducible] Equivalence.mapDerivedCategory
  sfIntrinsicDerivedEquivalence CompactSupportFiniteProjection.realization
  sixFunctorFiniteRealization integralCoefficientSheaf integralCoefficientCommRingSheaf
  compactSupportProjectionSquare Over.homMk CostructuredArrow.homMk
  fixedTensor tensor sixFunctorFiniteSupport sfIntrinsicCompactSupport
  sfAmbientCompactSupportCandidate derivedTensorRightDerivedLowerStar

private theorem tensor_map_comp
    {A B : Type*} [Category A] [Category B] (T : A ⥤ A ⥤ A) (F : A ⥤ B)
    {x y z v w : A} (a : x ⟶ y) (b : v ⟶ w) (c : y ⟶ z) :
    F.map ((Functor.uncurry.obj T).map (Prod.mkHom (a ≫ c) b)) =
      F.map ((Functor.uncurry.obj T).map (Prod.mkHom a b)) ≫ F.map ((T.map c).app w) := by
  rw [← F.map_comp]
  congr 1
  simp only [Functor.uncurry_obj_map, Prod.mkHom,
    Functor.map_comp, NatTrans.comp_app, Category.assoc, (T.map c).naturality b]

private theorem transported_tensor_map
    {A B : Type*} [Category A] [Category B] (T : A ⥤ A ⥤ A)
    (G : B ⥤ A) (F : A ⥤ B) {x y v w : B} (a : x ⟶ y) (b : v ⟶ w) :
    (Functor.uncurry.obj ((Functor.postcompose₂.obj F).obj
      ((((Functor.whiskeringLeft₂ _).obj G).obj G).obj T))).map (Prod.mkHom a b) =
      F.map ((Functor.uncurry.obj T).map (Prod.mkHom (G.map a) (G.map b))) := by
  simp only [Functor.uncurry_obj_map, Prod.mkHom,
    Functor.postcompose₂_obj_obj_map_app, Functor.postcompose₂_obj_obj_obj_map,
    Functor.whiskeringLeft₂_obj_obj_obj_map_app, Functor.whiskeringLeft₂_obj_obj_obj_obj_map,
    Functor.map_comp]

private theorem inverse_comparison_endpoint
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    (e : A ≌ B) (f : C ≌ D) (P : B ⥤ D) (Q : A ⥤ C)
    (r : e.functor ⋙ P ≅ Q ⋙ f.functor)
    {M : B} {N : A} (t : M ⟶ e.functor.obj N) :
    f.inverse.map (P.map t ≫ r.hom.app N) ≫ f.unitIso.inv.app (Q.obj N) =
      (FiniteIntrinsicRealization.inverseComparison e f P Q r).hom.app M ≫
        Q.map (e.inverse.map t ≫ e.unitIso.inv.app N) := by
  have h := inverseComparison_evaluation e f P Q r t (𝟙 (Q.obj N))
  have hid : P.map t ≫ r.hom.app N ≫ f.functor.map (𝟙 (Q.obj N)) =
      P.map t ≫ r.hom.app N :=
    (congrArg (fun a ↦ P.map t ≫ r.hom.app N ≫ a)
      (f.functor.map_id (Q.obj N))).trans
        (congrArg (fun a ↦ P.map t ≫ a) (Category.comp_id (r.hom.app N)))
  exact ((congrArg (fun a ↦ f.inverse.map a ≫ f.unitIso.inv.app (Q.obj N))
    hid).symm.trans h).trans
      (congrArg (fun a ↦ (FiniteIntrinsicRealization.inverseComparison e f P Q r).hom.app M ≫ a)
        (Category.comp_id (Q.map (e.inverse.map t ≫ e.unitIso.inv.app N))))

private theorem composed_comparison_app
    {A B C D E F : Type*} [Category A] [Category B] [Category C]
    [Category D] [Category E] [Category F]
    (V : A ⥤ B) (J : B ⥤ C) (R : C ⥤ D) (Jf : A ⥤ E)
    (W : E ⥤ C) (Rf : E ⥤ F) (Z : F ⥤ D)
    (ej : V ⋙ J ≅ Jf ⋙ W) (er : W ⋙ R ≅ Rf ⋙ Z) (x : A) :
    ((Functor.associator V J R).symm ≪≫
        Functor.isoWhiskerRight ej R ≪≫ Functor.associator Jf W R ≪≫
        Functor.isoWhiskerLeft Jf er ≪≫ (Functor.associator Jf Rf Z).symm).hom.app x =
      R.map (ej.hom.app x) ≫ er.hom.app (Jf.obj x) := by
  simp only [Iso.trans_hom, NatTrans.comp_app, Iso.symm_hom,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.comp_id]

private theorem inverse_map_cancel
    {A B : Type*} [Category A] [Category B] (G : A ⥤ B)
    {x y z w v : A} {t : B} (a : x ⟶ y) (e : z ≅ y)
    (b : y ⟶ w) (c : w ⟶ v) (d : G.obj v ⟶ t) :
    G.map (a ≫ e.inv) ≫ G.map (e.hom ≫ b ≫ c) ≫ d =
      G.map (a ≫ b ≫ c) ≫ d := by
  rw [← G.map_comp_assoc]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]

set_option maxHeartbeats 800000 in
-- Comparing the coefficient realizations requires additional elaboration heartbeats.
attribute [-instance] WeilConjectures.IntegralHom.derivedCategory in
/-- The support source endpoint is the explicit inverse-coordinate source endpoint.
This statement contains no proper projection map.
Source: fix-prop-projection-formula.proof.md, coefficient support realization;
Stacks 003G, 03DA and 07A6.
(blueprint: lem-sf-finite-intrinsic-proper-endpoint).

Proof: expand evaluatedTensor and sourceComparison, hence fixedSupportRealization
and supportRealization. Combine successive inverse realization maps. The inverse
S.finiteSupport followed by S.finiteSupport cancels. The remaining map is the open
comparison followed by the normalized derived direct-image comparison. Naturality
of the coefficient counit and the equivalence triangle identities cancel the inner
open unit and outer coefficient counit. Functoriality of the fixed tensor on pairs
then gives the source map equality. Postcompose that equality by the arbitrary q
and associate both sides. No adjunction mate, proper projection or inverse of a
projection occurs. The identity holds for zero inputs, empty spaces and m = 0. -/
theorem intrinsic_proper_endpoint_coordinates
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    {E : Type u} [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] (m : ℕ)
    (S : SixFunctorFiniteOperations D C E (m + 1) (Nat.le_add_left 1 m))
    {X Y : SixFunctorSpace D} (f : X ⟶ Y) (c : Compactification f.hom.left)
    (K : sixFunctorFiniteCategory D C E (m + 1) (Nat.le_add_left 1 m) X)
    (L : finiteTorConstructibleCategory C.l E (m + 1) (Nat.le_add_left 1 m) Y.obj.left)
    (U : normalizedDVRDerived C.l E X.obj.left m)
    (V : normalizedDVRDerived C.l E Y.obj.left m) (k : U ≅ K.obj) (l : V ≅ L.obj) :
    let A := Padic.coefficientExtensionRing C.l E (m + 1)
    let B := ModuleCat.{u + 1} (ULift.{u + 1} A)
    let Q := compactSupportProjectionSquare f c
    let RX := realization (C := C) (E := E) (n := m + 1)
      (hn := Nat.le_add_left 1 m) X
    let RY := realization (C := C) (E := E) (n := m + 1)
      (hn := Nat.le_add_left 1 m) Y
    let J := (sfIntrinsicExtensionByZero c.i A).mapDerivedCategory
    let Jf := (openImmersionLowerShriek B c.i).mapDerivedCategory
    let R := proEtaleConstantDerivedDirectImage c.g A
    let Rf := (lowerStar B c.g).rightDerivedFunctor
    let TY := Functor.uncurry.obj (derivedTensor B Y.obj.left)
    let pj := FiniteIntrinsicRealization.openCoordinate (C := C) (E := E) m f c K U k
    let er := FiniteIntrinsicRealization.inverseDirectImage (C := C) (E := E) m Q.p
    ∀ (W : normalizedDVRDerived C.l E Y.obj.left m)
      (q : RY.functor.obj (((derivedTensorRightDerivedLowerStar B c.g).obj
        (Jf.obj (RX.inverse.obj K.obj))).obj (RY.inverse.obj L.obj)) ⟶ W),
    (canonicalFiniteIntrinsicTensorComparison (C := C) (E := E) m Y).hom.app
        (R.obj (J.obj U), V) ≫
      RY.functor.map (TY.map (Prod.mkHom
        (er.hom.app (J.obj U) ≫ Rf.map pj.hom) (RY.inverse.map l.hom))) ≫ q =
      ((canonicalFiniteIntrinsicTensorComparison (C := C) (E := E) m Y).hom.app
        ((sixFunctorFiniteSupport D C E (m + 1) (Nat.le_add_left 1 m) f c).obj U, V) ≫
        (evaluatedTensor (C := C) (E := E) m Y).map
          (Prod.mkHom ((sixFunctorFiniteSupport D C E (m + 1)
            (Nat.le_add_left 1 m) f c).map k.hom ≫
              (S.finiteSupport f c).inv.app K) l.hom)) ≫
        (sourceComparison S f c K L).hom ≫ q := by
  dsimp only
  intro W q
  let A := Padic.coefficientExtensionRing C.l E (m + 1)
  let B := ModuleCat.{u + 1} (ULift.{u + 1} A)
  let Q := compactSupportProjectionSquare f c
  let RX := realization (C := C) (E := E) (n := m + 1)
    (hn := Nat.le_add_left 1 m) X
  let RY := realization (C := C) (E := E) (n := m + 1)
    (hn := Nat.le_add_left 1 m) Y
  let RZ := realization (C := C) (E := E) (n := m + 1)
    (hn := Nat.le_add_left 1 m) Q.Z
  let J := (sfIntrinsicExtensionByZero c.i A).mapDerivedCategory
  let Jf := (openImmersionLowerShriek B c.i).mapDerivedCategory
  let R := proEtaleConstantDerivedDirectImage c.g A
  let Rf := (lowerStar B c.g).rightDerivedFunctor
  let F := sixFunctorFiniteSupport D C E (m + 1) (Nat.le_add_left 1 m) f c
  let ej := FiniteIntrinsicRealization.openComparison (C := C) (E := E) m f c
  let er := FiniteIntrinsicRealization.inverseDirectImage (C := C) (E := E) m Q.p
  let pj := FiniteIntrinsicRealization.openCoordinate (C := C) (E := E) m f c K U k
  have he := inverse_comparison_endpoint RZ RY R Rf
    (sfIntrinsicDerivedDirectImageComparison c.g A)
    (J.map (k.hom ≫ RX.counitIso.inv.app K.obj) ≫ ej.hom.app (RX.inverse.obj K.obj))
  have he' :
      RY.inverse.map
          (R.map (J.map (k.hom ≫ RX.counitIso.inv.app K.obj) ≫
            ej.hom.app (RX.inverse.obj K.obj)) ≫
            (sfIntrinsicDerivedDirectImageComparison c.g A).hom.app
              (Jf.obj (RX.inverse.obj K.obj))) ≫
        RY.unitIso.inv.app (Rf.obj (Jf.obj (RX.inverse.obj K.obj))) =
      er.hom.app (J.obj U) ≫ Rf.map pj.hom := by
    dsimp only [er, pj, FiniteIntrinsicRealization.openCoordinate,
      FiniteIntrinsicRealization.inverseDirectImage, id, Iso.trans_hom,
      Functor.mapIso_hom, Iso.app_hom, Iso.symm_hom]
    convert he using 1
    rfl
  have hs :
      RY.inverse.map (F.map k.hom ≫ (S.finiteSupport f c).inv.app K) ≫
        (fixedSupportRealization S f c K).hom =
      er.hom.app (J.obj U) ≫ Rf.map pj.hom := by
    rw [← he']
    dsimp only [fixedSupportRealization, supportRealization, id, Iso.trans_hom,
      Functor.mapIso_hom, Iso.app_hom, Iso.symm_hom]
    have hc := inverse_map_cancel RY.inverse (F.map k.hom)
      ((S.finiteSupport f c).app K)
      (F.map (RX.counitIso.app K.obj).inv)
      ((sfIntrinsicCompactSupportComparison A c).hom.app (RX.inverse.obj K.obj))
      (RY.unitIso.app (Rf.obj (Jf.obj (RX.inverse.obj K.obj)))).inv
    refine hc.trans ?_
    have hcmp :
        (sfIntrinsicCompactSupportComparison A c).hom.app (RX.inverse.obj K.obj) =
          R.map (ej.hom.app (RX.inverse.obj K.obj)) ≫
            (sfIntrinsicDerivedDirectImageComparison c.g A).hom.app
              (Jf.obj (RX.inverse.obj K.obj)) := by
      exact composed_comparison_app RX.functor J R Jf RZ.functor Rf RY.functor
        ej (sfIntrinsicDerivedDirectImageComparison c.g A) (RX.inverse.obj K.obj)
    have hmap :
        F.map k.hom ≫ F.map (RX.counitIso.app K.obj).inv ≫
            (sfIntrinsicCompactSupportComparison A c).hom.app (RX.inverse.obj K.obj) =
          R.map (J.map (k.hom ≫ RX.counitIso.inv.app K.obj) ≫
            ej.hom.app (RX.inverse.obj K.obj)) ≫
              (sfIntrinsicDerivedDirectImageComparison c.g A).hom.app
                (Jf.obj (RX.inverse.obj K.obj)) := by
      rw [hcmp]
      change R.map (J.map k.hom) ≫ R.map (J.map (RX.counitIso.app K.obj).inv) ≫
        R.map (ej.hom.app (RX.inverse.obj K.obj)) ≫ _ = _
      simp only [Functor.map_comp, Category.assoc, Iso.app_inv]
    exact congrArg (fun a ↦ RY.inverse.map a ≫
      (RY.unitIso.app (Rf.obj (Jf.obj (RX.inverse.obj K.obj)))).inv) hmap
  simp only [← Category.assoc]
  apply congrArg (fun t ↦ t ≫ q)
  rw [Category.assoc]
  apply congrArg (fun t ↦
    (canonicalFiniteIntrinsicTensorComparison (C := C) (E := E) m Y).hom.app
      (F.obj U, V) ≫ t)
  rw [← hs]
  have ht := tensor_map_comp
    (fixedTensor (C := C) (E := E) (n := m + 1) Y) RY.functor
    (RY.inverse.map (F.map k.hom ≫ (S.finiteSupport f c).inv.app K))
    (RY.inverse.map l.hom) (fixedSupportRealization S f c K).hom
  dsimp only [sourceComparison, projectionTensorLeftRealization, Functor.mapIso_hom,
    Iso.app_hom, evaluatedTensor, tensor, id]
  rw [transported_tensor_map]
  convert ht using 1 <;> rfl

end WeilConjectures.IntegralProjectionReduction
