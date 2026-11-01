/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralProjectionReduction.FiniteIntrinsicRealization.FiniteIntrinsicRealizationComparisons
public import WeilConjectures.AlgebraicGeometry.AmbientClopen.AmbientOrdinaryClopenLocalization
public import WeilConjectures.AlgebraicGeometry.Comparison.ComparisonOpenTensorCoherence
public import WeilConjectures.AlgebraicGeometry.ProEtale.Fixed.ProEtaleFixedScalarRestrictionDirectImage
public import WeilConjectures.CategoryTheory.Adjunction.ProjectionMapCompat
public import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
public import WeilConjectures.CategoryTheory.Exact.ExactLocalizationInverseMate
public import WeilConjectures.SixFunctors.CompactSupportFiniteProjection.FiniteDirectCounitFixedRealizationTransport
public import WeilConjectures.SixFunctors.Finite.FiniteIntrinsicPullbackNormalization
public import WeilConjectures.SixFunctors.Finite.Scalar.FiniteScalarPullbackComparison
public import WeilConjectures.SixFunctors.Finite.Scalar.FiniteScalarPullbackRepresentativeFactorsFactorized
public import WeilConjectures.SixFunctors.Finite.Scalar.Tensor.FiniteScalarTensorPullbackComparison
public import WeilConjectures.SixFunctors.Finite.Scalar.Tensor.FiniteScalarTensorPullbackRepresentatives
public import WeilConjectures.SixFunctors.IntegralProjectionReduction.FiniteProjectionCoordinateMate

/-! # Open core of the finite intrinsic projection square

Source: fix-prop-projection-formula.proof.md, same projection map; Stacks 0B56, 0E8I.
(blueprint: lem-sf-finite-intrinsic-projection-open-square-core).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option Elab.async false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale
namespace WeilConjectures.IntegralProjectionReduction
open CompactSupportFiniteProjection

attribute [local irreducible] CategoryTheory.constantSheaf HasDerivedCategory.standard
  AlgebraicGeometry.Scheme.residueField integralDerivedPullback integralCompletedTensor
  pullbackTensorCalculus sfIntrinsicModuleEquivalence Functor.mapDerivedCategory
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor
  AlgebraicGeometry.ProEtale.derivedTensor finiteIntrinsicDerivedTensor
attribute [local implicit_reducible] Equivalence.mapDerivedCategory
  sfIntrinsicDerivedEquivalence CompactSupportFiniteProjection.realization
  sixFunctorFiniteRealization integralCoefficientSheaf integralCoefficientCommRingSheaf
  compactSupportProjectionSquare fixedTensor tensor
  Over.homMk CostructuredArrow.homMk
  sixFunctorFiniteSupport sfIntrinsicCompactSupport sfAmbientCompactSupportCandidate
  derivedTensorRightDerivedLowerStar


set_option maxHeartbeats 1600000 in
-- Elaborating the two coefficient tensor presentations requires extra heartbeats.
attribute [-instance] WeilConjectures.IntegralHom.derivedCategory in

private theorem invert_projection_square
    {C D : Type*} [Category C] [Category D] [HasZeroMorphisms C]
    (G : C ⥤ D) [G.ReflectsIsomorphisms]
    {A B : C} {X Y Z : D} (p : A ⟶ B)
    (a : X ≅ G.obj A) (b : G.obj B ≅ Y) (d : X ≅ Z) (q : Z ≅ Y)
    (h : a.hom ≫ G.map p ≫ b.hom = d.hom ≫ q.hom) :
    b.hom ≫ q.inv =
      G.map (WeilConjectures.SystemProjectionFormula.inverseOnDomain p) ≫
        a.inv ≫ d.hom := by
  have hp : G.map p = a.inv ≫ d.hom ≫ q.hom ≫ b.inv := by
    rw [← Category.assoc d.hom q.hom b.inv, ← h]
    simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id, Category.comp_id]
  have : IsIso (G.map p) := by rw [hp]; infer_instance
  have : IsIso p := isIso_of_reflects_iso p G
  have hi : WeilConjectures.SystemProjectionFormula.inverseOnDomain p = inv p := by
    simp only [WeilConjectures.SystemProjectionFormula.inverseOnDomain,
      dif_pos (inferInstance : IsIso p)]
  rw [hi, Functor.map_inv]
  apply (cancel_epi (G.map p)).1
  rw [← Category.assoc, ← Category.assoc, ← Category.assoc]
  simp only [IsIso.hom_inv_id, Category.id_comp]
  rw [hp]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id, Category.comp_id]

private theorem inverse_projection_of_unit_tensor
    {C D A B : Type*} [Category C] [Category D] [Category A] [Category B]
    [HasZeroMorphisms D]
    {J : C ⥤ D} {P : D ⥤ C} {Jf : A ⥤ B} {Pe Pf : B ⥤ A}
    (a : J ⊣ P) (af : Jf ⊣ Pe)
    (F : C ⥤ A) (G : D ⥤ B) [G.ReflectsIsomorphisms]
    (I : C ⥤ C ⥤ C) (T : D ⥤ D ⥤ D)
    (tx : A ⥤ A ⥤ A) (tz : B ⥤ B ⥤ B)
    (di : (((whiskeringLeft₂ C).obj P).obj P).obj I ⟶ (postcompose₂.obj P).obj T)
    (df : (((whiskeringLeft₂ A).obj Pe).obj Pf).obj tx ⟶ (postcompose₂.obj Pe).obj tz)
    (qx : (postcompose₂.obj F).obj I ≅ (((whiskeringLeft₂ A).obj F).obj F).obj tx)
    (qz : (postcompose₂.obj G).obj T ≅ (((whiskeringLeft₂ B).obj G).obj G).obj tz)
    (tau : P ⋙ F ≅ G ⋙ Pe) (ep : P ⋙ F ≅ G ⋙ Pf)
    (beta : F ⋙ Jf ≅ J ⋙ G)
    (pf : (postcompose₂.obj Jf).obj ((((whiskeringLeft₂ A).obj (𝟭 A)).obj Pf).obj tx) ≅
      (((whiskeringLeft₂ B).obj Jf).obj (𝟭 B)).obj tz)
    (hpf : pf.hom = af.projectionMap Pf tx tz df)
    (hu : ∀ K, af.unit.app (F.obj K) ≫ Pe.map (beta.hom.app K) =
      F.map (a.unit.app K) ≫ tau.hom.app (J.obj K))
    (ht : ∀ X Y, F.map ((di.app X).app Y) ≫ tau.hom.app ((T.obj X).obj Y) ≫
        Pe.map ((qz.hom.app X).app Y) =
      (qx.hom.app (P.obj X)).app (P.obj Y) ≫ (tx.map (tau.hom.app X)).app _ ≫
        (tx.obj _).map (ep.hom.app Y) ≫ (df.app (G.obj X)).app (G.obj Y))
    (K : C) (N : D) :
    (qz.hom.app (J.obj K)).app N ≫ (tz.map (beta.inv.app K)).app (G.obj N) ≫
        (pf.inv.app (F.obj K)).app (G.obj N) =
      G.map (WeilConjectures.SystemProjectionFormula.inverseOnDomain
        (((a.projectionMap P I T di).app K).app N)) ≫
        beta.inv.app ((I.obj K).obj (P.obj N)) ≫
        Jf.map ((qx.hom.app K).app (P.obj N)) ≫
        Jf.map ((tx.obj (F.obj K)).map (ep.hom.app N)) := by
  have h := a.projectionMap_mate af P Pf di df qx.hom qz.hom tau.hom ep.hom
    beta.hom hu ht K N
  rw [← hpf] at h
  let d := Jf.mapIso ((qx.app K).app (P.obj N)) ≪≫
    Jf.mapIso ((tx.obj (F.obj K)).mapIso (ep.app N))
  let q := (pf.app (F.obj K)).app (G.obj N) ≪≫
    (tz.mapIso (beta.app K)).app (G.obj N)
  have hi := invert_projection_square G (((a.projectionMap P I T di).app K).app N)
    (beta.app ((I.obj K).obj (P.obj N))) ((qz.app (J.obj K)).app N) d q (by
      simpa only [d, q, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom,
        Category.assoc] using h)
  simpa only [d, q, Iso.trans_inv, Iso.trans_hom, Functor.mapIso_hom,
    Functor.mapIso_inv, Iso.app_hom, Iso.app_inv, Category.assoc] using hi

private theorem inverse_open_coordinate
    {A C B D : Type*} [Category A] [Category C] [Category B] [Category D]
    (e : A ≌ C) (g : B ≌ D) (J : C ⥤ D) (Jf : A ⥤ B)
    (ej : e.functor ⋙ J ≅ Jf ⋙ g.functor)
    {U M : C} (k : U ≅ M) :
    (g.inverse.mapIso
      (J.mapIso (k ≪≫ (e.counitIso.app M).symm) ≪≫ ej.app (e.inverse.obj M)) ≪≫
        (g.unitIso.app _).symm).hom =
      (FiniteIntrinsicRealization.inverseComparison
        e g J Jf ej).hom.app U ≫ Jf.map (e.inverse.map k.hom) := by
  have h := WeilConjectures.IntegralProjectionReduction.inverseComparison_evaluation
    e g J Jf ej (k.hom ≫ e.counitIso.inv.app M) (𝟙 _)
  simp only [Functor.map_comp, CategoryTheory.Functor.map_id, Category.comp_id,
    Equivalence.inverse_counitInv_comp, Category.assoc] at h
  erw [g.inverse.map_id, Category.id_comp, Category.comp_id] at h
  simpa only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Iso.app_hom,
    NatTrans.comp_app, Functor.map_comp, CategoryTheory.Functor.map_id, Category.comp_id,
    Iso.app_inv, Category.assoc] using h

private def inverse_tensor_coordinates
    {A C : Type*} [Category A] [Category C] (e : A ≌ C)
    (t : A × A ⥤ A) (T : C × C ⥤ C)
    (s : T ≅ (e.inverse.prod e.inverse) ⋙ t ⋙ e.functor) :
    T ⋙ e.inverse ≅ (e.inverse.prod e.inverse) ⋙ t :=
  Functor.isoWhiskerRight s e.inverse ≪≫
    Functor.isoWhiskerLeft ((e.inverse.prod e.inverse) ⋙ t) e.unitIso.symm

private theorem inverse_tensor_app
    {A C : Type*} [Category A] [Category C] (e : A ≌ C)
    (t : A × A ⥤ A) (T : C × C ⥤ C)
    (s : T ≅ (e.inverse.prod e.inverse) ⋙ t ⋙ e.functor) (U V : C) :
    (inverse_tensor_coordinates e t T s).hom.app (U, V) =
      e.inverse.map (s.hom.app (U, V)) ≫
        e.unitIso.inv.app (t.obj (e.inverse.obj U, e.inverse.obj V)) := rfl

private theorem fixed_open_inverse_naturality
    {A B : Type*} [Category A] [Category B]
    (J : A ⥤ B) (P : B ⥤ A) (tx : A ⥤ A ⥤ A) (tz : B ⥤ B ⥤ B)
    (pf : (postcompose₂.obj J).obj ((((whiskeringLeft₂ A).obj (𝟭 A)).obj P).obj tx) ≅
      (((whiskeringLeft₂ B).obj J).obj (𝟭 B)).obj tz)
    {K K' : A} {N N' : B} (k : K ⟶ K') (b : N ⟶ N') :
    (Functor.uncurry.obj tz).map (Prod.mkHom (J.map k) b) ≫
        (pf.inv.app K').app N' =
      (pf.inv.app K).app N ≫
        J.map ((Functor.uncurry.obj tx).map (Prod.mkHom k (P.map b))) := by
  simpa only [Functor.uncurry_obj_map, Functor.uncurry_map_app, Functor.id_obj, Prod.mkHom,
    Functor.whiskeringLeft₂_obj_obj_obj_map_app,
    Functor.whiskeringLeft₂_obj_obj_obj_obj_map,
    Functor.postcompose₂_obj_obj_map_app, Functor.postcompose₂_obj_obj_obj_map,
    Functor.id_map, Functor.map_comp, Category.assoc] using
      (Functor.uncurry.map pf.inv).naturality (Prod.mkHom k b)

private theorem open_square_of_inverse_coordinates
    {A C B D : Type*} [Category A] [Category C] [Category B] [Category D]
    [HasZeroMorphisms D]
    (e : A ≌ C) (g : B ≌ D) (J : C ⥤ D) (P : D ⥤ C)
    (Jf : A ⥤ B) (Pf : B ⥤ A)
    (Tx : C × C ⥤ C) (Tz : D × D ⥤ D)
    (tx : A ⥤ A ⥤ A) (tz : B ⥤ B ⥤ B)
    (sx : Tx ≅ (e.inverse.prod e.inverse) ⋙ uncurry.obj tx ⋙ e.functor)
    (sz : Tz ≅ (g.inverse.prod g.inverse) ⋙ uncurry.obj tz ⋙ g.functor)
    (ej : e.functor ⋙ J ≅ Jf ⋙ g.functor)
    (ep : P ⋙ e.inverse ≅ g.inverse ⋙ Pf)
    (pf : (postcompose₂.obj Jf).obj ((((whiskeringLeft₂ A).obj (𝟭 A)).obj Pf).obj tx) ≅
      (((whiskeringLeft₂ B).obj Jf).obj (𝟭 B)).obj tz)
    (p : ∀ U N, J.obj (Tx.obj (U, P.obj N)) ⟶ Tz.obj (J.obj U, N))
    (h : ∀ U N,
      (inverse_tensor_coordinates g (uncurry.obj tz) Tz sz).hom.app (J.obj U, N) ≫
          (uncurry.obj tz).map (Prod.mkHom
            ((FiniteIntrinsicRealization.inverseComparison
              e g J Jf ej).hom.app U) (𝟙 _)) ≫
          (pf.inv.app (e.inverse.obj U)).app (g.inverse.obj N) =
        g.inverse.map (WeilConjectures.SystemProjectionFormula.inverseOnDomain (p U N)) ≫
          (FiniteIntrinsicRealization.inverseComparison
            e g J Jf ej).hom.app (Tx.obj (U, P.obj N)) ≫
          Jf.map ((inverse_tensor_coordinates e (uncurry.obj tx) Tx sx).hom.app
            (U, P.obj N)) ≫
          Jf.map ((uncurry.obj tx).map (Prod.mkHom (𝟙 _) (ep.hom.app N))))
    (U M : C) (N : D) (k : U ≅ M) (W : B) (b : g.inverse.obj N ⟶ W) :
    sz.hom.app (J.obj U, N) ≫
        g.functor.map ((uncurry.obj tz).map (Prod.mkHom
          ((g.inverse.mapIso
            (J.mapIso (k ≪≫ (e.counitIso.app M).symm) ≪≫
              ej.app (e.inverse.obj M)) ≪≫ (g.unitIso.app _).symm).hom) b)) ≫
        g.functor.map ((pf.inv.app (e.inverse.obj M)).app W) =
      WeilConjectures.SystemProjectionFormula.inverseOnDomain (p U N) ≫
        J.map (sx.hom.app (U, P.obj N)) ≫
        ej.hom.app ((uncurry.obj tx).obj (e.inverse.obj U, e.inverse.obj (P.obj N))) ≫
        g.functor.map (Jf.map ((uncurry.obj tx).map
          (Prod.mkHom (𝟙 _) (ep.hom.app N)))) ≫
        g.functor.map (Jf.map ((uncurry.obj tx).map
          (Prod.mkHom (e.inverse.map k.hom) (Pf.map b)))) := by
  let z := FiniteIntrinsicRealization.inverseComparison
    e g J Jf ej
  let base := (uncurry.obj tz).map (Prod.mkHom (z.hom.app U) (𝟙 (g.inverse.obj N))) ≫
    (pf.inv.app (e.inverse.obj U)).app (g.inverse.obj N)
  have hb : WeilConjectures.SystemProjectionFormula.inverseOnDomain (p U N) ≫
      J.map (sx.hom.app (U, P.obj N)) ≫
      ej.hom.app ((uncurry.obj tx).obj (e.inverse.obj U, e.inverse.obj (P.obj N))) ≫
      g.functor.map (Jf.map ((uncurry.obj tx).map
        (Prod.mkHom (𝟙 _) (ep.hom.app N)))) =
      sz.hom.app (J.obj U, N) ≫ g.functor.map base := by
    apply WeilConjectures.IntegralProjectionReduction.forward_of_inverse_equation
      e g J Jf ej
    simpa only [inverse_tensor_app, Functor.map_comp, Functor.prod_obj, Category.assoc, base, z]
      using (h U N).symm
  have hn := fixed_open_inverse_naturality Jf Pf tx tz pf (e.inverse.map k.hom) b
  have hm : (uncurry.obj tz).map
      (Prod.mkHom
        ((g.inverse.mapIso
          (J.mapIso (k ≪≫ (e.counitIso.app M).symm) ≪≫
            ej.app (e.inverse.obj M)) ≪≫ (g.unitIso.app _).symm).hom) b) ≫
        (pf.inv.app (e.inverse.obj M)).app W =
      base ≫ Jf.map ((uncurry.obj tx).map
        (Prod.mkHom (e.inverse.map k.hom) (Pf.map b))) := by
    rw [inverse_open_coordinate]
    have hh : Prod.mkHom (z.hom.app U ≫ Jf.map (e.inverse.map k.hom)) b =
        Prod.mkHom (z.hom.app U) (𝟙 (g.inverse.obj N)) ≫
          Prod.mkHom (Jf.map (e.inverse.map k.hom)) b := by ext <;> simp
    rw [hh, Functor.map_comp, Category.assoc, hn]
    simp only [base, Category.assoc]
  rw [← g.functor.map_comp, hm, g.functor.map_comp]
  simpa only [Category.assoc] using congrArg
    (fun q ↦ q ≫ g.functor.map (Jf.map ((uncurry.obj tx).map
      (Prod.mkHom (e.inverse.map k.hom) (Pf.map b))))) hb.symm

private def inverse_curried_tensor_coordinates
    {A C : Type*} [Category A] [Category C] (e : A ≌ C)
    (t : A ⥤ A ⥤ A) (T : C × C ⥤ C)
    (s : T ≅ (e.inverse.prod e.inverse) ⋙ uncurry.obj t ⋙ e.functor) :
    (postcompose₂.obj e.inverse).obj (curry.obj T) ≅
      (((whiskeringLeft₂ A).obj e.inverse).obj e.inverse).obj t := by
  let z := inverse_tensor_coordinates e (uncurry.obj t) T s
  refine NatIso.ofComponents (fun U ↦ NatIso.ofComponents (fun V ↦ z.app (U,V)) ?_) ?_
  · intro V V' f
    have h := z.hom.naturality (Prod.mkHom (𝟙 U) f)
    simp only [Functor.comp_map, Functor.prod_map, Functor.prod_obj,
      Functor.uncurry_obj_map] at h
    erw [e.inverse.map_id, t.map_id] at h
    simpa only [z, Functor.prod_obj, Iso.app_hom,
      Functor.uncurry_obj_map,
      CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp,
      Functor.curry_obj_obj_map, Functor.postcompose₂_obj_obj_obj_map,
      Functor.whiskeringLeft₂_obj_obj_obj_obj_map] using h
  · intro U U' f
    apply NatTrans.ext
    ext V
    have h := z.hom.naturality (Prod.mkHom f (𝟙 V))
    simp only [Functor.comp_map, Functor.prod_map, Functor.prod_obj,
      Functor.uncurry_obj_map] at h
    erw [e.inverse.map_id, (t.obj (e.inverse.obj U')).map_id] at h
    simpa only [NatTrans.comp_app, NatIso.ofComponents_hom_app, Functor.prod_obj, Iso.app_hom,
      Functor.uncurry_obj_map,
      CategoryTheory.Functor.map_id, Category.comp_id, Functor.curry_obj_map_app,
      Functor.postcompose₂_obj_obj_map_app,
      Functor.whiskeringLeft₂_obj_obj_obj_map_app] using h

private def uncurry_precompose_iso
    {A C : Type*} [Category A] [Category C] (F : C ⥤ A) (t : A ⥤ A ⥤ A) :
    uncurry.obj ((((whiskeringLeft₂ A).obj F).obj F).obj t) ≅
      (F.prod F) ⋙ uncurry.obj t :=
  uncurry.mapIso ((((whiskeringLeft₂ A).obj F).obj F).mapIso
      (currying.unitIso.app t)) ≪≫
    (uncurry.mapIso (curryObjProdComp F F (uncurry.obj t))).symm ≪≫
    currying.counitIso.app ((F.prod F) ⋙ uncurry.obj t)

private def tensor_coordinate_iso
    {A C : Type*} [Category A] [Category C] (e : A ≌ C) (t : A ⥤ A ⥤ A) :
    uncurry.obj ((postcompose₂.obj e.functor).obj
      ((((whiskeringLeft₂ A).obj e.inverse).obj e.inverse).obj t)) ≅
        (e.inverse.prod e.inverse) ⋙ uncurry.obj t ⋙ e.functor :=
  (WeilConjectures.finiteScalarUncurryPostcomposeIso _ e.functor).symm ≪≫
    isoWhiskerRight (uncurry_precompose_iso e.inverse t) e.functor

private theorem tensor_coordinate_iso_hom_app
    {A C : Type*} [Category A] [Category C] (e : A ≌ C) (t : A ⥤ A ⥤ A)
    (V W : C) : (tensor_coordinate_iso e t).hom.app (V,W) = 𝟙 _ := by
  simp [tensor_coordinate_iso, uncurry_precompose_iso,
    WeilConjectures.finiteScalarUncurryPostcomposeIso, Functor.currying,
    Functor.curryObjProdComp]

private theorem tensor_coordinate_iso_inv_app
    {A C : Type*} [Category A] [Category C] (e : A ≌ C) (t : A ⥤ A ⥤ A)
    (V W : C) : (tensor_coordinate_iso e t).inv.app (V,W) = 𝟙 _ := by
  have h := tensor_coordinate_iso_hom_app e t V W
  have hc := (tensor_coordinate_iso e t).hom_inv_id_app (V,W)
  rw [h, Category.id_comp] at hc
  exact hc

private theorem exact_square_unit
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    [Abelian A] [Abelian B] [Abelian C] [Abelian D]
    [HasDerivedCategory A] [HasDerivedCategory B]
    [HasDerivedCategory C] [HasDerivedCategory D]
    {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : C ⥤ D} {R₂ : D ⥤ C}
    {G : A ⥤ C} {H : B ⥤ D}
    [L₁.Additive] [R₁.Additive] [L₂.Additive] [R₂.Additive]
    [G.Additive] [H.Additive]
    [PreservesFiniteLimits L₁] [PreservesFiniteColimits L₁]
    [PreservesFiniteLimits R₁] [PreservesFiniteColimits R₁]
    [PreservesFiniteLimits L₂] [PreservesFiniteColimits L₂]
    [PreservesFiniteLimits R₂] [PreservesFiniteColimits R₂]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂) (d : R₁ ⋙ G ≅ H ⋙ R₂)
    (β : G ⋙ L₂ ≅ L₁ ⋙ H)
    (hβ : ∀ K, a₂.unit.app (G.obj K) ≫ R₂.map (β.hom.app K) =
      G.map (a₁.unit.app K) ≫ d.hom.app (L₁.obj K))
    (K : DerivedCategory A) :
    a₂.mapExactDerivedCategory.unit.app (G.mapDerivedCategory.obj K) ≫
        R₂.mapDerivedCategory.map ((Functor.mapDerivedCategorySquareIso β).hom.app K) =
      G.mapDerivedCategory.map (a₁.mapExactDerivedCategory.unit.app K) ≫
        (Functor.mapDerivedCategorySquareIso d).hom.app (L₁.mapDerivedCategory.obj K) := by
  let l : G.mapDerivedCategory ⟶
      L₁.mapDerivedCategory ⋙ H.mapDerivedCategory ⋙ R₂.mapDerivedCategory :=
    Functor.whiskerLeft G.mapDerivedCategory a₂.mapExactDerivedCategory.unit ≫
      Functor.whiskerRight (Functor.mapDerivedCategorySquareIso β).hom R₂.mapDerivedCategory
  let r : G.mapDerivedCategory ⟶
      L₁.mapDerivedCategory ⋙ H.mapDerivedCategory ⋙ R₂.mapDerivedCategory :=
    Functor.whiskerRight a₁.mapExactDerivedCategory.unit G.mapDerivedCategory ≫
      Functor.whiskerLeft L₁.mapDerivedCategory (Functor.mapDerivedCategorySquareIso d).hom
  have h : l = r := by
    refine Localization.natTrans_ext DerivedCategory.Q
      (HomologicalComplex.quasiIso A (.up ℤ)) (fun Q ↦ ?_)
    exact CategoryTheory.mate_unit_Q a₁ a₂ d β hβ Q
  exact NatTrans.congr_app h K

private theorem coordinate_unit
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    (e : A ≌ C) (g : B ≌ D) {J : A ⥤ B} {P : B ⥤ A} (af : J ⊣ P)
    {Ji : C ⥤ D} {Pi : D ⥤ C} (ai : Ji ⊣ Pi)
    (o : Pi ≅ g.inverse ⋙ P ⋙ e.functor)
    (ej : e.functor ⋙ Ji ≅ J ⋙ g.functor)
    (d : P ⋙ e.functor ≅ g.functor ⋙ Pi)
    (hu : ∀ K, ai.unit.app (e.functor.obj K) ≫ Pi.map (ej.hom.app K) =
      e.functor.map (af.unit.app K) ≫ d.hom.app (J.obj K))
    (ho : ∀ N, o.hom.app N ≫ d.hom.app (g.inverse.obj N) =
      Pi.map (g.counitIso.inv.app N)) (K : C) :
    let z :=
      FiniteIntrinsicRealization.inverseComparison
      e g Ji J ej
    let t := Functor.isoWhiskerRight o e.inverse ≪≫
      Functor.isoWhiskerLeft (g.inverse ⋙ P) e.unitIso.symm
    af.unit.app (e.inverse.obj K) ≫ P.map (z.inv.app K) =
      e.inverse.map (ai.unit.app K) ≫ t.hom.app (Ji.obj K) := by
  dsimp only
  let z :=
      FiniteIntrinsicRealization.inverseComparison
    e g Ji J ej
  let t := Functor.isoWhiskerRight o e.inverse ≪≫
    Functor.isoWhiskerLeft (g.inverse ⋙ P) e.unitIso.symm
  have hd (Q : B) : o.hom.app (g.functor.obj Q) ≫
      e.functor.map (P.map (g.unitIso.inv.app Q)) = d.inv.app Q := by
    apply (cancel_mono (d.hom.app Q)).1
    have hn := d.hom.naturality (g.unitIso.inv.app Q)
    dsimp only [Functor.comp_map, Functor.comp_obj, Functor.id_obj] at hn
    rw [Category.assoc, hn, ← Category.assoc, ho, ← Pi.map_comp]
    simp only [Equivalence.counitInv_app_functor, ← g.functor.map_comp,
      Iso.hom_inv_id_app, Iso.inv_hom_id_app]
    erw [g.functor.map_id, Pi.map_id]
    rfl
  have ht (N : D) : e.counitIso.inv.app (Pi.obj N) ≫
      e.functor.map (t.hom.app N) = o.hom.app N := by
    dsimp only [t, Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
      Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      Iso.symm_hom]
    rw [Functor.map_comp, ← Category.assoc]
    erw [← e.counitIso.inv.naturality]
    dsimp only [Functor.comp_obj, Functor.id_map]
    rw [Category.assoc]
    erw [Equivalence.counitIso_functor_comp]
    exact Category.comp_id _
  change af.unit.app (e.inverse.obj K) ≫ P.map (z.inv.app K) =
    e.inverse.map (ai.unit.app K) ≫ t.hom.app (Ji.obj K)
  apply (cancel_mono (P.map (z.hom.app K))).1
  simp only [Category.assoc, ← P.map_comp, Iso.inv_hom_id_app]
  symm
  apply e.functor.map_injective
  apply (cancel_epi (e.counitIso.inv.app K)).1
  simp only [Functor.map_comp]
  erw [← e.counitIso.inv.naturality_assoc]
  dsimp only [Functor.id_map, Functor.comp_obj]
  rw [reassoc_of% (ht (Ji.obj K))]
  dsimp only [z,
    FiniteIntrinsicRealization.inverseComparison,
    Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Iso.symm_hom]
  simp only [Functor.map_comp]
  have hn := o.hom.naturality (Ji.map (e.counitIso.inv.app K) ≫
    ej.hom.app (e.inverse.obj K))
  dsimp only [Functor.comp_map, Functor.comp_obj, Functor.id_obj] at hn
  simp only [Functor.map_comp, Category.assoc] at hn
  dsimp only [Functor.comp_map, Functor.comp_obj]
  erw [P.map_id, e.functor.map_id]
  simp only [Category.comp_id]
  rw [← reassoc_of% hn, hd]
  erw [← ai.unit.naturality_assoc]
  simp only [Functor.id_map]
  rw [reassoc_of% (hu (e.inverse.obj K))]
  simp only [Iso.hom_inv_id_app]
  erw [Category.comp_id]

private theorem conjugated_forward_unit
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    (e : A ≌ C) (g : B ≌ D) {J : A ⥤ B} {P : B ⥤ A} (a : J ⊣ P) (K : A) :
    (((e.symm.toAdjunction.comp a).comp g.toAdjunction).unit).app (e.functor.obj K) ≫
        (g.inverse ⋙ P ⋙ e.functor).map
          ((e.funInvIdAssoc (J ⋙ g.functor)).hom.app K) =
      e.functor.map (a.unit.app K) ≫
        ((g.funInvIdAssoc (P ⋙ e.functor)).inv.app (J.obj K)) := by
  simp only [Adjunction.comp_unit_app, Equivalence.toAdjunction_unit,
    Equivalence.symm_unit, Equivalence.funInvIdAssoc_hom_app,
    Equivalence.funInvIdAssoc_inv_app, Functor.comp_map, Category.assoc,
    Equivalence.counitInv_app_functor]
  dsimp only [Equivalence.symm_functor, Equivalence.symm_inverse, Functor.comp_obj]
  have hg := g.unitIso.hom.naturality (J.map (e.unitIso.inv.app K))
  dsimp only [Functor.id_map, Functor.comp_map, Functor.comp_obj, Functor.id_obj] at hg
  have ha := a.unit.naturality (e.unitIso.inv.app K)
  dsimp only [Functor.id_map, Functor.comp_map, Functor.comp_obj, Functor.id_obj] at ha
  simp only [← e.functor.map_comp]
  apply congrArg e.functor.map
  simp only [Equivalence.unit, Equivalence.unitInv]
  rw [← P.map_comp, ← hg, P.map_comp]
  rw [← Category.assoc (a.unit.app _), ← ha]
  simp only [← Category.assoc, Iso.hom_inv_id_app, Category.id_comp]

private theorem symm_functor_additive
    {A C : Type*} [Category A] [Category C] [Preadditive A] [Preadditive C]
    (e : A ≌ C) [e.inverse.Additive] : e.symm.functor.Additive :=
  (inferInstance : e.inverse.Additive)

private theorem symm_inverse_additive
    {A C : Type*} [Category A] [Category C] [Preadditive A] [Preadditive C]
    (e : A ≌ C) [e.functor.Additive] : e.symm.inverse.Additive :=
  (inferInstance : e.functor.Additive)

private theorem derived_conjugate_unit
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    [Abelian A] [Abelian B] [Abelian C] [Abelian D]
    [HasDerivedCategory A] [HasDerivedCategory B]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (e : A ≌ C) (g : B ≌ D)
    [e.functor.Additive] [e.inverse.Additive] [g.functor.Additive] [g.inverse.Additive]
    {J : A ⥤ B} {P : B ⥤ A} [J.Additive] [P.Additive]
    [PreservesFiniteLimits J] [PreservesFiniteColimits J]
    [PreservesFiniteLimits P] [PreservesFiniteColimits P] (a : J ⊣ P)
    (K : DerivedCategory C) :
    let Ji := e.inverse ⋙ J ⋙ g.functor
    let _Pi := g.inverse ⋙ P ⋙ e.functor
    let ai := ((e.symm.toAdjunction.comp a).comp g.toAdjunction).mapExactDerivedCategory
    let ej := Functor.mapDerivedCategorySquareIso (e.funInvIdAssoc (J ⋙ g.functor))
    let o := Functor.mapDerivedCategoryCompIso g.inverse (P ⋙ e.functor) ≪≫
      Functor.isoWhiskerLeft g.inverse.mapDerivedCategory
        (Functor.mapDerivedCategoryCompIso P e.functor)
    let t := Functor.isoWhiskerRight o e.mapDerivedCategory.inverse ≪≫
      Functor.isoWhiskerLeft (g.mapDerivedCategory.inverse ⋙ P.mapDerivedCategory)
        e.mapDerivedCategory.unitIso.symm
    let z :=
      FiniteIntrinsicRealization.inverseComparison
      e.mapDerivedCategory g.mapDerivedCategory Ji.mapDerivedCategory J.mapDerivedCategory ej
    a.mapExactDerivedCategory.unit.app (e.mapDerivedCategory.inverse.obj K) ≫
        P.mapDerivedCategory.map (z.inv.app K) =
      e.mapDerivedCategory.inverse.map (ai.unit.app K) ≫
        t.hom.app (Ji.mapDerivedCategory.obj K) := by
  dsimp only
  let ad := ((e.symm.toAdjunction.comp a).comp g.toAdjunction).mapExactDerivedCategory
  let d := (g.funInvIdAssoc (P ⋙ e.functor)).symm
  let β := e.funInvIdAssoc (J ⋙ g.functor)
  let od := Functor.mapDerivedCategoryCompIso g.inverse (P ⋙ e.functor) ≪≫
    Functor.isoWhiskerLeft g.inverse.mapDerivedCategory
      (Functor.mapDerivedCategoryCompIso P e.functor)
  apply coordinate_unit e.mapDerivedCategory g.mapDerivedCategory a.mapExactDerivedCategory ad od
    (Functor.mapDerivedCategorySquareIso β) (Functor.mapDerivedCategorySquareIso d)
  · intro L
    exact exact_square_unit a ((e.symm.toAdjunction.comp a).comp g.toAdjunction) d β
      (conjugated_forward_unit e g a) L
  · intro N
    exact derived_square_coherence g P e.functor N

private theorem cancel_left_comparison
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    (e : A ≌ C) (G : D ⥤ B) {P Q : B ⥤ A} (s : P ≅ Q)
    (Pi : D ⥤ C) (o : Pi ≅ G ⋙ Q ⋙ e.functor) (N : D) :
    ((Functor.isoWhiskerRight
      (o ≪≫ Functor.isoWhiskerLeft G (Functor.isoWhiskerRight s.symm e.functor)) e.inverse ≪≫
        Functor.isoWhiskerLeft (G ⋙ P) e.unitIso.symm) ≪≫
      Functor.isoWhiskerLeft G s).hom.app N =
    (Functor.isoWhiskerRight o e.inverse ≪≫
      Functor.isoWhiskerLeft (G ⋙ Q) e.unitIso.symm).hom.app N := by
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Functor.map_comp, Category.assoc]
  erw [e.unitIso.inv.naturality_assoc]
  simp only [Functor.id_map, Iso.inv_hom_id_app]
  dsimp only [Functor.comp_obj]
  erw [Category.comp_id]

private theorem finiteScalarTensorPullbackComparisonCanonical
    (R : Type u) [CommRing R] [Finite R]
    {X Y : Scheme.{u}} (p : X ⟶ Y)
    (aX : ProEtaleTensorModel X (proEtaleConstantRing X R))
    (aY : ProEtaleTensorModel Y (proEtaleConstantRing Y R)) :
    Adjunction.ComparisonCompatible (finiteScalarPullbackComparison R p)
      (ProEtale.leftDerivedUpperStarTensorComparison
        (ModuleCat.{u + 1} (ULift.{u + 1} R)) p)
      (finiteScalarCurriedTensorPullback R p aX aY)
      (finiteScalarTensorRealization X R aX) (finiteScalarTensorRealization Y R aY) := by
  let C := Sheaf (ProEt.topology Y) (ModuleCat.{u + 1} (ULift.{u + 1} R))
  let q := DerivedCategory.Q (C := C)
  refine tensorComparisonCompatible_of_representatives q
    (finiteScalarFlatRepresentatives Y R) ?_ _ _ _ _ _ ?_
  · intro Z
    obtain ⟨P, f, hf, hflat, hk⟩ :=
      CochainComplex.exists_quasiIso_flat_kFlat (q.objPreimage Z)
    have : QuasiIso f := hf
    exact ⟨P, ⟨hk, hflat⟩, ⟨asIso (q.map f) ≪≫ q.objObjPreimageIso Z⟩⟩
  · intro P Q hp hq
    exact finiteScalarTensorPullback_onRepresentatives R p aX aY P Q hp hq

private theorem scalarPullback_exact
    (R : Type u) [CommRing R] [Finite R] {X Y : Scheme.{u}} (p : X ⟶ Y) :
    (finiteScalarPullbackComparison R p).hom ≫
      Functor.whiskerRight
        (ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} R)) p
          ).leftDerivedFunctorIsoMapDerivedCategory.hom
        (sfIntrinsicDerivedEquivalence X R).functor =
      (Functor.mapDerivedCategorySquareIso (finiteScalarOrdinaryPullbackComparison R p)).hom := by
  let L := ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} R)) p
  let L' := proEtaleRingModulePullback p (proEtaleConstantRing Y R)
    (proEtaleConstantRing X R) (proEtaleConstantRingComparison p R)
  let G := (sfIntrinsicModuleEquivalence Y R).functor
  let H := (sfIntrinsicModuleEquivalence X R).functor
  let a := ProEtale.upperStarLowerStarAdjunction
    (ModuleCat.{u + 1} (ULift.{u + 1} R)) p
  let b := proEtaleRingModuleAdjunction p (proEtaleConstantRing Y R)
    (proEtaleConstantRing X R) (proEtaleConstantRingComparison p R)
  let s := finiteScalarOrdinaryPullbackComparison R p
  let hg := finiteScalarConstantPushforward_eq R p
  let t := (sfIntrinsicDirectImageComparison p R).symm ≪≫
    isoWhiskerLeft H (eqToIso hg).symm
  let d := (sfIntrinsicDerivedDirectImageComparison p R).symm ≪≫
    isoWhiskerLeft H.mapDerivedCategory
      (Functor.rightDerivedFunctorNatIso (eqToIso hg)).symm
  have hs : (mateEquiv a b s.hom).natTrans = t.hom := by
    unfold s finiteScalarOrdinaryPullbackComparison
    change (mateEquiv a b ((mateEquiv a b).symm
      (TwoSquare.mk _ _ _ _ t.hom))).natTrans = t.hom
    exact congrArg TwoSquare.natTrans ((mateEquiv a b).apply_symm_apply
      (TwoSquare.mk _ _ _ _ t.hom))
  have hd := normalization_transport
    (ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} R)) p)
    (proEtaleConstantRingPushforward R p) (proEtaleConstantModuleDirectImage p R) G H hg
    (sfIntrinsicDirectImageComparison p R).symm
    (sfIntrinsicDerivedDirectImageComparison p R).symm
    (sfIntrinsicDerivedDirectImageComparison_inv_unitQ_factors R p)
  have he := inverse_mate_localization a b s t d hs hd
  change (finiteScalarPullbackComparison R p).hom ≫
    Functor.whiskerRight L.leftDerivedFunctorIsoMapDerivedCategory.hom H.mapDerivedCategory =
      (Functor.mapDerivedCategorySquareIso s).hom
  change ((mateEquiv
    (ProEtale.derivedUpperStarLowerStarAdjunction
      (ModuleCat.{u + 1} (ULift.{u + 1} R)) p)
    b.mapDerivedCategoryRightDerivedAdjunction).symm d.hom).natTrans ≫
    Functor.whiskerRight L.leftDerivedFunctorIsoMapDerivedCategory.hom H.mapDerivedCategory = _
  rw [AlgebraicGeometry.ProEtale.restriction_derived_adj_eq]
  exact (inverse_mate_left_iso a.mapDerivedCategoryRightDerivedAdjunction
    b.mapDerivedCategoryRightDerivedAdjunction
    L.leftDerivedFunctorIsoMapDerivedCategory.symm d.hom).trans he

private theorem finiteIntrinsicOpenUnit
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    {E : Type u} [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] (m : ℕ)
    {X Y : SixFunctorSpace D} (f : X ⟶ Y) (c : Compactification f.hom.left) :
    let A := Padic.coefficientExtensionRing C.l E (m + 1)
    let B := ModuleCat.{u + 1} (ULift.{u + 1} A)
    let Q := compactSupportProjectionSquare f c
    let RX := realization (C := C) (E := E) (n := m + 1)
      (hn := Nat.le_add_left 1 m) X
    let RZ := realization (C := C) (E := E) (n := m + 1)
      (hn := Nat.le_add_left 1 m) Q.Z
    let J := (sfIntrinsicExtensionByZero c.i A).mapDerivedCategory
    let _P := finiteDerivedPullback C.l E m c.i
    let Jf := (openImmersionLowerShriek B c.i).mapDerivedCategory
    let Pe := (upperStar B c.i).mapDerivedCategory
    let ej := FiniteIntrinsicRealization.openComparison (C := C) (E := E) m f c
    let ep := FiniteIntrinsicRealization.inversePullback (C := C) (E := E) m Q.i
    let tau := ep ≪≫ Functor.isoWhiskerLeft RZ.inverse
      (leftDerivedUpperStarIsoMapDerivedCategory B c.i)
    let beta := (FiniteIntrinsicRealization.inverseComparison RX RZ J Jf ej).symm
    let ai := IntegralSystemRealization.finiteOpenAdj C.l E c.i m
    let af := derivedOpenImmersionLowerShriekUpperStarAdjunction B c.i
    ∀ K, af.unit.app (RX.inverse.obj K) ≫ Pe.map (beta.hom.app K) =
      RX.inverse.map (ai.unit.app K) ≫ tau.hom.app (J.obj K) := by
  dsimp only
  intro K
  let A := Padic.coefficientExtensionRing C.l E (m + 1)
  let B := ModuleCat.{u + 1} (ULift.{u + 1} A)
  let EX := sfIntrinsicModuleEquivalence X.obj.left A
  let EZ := sfIntrinsicModuleEquivalence c.Z A
  let Po := upperStar B c.i
  let Jo := openImmersionLowerShriek B c.i
  let o := Functor.mapDerivedCategoryCompIso EZ.inverse (Po ⋙ EX.functor) ≪≫
    Functor.isoWhiskerLeft EZ.inverse.mapDerivedCategory
      (Functor.mapDerivedCategoryCompIso Po EX.functor)
  have h := derived_conjugate_unit EX EZ
    (openImmersionLowerShriekUpperStarAdjunction B c.i) K
  have ht := cancel_left_comparison EX.mapDerivedCategory EZ.mapDerivedCategory.inverse
    (leftDerivedUpperStarIsoMapDerivedCategory B c.i)
    (finiteDerivedPullback C.l E m c.i) o
    ((sfIntrinsicExtensionByZero c.i A).mapDerivedCategory.obj K)
  rw [AlgebraicGeometry.ProEtale.AmbientClopen.ordinary_open_adjunction_exact]
  have h' := congrArg (fun t ↦ EX.mapDerivedCategory.inverse.map
    ((IntegralSystemRealization.finiteOpenAdj C.l E c.i m).unit.app K) ≫ t) ht
  dsimp only [IntegralSystemRealization.finiteOpenAdj,
    SheafOfModules.OpenTensorNormalization.exactDerivedAdjunction,
    sfIntrinsicOpenAdjunction] at h'
  have hh := h.trans h'.symm
  have hej : FiniteIntrinsicRealization.openComparison (C := C) (E := E) m f c =
      Functor.mapDerivedCategorySquareIso (EX.funInvIdAssoc (Jo ⋙ EZ.functor)) := by
    apply Iso.ext
    apply NatTrans.ext
    funext V
    rfl
  have hep : FiniteIntrinsicRealization.inversePullback (C := C) (E := E) m
        (compactSupportProjectionSquare f c).i =
      Functor.isoWhiskerRight
        (o ≪≫ Functor.isoWhiskerLeft EZ.mapDerivedCategory.inverse
          (Functor.isoWhiskerRight (leftDerivedUpperStarIsoMapDerivedCategory B c.i).symm
            EX.mapDerivedCategory.functor)) EX.mapDerivedCategory.inverse ≪≫
        Functor.isoWhiskerLeft (EZ.mapDerivedCategory.inverse ⋙ Po.leftDerivedFunctor)
          EX.mapDerivedCategory.unitIso.symm := by
    dsimp only [FiniteIntrinsicRealization.inversePullback,
      FiniteIntrinsicRealization.pullback, realization, sixFunctorFiniteRealization,
      sfIntrinsicDerivedEquivalence, compactSupportProjectionSquare,
      Over.mk, Over.left, Over.Hom.left, CostructuredArrow.mk,
      Over.homMk, CostructuredArrow.homMk, ObjectProperty.homMk,
      A, B, EX, EZ, Po, o]
    simp only [Iso.trans_assoc]
    rfl
  rw [hej, hep]
  dsimp only [IntegralSystemRealization.finiteOpenAdj,
    SheafOfModules.OpenTensorNormalization.exactDerivedAdjunction, sfIntrinsicOpenAdjunction,
    realization, sixFunctorFiniteRealization, sfIntrinsicDerivedEquivalence,
    compactSupportProjectionSquare, Over.mk, Over.left, Over.Hom.left,
    CostructuredArrow.mk, Over.homMk, CostructuredArrow.homMk, ObjectProperty.homMk,
    sfIntrinsicExtensionByZero, sfIntrinsicTransport,
    A, B, EX, EZ, Po, Jo] at hh ⊢
  simpa only [Iso.trans_assoc, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Iso.symm_hom,
    Functor.comp_obj, Category.assoc] using hh

private theorem canonicalTensor_inv
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    {E : Type u} [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] (m : ℕ) (X : SixFunctorSpace D)
    (U V : normalizedDVRDerived C.l E X.obj.left m) :
    let A := Padic.coefficientExtensionRing C.l E (m + 1)
    let e := realization (C := C) (E := E) (n := m + 1)
      (hn := Nat.le_add_left 1 m) X
    let a := pullbackTensorFiniteModel C.l E X.obj.left m
    (canonicalFiniteIntrinsicTensorComparison (C := C) (E := E) m X).inv.app (U,V) =
      ((finiteScalarTensorRealization X.obj.left A a).hom.app
        (e.inverse.obj U)).app (e.inverse.obj V) ≫
      a.tensor.map (Prod.mkHom (e.counitIso.hom.app U) (e.counitIso.hom.app V)) ≫
      (pullbackTensorFiniteModelIso C.l E X.obj.left m).hom.app (U,V) := by
  dsimp only
  simp [canonicalFiniteIntrinsicTensorComparison, evaluatedTensor,
    CompactSupportFiniteProjection.tensor, CompactSupportFiniteProjection.realization,
    CompactSupportFiniteProjection.fixedTensor, sixFunctorFiniteRealization,
    integralCoefficientCommRingSheaf, Category.assoc]

private def finiteTensorForward
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    {E : Type u} [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] (m : ℕ) (X : SixFunctorSpace D) :
    let A := Padic.coefficientExtensionRing C.l E (m + 1)
    let B := ModuleCat.{u + 1} (ULift.{u + 1} A)
    let e := realization (C := C) (E := E) (n := m + 1)
      (hn := Nat.le_add_left 1 m) X
    Functor.uncurry.obj (derivedTensor B X.obj.left) ⋙ e.functor ≅
      (e.functor.prod e.functor) ⋙ finiteIntrinsicDerivedTensor C.l E X.obj.left m := by
  dsimp only
  let A := Padic.coefficientExtensionRing C.l E (m + 1)
  let B := ModuleCat.{u + 1} (ULift.{u + 1} A)
  let e := realization (C := C) (E := E) (n := m + 1)
    (hn := Nat.le_add_left 1 m) X
  let a := pullbackTensorFiniteModel C.l E X.obj.left m
  exact tensor_realization_uncurry e.functor (derivedTensor B X.obj.left) a.tensor
    (finiteScalarTensorRealization X.obj.left A a) ≪≫
    Functor.isoWhiskerLeft (e.functor.prod e.functor)
      (pullbackTensorFiniteModelIso C.l E X.obj.left m)

private theorem canonicalTensor_inv_forward
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    {E : Type u} [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] (m : ℕ) (X : SixFunctorSpace D)
    (U V : normalizedDVRDerived C.l E X.obj.left m) :
    let e := realization (C := C) (E := E) (n := m + 1)
      (hn := Nat.le_add_left 1 m) X
    (canonicalFiniteIntrinsicTensorComparison (C := C) (E := E) m X).inv.app (U,V) =
      (finiteTensorForward (C := C) (E := E) m X).hom.app
        (e.inverse.obj U,e.inverse.obj V) ≫
      (finiteIntrinsicDerivedTensor C.l E X.obj.left m).map
        (Prod.mkHom (e.counitIso.hom.app U) (e.counitIso.hom.app V)) := by
  dsimp only
  rw [canonicalTensor_inv]
  simp only [finiteTensorForward, id_eq, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
    tensor_realization_uncurry_hom, Category.assoc]
  erw [← (pullbackTensorFiniteModelIso C.l E X.obj.left m).hom.naturality]
  rfl

private def canonicalTensorCoordinates
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    {E : Type u} [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] (m : ℕ) (X : SixFunctorSpace D) :
    let A := Padic.coefficientExtensionRing C.l E (m + 1)
    let B := ModuleCat.{u + 1} (ULift.{u + 1} A)
    let e := realization (C := C) (E := E) (n := m + 1)
      (hn := Nat.le_add_left 1 m) X
    finiteIntrinsicDerivedTensor C.l E X.obj.left m ≅
      (e.inverse.prod e.inverse) ⋙ Functor.uncurry.obj (derivedTensor B X.obj.left) ⋙
        e.functor :=
  canonicalFiniteIntrinsicTensorComparison (C := C) (E := E) m X ≪≫
    tensor_coordinate_iso (realization (C := C) (E := E) (n := m + 1)
      (hn := Nat.le_add_left 1 m) X) _

private theorem canonicalTensorCoordinates_hom
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    {E : Type u} [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] (m : ℕ) (X : SixFunctorSpace D)
    (U V : normalizedDVRDerived C.l E X.obj.left m) :
    (canonicalTensorCoordinates (C := C) (E := E) m X).hom.app (U,V) =
      (canonicalFiniteIntrinsicTensorComparison (C := C) (E := E) m X).hom.app (U,V) := by
  simp only [canonicalTensorCoordinates, Iso.trans_hom, NatTrans.comp_app,
    tensor_coordinate_iso_hom_app]
  erw [Category.comp_id]

private theorem canonicalTensorCoordinates_inv
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    {E : Type u} [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] (m : ℕ) (X : SixFunctorSpace D)
    (U V : normalizedDVRDerived C.l E X.obj.left m) :
    let e := realization (C := C) (E := E) (n := m + 1)
      (hn := Nat.le_add_left 1 m) X
    (canonicalTensorCoordinates (C := C) (E := E) m X).inv.app (U,V) =
      (finiteTensorForward (C := C) (E := E) m X).hom.app
        (e.inverse.obj U,e.inverse.obj V) ≫
      (finiteIntrinsicDerivedTensor C.l E X.obj.left m).map
        (Prod.mkHom (e.counitIso.hom.app U) (e.counitIso.hom.app V)) := by
  simp only [canonicalTensorCoordinates, Iso.trans_inv, NatTrans.comp_app,
    tensor_coordinate_iso_inv_app]
  erw [Category.id_comp]
  exact canonicalTensor_inv_forward (C := C) (E := E) m X U V

private theorem finitePullbackTensorCoordinates
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    {E : Type u} [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] (m : ℕ)
    {X Y : SixFunctorSpace D} (f : X ⟶ Y) (c : Compactification f.hom.left) :
    let A := Padic.coefficientExtensionRing C.l E (m + 1)
    let Pr := proEtaleConstantRingDerivedPullback A c.i
    let Tx := finiteIntrinsicDerivedTensor C.l E X.obj.left m
    let Tz := finiteIntrinsicDerivedTensor C.l E c.Z m
    let r := Functor.mapDerivedCategoryNatIso (openSquarePullbackModel A c.i)
    letI := SystemProjectionFormula.residueInvertible C.l D C.different X.obj.left X.obj.hom
    letI := SystemProjectionFormula.residueInvertible C.l D C.different c.Z (c.g ≫ Y.obj.hom)
    finitePullbackTensorConstructionIso C.l E c.i m =
      Functor.isoWhiskerLeft Tz r.symm ≪≫
        Functor.isoWhiskerRight (pullbackTensorFiniteModelIso C.l E c.Z m).symm Pr ≪≫
        proEtaleCanonicalTensorComparison c.i (proEtaleConstantRing c.Z A)
          (proEtaleConstantRing X.obj.left A) (proEtaleConstantRingComparison c.i A)
          (pullbackTensorFiniteModel C.l E c.Z m) (pullbackTensorFiniteModel C.l E X.obj.left m) ≪≫
        Functor.isoWhiskerLeft (Pr.prod Pr) (pullbackTensorFiniteModelIso C.l E X.obj.left m) ≪≫
        Functor.isoWhiskerRight (NatIso.prod r r) Tx := by
  rfl


-- Keep the constructed comparison data folded in categorical transport arguments.

private theorem finiteIntrinsicTensorForwardCompatible
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    {E : Type u} [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] (m : ℕ)
    {X Y : SixFunctorSpace D} (f : X ⟶ Y) (c : Compactification f.hom.left) :
    let A := Padic.coefficientExtensionRing C.l E (m + 1)
    let B := ModuleCat.{u + 1} (ULift.{u + 1} A)
    let Q := compactSupportProjectionSquare f c
    let RX := realization (C := C) (E := E) (n := m + 1)
      (hn := Nat.le_add_left 1 m) X
    let RZ := realization (C := C) (E := E) (n := m + 1)
      (hn := Nat.le_add_left 1 m) Q.Z
    let P := finiteDerivedPullback C.l E m c.i
    let Pf := (upperStar B c.i).leftDerivedFunctor
    let _tx := Functor.uncurry.obj (derivedTensor B X.obj.left)
    let tz := Functor.uncurry.obj (derivedTensor B c.Z)
    let Tx := finiteIntrinsicDerivedTensor C.l E X.obj.left m
    let _Tz := finiteIntrinsicDerivedTensor C.l E c.Z m
    let r := Functor.mapDerivedCategoryNatIso (openSquarePullbackModel A c.i)
    let α := Functor.isoWhiskerLeft RZ.functor r.symm ≪≫ finiteScalarPullbackComparison A c.i
    letI := SystemProjectionFormula.residueInvertible C.l D C.different X.obj.left X.obj.hom
    letI := SystemProjectionFormula.residueInvertible C.l D C.different c.Z (c.g ≫ Y.obj.hom)
    ∀ V W, RX.functor.map
        ((uncurry_tensor_natTrans Pf (derivedTensor B c.Z) (derivedTensor B X.obj.left)
          (leftDerivedUpperStarTensorComparison B c.i)).app (V,W)) ≫
        (finiteTensorForward (C := C) (E := E) m X).hom.app (Pf.obj V,Pf.obj W) =
      α.inv.app (tz.obj (V,W)) ≫
        P.map ((finiteTensorForward (C := C) (E := E) m Q.Z).hom.app (V,W)) ≫
        (finitePullbackTensorConstructionIso C.l E c.i m).hom.app
          (RZ.functor.obj V,RZ.functor.obj W) ≫
        Tx.map (Prod.mkHom (α.hom.app V) (α.hom.app W)) := by
  dsimp only
  letI A := Padic.coefficientExtensionRing C.l E (m + 1)
  letI B := ModuleCat.{u + 1} (ULift.{u + 1} A)
  letI Q := compactSupportProjectionSquare f c
  letI RX := realization (C := C) (E := E) (n := m + 1)
    (hn := Nat.le_add_left 1 m) X
  letI RZ := realization (C := C) (E := E) (n := m + 1)
    (hn := Nat.le_add_left 1 m) Q.Z
  letI ax := pullbackTensorFiniteModel C.l E X.obj.left m
  letI az := pullbackTensorFiniteModel C.l E c.Z m
  letI fx := derivedTensor B X.obj.left
  letI fz := derivedTensor B c.Z
  letI P := finiteDerivedPullback C.l E m c.i
  letI Pf := (upperStar B c.i).leftDerivedFunctor
  letI Pr := proEtaleConstantRingDerivedPullback A c.i
  letI Tx := finiteIntrinsicDerivedTensor C.l E X.obj.left m
  letI Tz := finiteIntrinsicDerivedTensor C.l E c.Z m
  letI r := Functor.mapDerivedCategoryNatIso (openSquarePullbackModel A c.i)
  letI α := Functor.isoWhiskerLeft RZ.functor r.symm ≪≫ finiteScalarPullbackComparison A c.i
  letI tx := Functor.uncurry.obj fx
  letI tz := Functor.uncurry.obj fz
  letI rx := tensor_realization_uncurry RX.functor fx ax.tensor
    (finiteScalarTensorRealization X.obj.left A ax)
  letI rz := tensor_realization_uncurry RZ.functor fz az.tensor
    (finiteScalarTensorRealization c.Z A az)
  letI μ := uncurry_tensor_natTrans Pf fz fx (leftDerivedUpperStarTensorComparison B c.i)
  letI ν := (proEtaleCanonicalTensorComparison c.i (proEtaleConstantRing c.Z A)
    (proEtaleConstantRing X.obj.left A) (proEtaleConstantRingComparison c.i A) az ax).hom
  have hs : ∀ V W, RX.functor.map (μ.app (V,W)) ≫ rx.hom.app (Pf.obj V,Pf.obj W) =
      (finiteScalarPullbackComparison A c.i).inv.app (tz.obj (V,W)) ≫
        Pr.map (rz.hom.app (V,W)) ≫ ν.app (RZ.functor.obj V,RZ.functor.obj W) ≫
        ax.tensor.map (Prod.mkHom ((finiteScalarPullbackComparison A c.i).hom.app V)
          ((finiteScalarPullbackComparison A c.i).hom.app W)) := by
    intro V W
    exact scalar_uncurry_compatible RZ.functor RX.functor Pr Pf fz fx az.tensor ax.tensor
      (finiteScalarPullbackComparison A c.i)
      (finiteScalarTensorRealization c.Z A az)
      (finiteScalarTensorRealization X.obj.left A ax)
      (leftDerivedUpperStarTensorComparison B c.i) ν
      (finiteScalarTensorPullbackComparisonCanonical A c.i ax az) V W
  letI := SystemProjectionFormula.residueInvertible C.l D C.different X.obj.left X.obj.hom
  letI := SystemProjectionFormula.residueInvertible C.l D C.different c.Z (c.g ≫ Y.obj.hom)
  intro V W
  exact tensor_compatibility_transport_of_eq RZ.functor RX.functor Pr P Pf tz tx
    az.tensor Tz ax.tensor Tx (finiteScalarPullbackComparison A c.i) r
    (pullbackTensorFiniteModelIso C.l E c.Z m)
    (pullbackTensorFiniteModelIso C.l E X.obj.left m) rz rx μ
    (proEtaleCanonicalTensorComparison c.i (proEtaleConstantRing c.Z A)
      (proEtaleConstantRing X.obj.left A) (proEtaleConstantRingComparison c.i A) az ax)
    α (finiteTensorForward (C := C) (E := E) m Q.Z)
    (finiteTensorForward (C := C) (E := E) m X)
    (finitePullbackTensorConstructionIso C.l E c.i m)
    rfl
    (by unfold finiteTensorForward; rfl)
    (by unfold finiteTensorForward; rfl)
    (finitePullbackTensorCoordinates (C := C) (E := E) m f c)
    hs V W
-- Inlining these concrete data avoids expensive kernel conversions.

private theorem finiteIntrinsicTensorCompatible
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    {E : Type u} [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] (m : ℕ)
    {X Y : SixFunctorSpace D} (f : X ⟶ Y) (c : Compactification f.hom.left) :
    let A := Padic.coefficientExtensionRing C.l E (m + 1)
    let B := ModuleCat.{u + 1} (ULift.{u + 1} A)
    let Q := compactSupportProjectionSquare f c
    let RX := realization (C := C) (E := E) (n := m + 1)
      (hn := Nat.le_add_left 1 m) X
    let RZ := realization (C := C) (E := E) (n := m + 1)
      (hn := Nat.le_add_left 1 m) Q.Z
    let P := finiteDerivedPullback C.l E m c.i
    let Tx := finiteIntrinsicDerivedTensor C.l E X.obj.left m
    let Tz := finiteIntrinsicDerivedTensor C.l E c.Z m
    let fx := derivedTensor B X.obj.left
    let fz := derivedTensor B c.Z
    let sx := canonicalTensorCoordinates (C := C) (E := E) m X
    let sz := canonicalTensorCoordinates (C := C) (E := E) m Q.Z
    let qx := inverse_curried_tensor_coordinates RX fx Tx sx
    let qz := inverse_curried_tensor_coordinates RZ fz Tz sz
    let ep := FiniteIntrinsicRealization.inversePullback (C := C) (E := E) m Q.i
    letI := SystemProjectionFormula.residueInvertible C.l D C.different X.obj.left X.obj.hom
    letI := SystemProjectionFormula.residueInvertible C.l D C.different c.Z (c.g ≫ Y.obj.hom)
    Adjunction.ComparisonCompatible ep.symm
      (Functor.curry.map (finitePullbackTensorConstructionIso C.l E c.i m).hom ≫
        (Functor.curryObjProdComp P P Tx).hom)
      (leftDerivedUpperStarTensorComparison B c.i) qx qz := by
  dsimp only
  letI A := Padic.coefficientExtensionRing C.l E (m + 1)
  letI B := ModuleCat.{u + 1} (ULift.{u + 1} A)
  letI Q := compactSupportProjectionSquare f c
  letI RX := realization (C := C) (E := E) (n := m + 1)
    (hn := Nat.le_add_left 1 m) X
  letI RZ := realization (C := C) (E := E) (n := m + 1)
    (hn := Nat.le_add_left 1 m) Q.Z
  letI P := finiteDerivedPullback C.l E m c.i
  letI Pf := (upperStar B c.i).leftDerivedFunctor
  letI tx := Functor.uncurry.obj (derivedTensor B X.obj.left)
  letI tz := Functor.uncurry.obj (derivedTensor B c.Z)
  letI Tx := finiteIntrinsicDerivedTensor C.l E X.obj.left m
  letI Tz := finiteIntrinsicDerivedTensor C.l E c.Z m
  letI r := Functor.mapDerivedCategoryNatIso (openSquarePullbackModel A c.i)
  letI α := Functor.isoWhiskerLeft RZ.functor r.symm ≪≫ finiteScalarPullbackComparison A c.i
  letI μ := uncurry_tensor_natTrans Pf (derivedTensor B c.Z) (derivedTensor B X.obj.left)
    (leftDerivedUpperStarTensorComparison B c.i)
  letI := SystemProjectionFormula.residueInvertible C.l D C.different X.obj.left X.obj.hom
  letI := SystemProjectionFormula.residueInvertible C.l D C.different c.Z (c.g ≫ Y.obj.hom)
  have he : FiniteIntrinsicRealization.inverseComparison RZ RX P Pf α =
      FiniteIntrinsicRealization.inversePullback (C := C) (E := E) m Q.i :=
    by
      simpa only [α, r, RX, RZ, Q, A, B, P, Pf,
        FiniteIntrinsicRealization.inversePullback, FiniteIntrinsicRealization.pullback,
        realization, sixFunctorFiniteRealization, sfIntrinsicDerivedEquivalence,
        compactSupportProjectionSquare, Over.mk, Over.left, Over.Hom.left,
        CostructuredArrow.mk, Over.homMk, CostructuredArrow.homMk,
        ObjectProperty.homMk, Iso.trans_assoc, finiteDerivedPullback, sfIntrinsicDerivedPullback,
        leftDerivedUpperStarIsoMapDerivedCategory] using scalar_intrinsic_inverse A c.i
  exact tensor_coordinates_compatible_of_forward RZ RX P Pf
    (derivedTensor B X.obj.left) (derivedTensor B c.Z) Tx Tz α
    (finiteTensorForward (C := C) (E := E) m Q.Z)
    (finiteTensorForward (C := C) (E := E) m X)
    (canonicalTensorCoordinates (C := C) (E := E) m X)
    (canonicalTensorCoordinates (C := C) (E := E) m Q.Z)
    (canonicalTensorCoordinates_inv (C := C) (E := E) m X)
    (canonicalTensorCoordinates_inv (C := C) (E := E) m Q.Z)
    (FiniteIntrinsicRealization.inversePullback (C := C) (E := E) m Q.i) he
    (leftDerivedUpperStarTensorComparison B c.i)
    (finitePullbackTensorConstructionIso C.l E c.i m).hom
    (finiteIntrinsicTensorForwardCompatible (C := C) (E := E) m f c)

private theorem scalar_intrinsic_inverse
    (R : Type u) [CommRing R] [Finite R] {X Y : Scheme.{u}} (p : X ⟶ Y) :
    let EX := sfIntrinsicModuleEquivalence X R
    let EY := sfIntrinsicModuleEquivalence Y R
    let P := ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} R)) p
    let r := Functor.mapDerivedCategoryNatIso (openSquarePullbackModel R p)
    let a := Functor.isoWhiskerLeft EY.mapDerivedCategory.functor r.symm ≪≫
      finiteScalarPullbackComparison R p
    let o := Functor.mapDerivedCategoryCompIso EY.inverse (P ⋙ EX.functor) ≪≫
      Functor.isoWhiskerLeft EY.inverse.mapDerivedCategory
        (Functor.mapDerivedCategoryCompIso P EX.functor) ≪≫
      Functor.isoWhiskerLeft EY.inverse.mapDerivedCategory
        (Functor.isoWhiskerRight P.leftDerivedFunctorIsoMapDerivedCategory.symm
          EX.functor.mapDerivedCategory)
    inverseComparison EY.mapDerivedCategory EX.mapDerivedCategory
        (sfIntrinsicPullback R p).mapDerivedCategory P.leftDerivedFunctor a =
      Functor.isoWhiskerRight o EX.mapDerivedCategory.inverse ≪≫
        Functor.isoWhiskerLeft (EY.mapDerivedCategory.inverse ⋙ P.leftDerivedFunctor)
          EX.mapDerivedCategory.unitIso.symm := by
  dsimp only
  rw [scalar_intrinsic_comparison]
  exact inverseComparison_localized_conjugate (sfIntrinsicModuleEquivalence Y R)
    (sfIntrinsicModuleEquivalence X R)
    (ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} R)) p) _
    (ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} R)) p
      ).leftDerivedFunctorIsoMapDerivedCategory

private theorem scalar_intrinsic_comparison
    (R : Type u) [CommRing R] [Finite R] {X Y : Scheme.{u}} (p : X ⟶ Y) :
    let EX := sfIntrinsicModuleEquivalence X R
    let EY := sfIntrinsicModuleEquivalence Y R
    let P := ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} R)) p
    let r := Functor.mapDerivedCategoryNatIso (openSquarePullbackModel R p)
    Functor.isoWhiskerLeft EY.mapDerivedCategory.functor r.symm ≪≫
        finiteScalarPullbackComparison R p =
      Functor.mapDerivedCategorySquareIso (EY.funInvIdAssoc (P ⋙ EX.functor)) ≪≫
        Functor.isoWhiskerRight P.leftDerivedFunctorIsoMapDerivedCategory.symm
          EX.mapDerivedCategory.functor := by
  dsimp only
  let EX := sfIntrinsicModuleEquivalence X R
  let EY := sfIntrinsicModuleEquivalence Y R
  let P := ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} R)) p
  let F := proEtaleConstantRingPullback R p
  let s := finiteScalarOrdinaryPullbackComparison R p
  let r := openSquarePullbackModel R p
  have hr : Functor.isoWhiskerLeft EY.functor r.symm ≪≫ s =
      EY.funInvIdAssoc (P ⋙ EX.functor) := by
    dsimp only [r]
    rw [finiteIntrinsicOrdinaryPullbackNormalization]
    exact conjugated_comparison EY EX F P s
  apply Iso.ext
  apply NatTrans.ext
  funext K
  apply (cancel_mono (EX.mapDerivedCategory.functor.map
    (P.leftDerivedFunctorIsoMapDerivedCategory.hom.app K))).1
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Category.assoc]
  have hs := NatTrans.congr_app (scalarPullback_exact R p) K
  dsimp only [NatTrans.comp_app, Functor.whiskerRight_app] at hs
  dsimp only [EX, P, sfIntrinsicDerivedEquivalence] at hs ⊢
  erw [hs]
  have hw := square_whiskerLeft_iso EY.functor _ F P EX.functor r.symm s K
  rw [hr] at hw
  simp only [mapDerivedCategoryNatIso_symm] at hw
  dsimp only [r, s, EY, EX, P] at hw
  erw [← hw]
  dsimp only [Equivalence.mapDerivedCategory, CategoryTheory.Equivalence.mk, Functor.comp_obj]
  erw [← (sfIntrinsicModuleEquivalence X R).functor.mapDerivedCategory.map_comp,
    Iso.inv_hom_id_app, (sfIntrinsicModuleEquivalence X R).functor.mapDerivedCategory.map_id,
    Category.comp_id]
  rfl

private theorem inverseComparison_localized_conjugate
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    [Abelian A] [Abelian B] [Abelian C] [Abelian D]
    [HasDerivedCategory A] [HasDerivedCategory B]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (e : A ≌ C) (g : B ≌ D)
    [e.functor.Additive] [e.inverse.Additive] [g.functor.Additive] [g.inverse.Additive]
    (P : A ⥤ B) [P.Additive] [PreservesFiniteLimits P] [PreservesFiniteColimits P]
    (P' : DerivedCategory A ⥤ DerivedCategory B) (s : P' ≅ P.mapDerivedCategory) :
    let Pi := (e.inverse ⋙ P ⋙ g.functor).mapDerivedCategory
    let a := mapDerivedCategorySquareIso (e.funInvIdAssoc (P ⋙ g.functor)) ≪≫
      isoWhiskerRight s.symm g.mapDerivedCategory.functor
    let o := mapDerivedCategoryCompIso e.inverse (P ⋙ g.functor) ≪≫
      isoWhiskerLeft e.inverse.mapDerivedCategory
        (mapDerivedCategoryCompIso P g.functor) ≪≫
      isoWhiskerLeft e.inverse.mapDerivedCategory
        (isoWhiskerRight s.symm g.functor.mapDerivedCategory)
    inverseComparison e.mapDerivedCategory g.mapDerivedCategory Pi P' a =
      isoWhiskerRight o g.mapDerivedCategory.inverse ≪≫
        isoWhiskerLeft (e.mapDerivedCategory.inverse ⋙ P')
          g.mapDerivedCategory.unitIso.symm := by
  dsimp only
  apply Iso.ext
  apply NatTrans.ext
  funext N
  apply inverseComparison_of_raw
  intro K
  simp only [Iso.trans_hom, Iso.trans_inv, Iso.symm_inv, NatTrans.comp_app,
    isoWhiskerLeft_hom, isoWhiskerRight_inv, isoWhiskerRight_hom,
    whiskerLeft_app, whiskerRight_app, Category.assoc]
  dsimp only [Equivalence.mapDerivedCategory, CategoryTheory.Equivalence.mk, Functor.comp_obj]
  erw [← g.functor.mapDerivedCategory.map_comp_assoc, Iso.inv_hom_id_app,
    g.functor.mapDerivedCategory.map_id, Category.id_comp]
  have h := derived_square_coherence e P g.functor K
  simpa only [mapDerivedCategorySquareIso, mapDerivedCategoryNatIso_symm,
    Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv, NatTrans.comp_app,
    isoWhiskerLeft_hom, whiskerLeft_app, Category.assoc,
    Equivalence.mapDerivedCategory, CategoryTheory.Equivalence.mk, Functor.comp_obj,
    Equivalence.counitInv] using h

private theorem inverseComparison_of_raw
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    (e : A ≌ C) (g : B ≌ D) (P : C ⥤ D) (P₀ : A ⥤ B)
    (o : P ≅ e.inverse ⋙ P₀ ⋙ g.functor)
    (r : e.functor ⋙ P ≅ P₀ ⋙ g.functor)
    (ho : ∀ N, o.hom.app N ≫ r.inv.app (e.inverse.obj N) =
      P.map (e.counitIso.inv.app N)) (N : C) :
    (inverseComparison e g P P₀ r).hom.app N =
      (isoWhiskerRight o g.inverse ≪≫
        isoWhiskerLeft (e.inverse ⋙ P₀) g.unitIso.symm).hom.app N := by
  have hh : P.map (e.counitIso.inv.app N) ≫ r.hom.app (e.inverse.obj N) =
      o.hom.app N := by
    rw [← ho]
    simp only [Category.assoc, Iso.inv_hom_id_app]
    erw [Category.comp_id]
  simp only [inverseComparison, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    isoWhiskerRight_hom, isoWhiskerLeft_hom, whiskerRight_app, whiskerLeft_app,
    Functor.comp_map, ← g.inverse.map_comp_assoc, hh]

private theorem square_whiskerLeft_iso
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    [Abelian A] [Abelian B] [Abelian C] [Abelian D]
    [HasDerivedCategory A] [HasDerivedCategory B]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (H : A ⥤ C) (F F' : C ⥤ D) (P : A ⥤ B) (G : B ⥤ D)
    [H.Additive] [F.Additive] [F'.Additive] [P.Additive] [G.Additive]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits F'] [PreservesFiniteColimits F']
    [PreservesFiniteLimits P] [PreservesFiniteColimits P]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (r : F ≅ F') (s : H ⋙ F' ≅ P ⋙ G) (K : DerivedCategory A) :
    (mapDerivedCategorySquareIso (isoWhiskerLeft H r ≪≫ s)).hom.app K =
      (mapDerivedCategoryNatIso r).hom.app (H.mapDerivedCategory.obj K) ≫
        (mapDerivedCategorySquareIso s).hom.app K := by
  have h := NatTrans.congr_app (mapDerivedCategoryNatIso_isoWhiskerLeft H r) K
  dsimp only [NatTrans.comp_app, whiskerLeft_app] at h
  simp only [mapDerivedCategorySquareIso, mapDerivedCategoryNatIso_trans,
    Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app]
  apply (cancel_epi ((mapDerivedCategoryCompIso H F).hom.app K)).1
  simp only [Iso.hom_inv_id_app_assoc]
  rw [← reassoc_of% h]
  simp only [Iso.hom_inv_id_app_assoc, Category.assoc]

private theorem conjugated_comparison
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    (e : A ≌ C) (g : B ≌ D) (F : C ⥤ D) (P : A ⥤ B)
    (s : e.functor ⋙ F ≅ P ⋙ g.functor) :
    let r : F ≅ e.inverse ⋙ P ⋙ g.functor :=
      (leftUnitor F).symm ≪≫ isoWhiskerRight e.counitIso.symm F ≪≫
        associator _ _ _ ≪≫ isoWhiskerLeft e.inverse s
    isoWhiskerLeft e.functor r.symm ≪≫ s = e.funInvIdAssoc (P ⋙ g.functor) := by
  let r : F ≅ e.inverse ⋙ P ⋙ g.functor :=
    (leftUnitor F).symm ≪≫ isoWhiskerRight e.counitIso.symm F ≪≫
      associator _ _ _ ≪≫ isoWhiskerLeft e.inverse s
  change isoWhiskerLeft e.functor r.symm ≪≫ s = e.funInvIdAssoc (P ⋙ g.functor)
  apply Iso.ext
  apply NatTrans.ext
  funext X
  apply (cancel_epi (r.hom.app (e.functor.obj X))).1
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    isoWhiskerLeft_hom, whiskerLeft_app, Iso.hom_inv_id_app_assoc]
  simp only [r, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    isoWhiskerLeft_hom, isoWhiskerRight_hom, whiskerLeft_app, whiskerRight_app,
    leftUnitor_inv_app, associator_hom_app, Category.id_comp,
    Equivalence.funInvIdAssoc_hom_app, Functor.comp_map, Category.assoc]
  have hn := s.hom.naturality (e.unitIso.inv.app X)
  dsimp only [Functor.comp_map, Functor.comp_obj, Functor.id_obj] at hn
  erw [← hn]
  simp only [← F.map_comp_assoc, Equivalence.counitIso_functor_comp]
  erw [F.map_id, Category.id_comp]

private theorem mixed_curry_tensor_square
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    (e : A ≌ C) (g : B ≌ D) (P : C ⥤ D) (Pe Pf : A ⥤ B)
    (T : A ⥤ A ⥤ A) (U : B ⥤ B ⥤ B)
    (Ti : C × C ⥤ C) (Ui : D × D ⥤ D)
    (ep : P ⋙ g.inverse ≅ e.inverse ⋙ Pf) (s : Pf ≅ Pe)
    (t : Ti ⋙ P ≅ (P.prod P) ⋙ Ui)
    (tf : (postcompose₂.obj Pf).obj T ≅
      (((whiskeringLeft₂ B).obj Pf).obj Pf).obj U)
    (qt : (postcompose₂.obj e.inverse).obj (curry.obj Ti) ≅
      (((whiskeringLeft₂ A).obj e.inverse).obj e.inverse).obj T)
    (qu : (postcompose₂.obj g.inverse).obj (curry.obj Ui) ≅
      (((whiskeringLeft₂ B).obj g.inverse).obj g.inverse).obj U)
    (h : Adjunction.ComparisonCompatible ep.symm
      (curry.map t.hom ≫ (curryObjProdComp P P Ui).hom) tf.hom qu qt) (V W : C) :
    let tau := ep ≪≫ isoWhiskerLeft e.inverse s
    g.inverse.map (t.inv.app (V, W)) ≫ tau.hom.app (Ti.obj (V, W)) ≫
        Pe.map ((qt.hom.app V).app W) =
      (qu.hom.app (P.obj V)).app (P.obj W) ≫
        (U.map (tau.hom.app V)).app (g.inverse.obj (P.obj W)) ≫
        (U.obj (Pe.obj (e.inverse.obj V))).map (ep.hom.app W) ≫
        ((mixedTensor T U s tf).hom.app (e.inverse.obj V)).app (e.inverse.obj W) := by
  dsimp only
  have hh := mixed_tensor_square (T := curry.obj Ti) (U := curry.obj Ui)
    ep.symm (Iso.refl P) s (curry_tensor_iso P Ti Ui t) tf qu qt
    (by
      intro V W
      have hh := h V W
      simp only [NatTrans.comp_app, curry_map_app_app,
        curryObjProdComp_hom_app_app] at hh
      erw [Category.comp_id] at hh
      simpa only [curry_tensor_iso_hom] using hh) V W
  dsimp only [Functor.comp_obj, Functor.id_obj, curry_obj_obj_obj] at hh ⊢
  simp only [mixedTensor, Iso.trans_hom, Iso.symm_hom, Iso.symm_inv,
    Iso.symm_symm_eq, Iso.refl_hom, Iso.refl_inv, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, NatTrans.id_app,
    Functor.whiskeringLeft₂_map_app_app_app_app, Functor.postcompose₂_map_app_app_app,
    Functor.mapIso_hom, Iso.app_hom, curry_tensor_iso_inv,
    CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id, Category.assoc] at hh ⊢
  erw [Category.id_comp, Category.id_comp] at hh
  exact hh

private theorem projectionMap_curry_tensor
    {C D : Type*} [Category C] [Category D]
    {J : C ⥤ D} {P : D ⥤ C} (a : J ⊣ P)
    (T : C × C ⥤ C) (U : D × D ⥤ D)
    (s : U ⋙ P ≅ (P.prod P) ⋙ T) (K : C) (L : D) :
    ((a.projectionMap P (curry.obj T) (curry.obj U)
      (curry_tensor_iso P U T s).inv).app K).app L =
      (a.homEquiv _ _).symm
        (T.map (Prod.mkHom (a.unit.app K) (𝟙 (P.obj L))) ≫ s.inv.app (J.obj K, L)) := by
  rw [Adjunction.projectionMap_app_app, Adjunction.projectionMapTranspose_app_app]
  simp only [Functor.curry_obj_map_app, curry_tensor_iso_inv]
  rfl

private theorem curry_tensor_iso_inv
    {A B : Type*} [Category A] [Category B] (P : A ⥤ B)
    (T : A × A ⥤ A) (U : B × B ⥤ B)
    (s : T ⋙ P ≅ (P.prod P) ⋙ U) (V W : A) :
    ((curry_tensor_iso P T U s).inv.app V).app W = s.inv.app (V, W) := rfl

private theorem curry_tensor_iso_hom
    {A B : Type*} [Category A] [Category B] (P : A ⥤ B)
    (T : A × A ⥤ A) (U : B × B ⥤ B)
    (s : T ⋙ P ≅ (P.prod P) ⋙ U) (V W : A) :
    ((curry_tensor_iso P T U s).hom.app V).app W = s.hom.app (V, W) := rfl

private def curry_tensor_iso
    {A B : Type*} [Category A] [Category B] (P : A ⥤ B)
    (T : A × A ⥤ A) (U : B × B ⥤ B)
    (s : T ⋙ P ≅ (P.prod P) ⋙ U) :
    (postcompose₂.obj P).obj (curry.obj T) ≅
      (((whiskeringLeft₂ B).obj P).obj P).obj (curry.obj U) :=
  NatIso.ofComponents (fun V ↦ NatIso.ofComponents (fun W ↦ s.app (V, W))
    (by
      intro W W' w
      simpa only [Functor.comp_map, Functor.prod_map, CategoryTheory.Functor.map_id,
        postcompose₂_obj_obj_obj_map, postcompose₂_obj_obj_map_app,
        whiskeringLeft₂_obj_obj_obj_obj_map, whiskeringLeft₂_obj_obj_obj_map_app,
        curry_obj_obj_map, curry_obj_map_app, Iso.app_hom,
        NatTrans.comp_app, NatIso.ofComponents_hom_app]
        using s.hom.naturality (Prod.mkHom (𝟙 V) w)))
    (by
      intro V V' v
      ext W
      simpa only [Functor.comp_map, Functor.prod_map, CategoryTheory.Functor.map_id,
        postcompose₂_obj_obj_obj_map, postcompose₂_obj_obj_map_app,
        whiskeringLeft₂_obj_obj_obj_obj_map, whiskeringLeft₂_obj_obj_obj_map_app,
        curry_obj_obj_map, curry_obj_map_app, Iso.app_hom,
        NatTrans.comp_app, NatIso.ofComponents_hom_app]
        using s.hom.naturality (Prod.mkHom v (𝟙 W)))

private theorem tensor_coordinates_compatible_of_forward
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    (e : A ≌ C) (g : B ≌ D) (P : C ⥤ D) (Pf : A ⥤ B)
    (fx : B ⥤ B ⥤ B) (fz : A ⥤ A ⥤ A)
    (Tx : D × D ⥤ D) (Tz : C × C ⥤ C)
    (r : e.functor ⋙ P ≅ Pf ⋙ g.functor)
    (t : uncurry.obj fz ⋙ e.functor ≅ (e.functor.prod e.functor) ⋙ Tz)
    (u : uncurry.obj fx ⋙ g.functor ≅ (g.functor.prod g.functor) ⋙ Tx)
    (sx : Tx ≅ (g.inverse.prod g.inverse) ⋙ uncurry.obj fx ⋙ g.functor)
    (sz : Tz ≅ (e.inverse.prod e.inverse) ⋙ uncurry.obj fz ⋙ e.functor)
    (hsx : ∀ V W, sx.inv.app (V, W) =
      u.hom.app (g.inverse.obj V, g.inverse.obj W) ≫
        Tx.map (Prod.mkHom (g.counitIso.hom.app V) (g.counitIso.hom.app W)))
    (hsz : ∀ V W, sz.inv.app (V, W) =
      t.hom.app (e.inverse.obj V, e.inverse.obj W) ≫
        Tz.map (Prod.mkHom (e.counitIso.hom.app V) (e.counitIso.hom.app W)))
    (z : P ⋙ g.inverse ≅ e.inverse ⋙ Pf)
    (hz : inverseComparison e g P Pf r = z)
    (μ : (postcompose₂.obj Pf).obj fz ⟶
      (((whiskeringLeft₂ B).obj Pf).obj Pf).obj fx)
    (ν : Tz ⋙ P ⟶ (P.prod P) ⋙ Tx)
    (h : ∀ V W, g.functor.map ((uncurry_tensor_natTrans Pf fz fx μ).app (V, W)) ≫
        u.hom.app (Pf.obj V, Pf.obj W) =
      r.inv.app ((uncurry.obj fz).obj (V, W)) ≫ P.map (t.hom.app (V, W)) ≫
        ν.app (e.functor.obj V, e.functor.obj W) ≫
        Tx.map (Prod.mkHom (r.hom.app V) (r.hom.app W))) :
    Adjunction.ComparisonCompatible z.symm
      (curry.map ν ≫ (curryObjProdComp P P Tx).hom) μ
      (inverse_curried_tensor_coordinates g fx Tx sx)
      (inverse_curried_tensor_coordinates e fz Tz sz) := by
  subst z
  apply inverse_coordinates_compatible e g P Pf fx fz Tx Tz sx sz _ μ ν
  intro V W
  rw [tensor_inverseComparison g _ Tx u sx hsx,
    tensor_inverseComparison e _ Tz t sz hsz]
  exact inverse_tensor_compatibility e g P Pf _ _ Tz Tx r t u
    (uncurry_tensor_natTrans Pf fz fx μ) ν h V W

private theorem inverse_coordinates_compatible
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    (e : A ≌ C) (g : B ≌ D) (P : C ⥤ D) (Pf : A ⥤ B)
    (fx : B ⥤ B ⥤ B) (fz : A ⥤ A ⥤ A)
    (Tx : D × D ⥤ D) (Tz : C × C ⥤ C)
    (sx : Tx ≅ (g.inverse.prod g.inverse) ⋙ uncurry.obj fx ⋙ g.functor)
    (sz : Tz ≅ (e.inverse.prod e.inverse) ⋙ uncurry.obj fz ⋙ e.functor)
    (z : P ⋙ g.inverse ≅ e.inverse ⋙ Pf)
    (μ : (postcompose₂.obj Pf).obj fz ⟶
      (((whiskeringLeft₂ B).obj Pf).obj Pf).obj fx)
    (ν : Tz ⋙ P ⟶ (P.prod P) ⋙ Tx)
    (h : ∀ V W, g.inverse.map (ν.app (V, W)) ≫
        (inverse_tensor_coordinates g (uncurry.obj fx) Tx sx).hom.app (P.obj V, P.obj W) =
      z.hom.app (Tz.obj (V, W)) ≫
        Pf.map ((inverse_tensor_coordinates e (uncurry.obj fz) Tz sz).hom.app (V, W)) ≫
        (uncurry_tensor_natTrans Pf fz fx μ).app (e.inverse.obj V, e.inverse.obj W) ≫
        (uncurry.obj fx).map (Prod.mkHom (z.inv.app V) (z.inv.app W))) :
    Adjunction.ComparisonCompatible z.symm
      (curry.map ν ≫ (curryObjProdComp P P Tx).hom) μ
      (inverse_curried_tensor_coordinates g fx Tx sx)
      (inverse_curried_tensor_coordinates e fz Tz sz) := by
  intro V W
  simp only [NatTrans.comp_app, curry_map_app_app, curryObjProdComp_hom_app_app]
  erw [Category.comp_id]
  simpa only [inverse_curried_tensor_coordinates, NatIso.ofComponents_hom_app,
    Iso.app_hom, Iso.symm_hom, Iso.symm_inv, uncurry_tensor_natTrans,
    uncurry_obj_map, Functor.comp_obj, Functor.prod_obj, uncurry_obj_obj,
    curry_obj_obj_obj, postcompose₂_obj_obj_obj_obj,
    whiskeringLeft₂_obj_obj_obj_obj_obj] using h V W

private theorem scalar_uncurry_compatible
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    (e : A ⥤ C) (g : B ⥤ D) (P : C ⥤ D) (P₀ : A ⥤ B)
    (T : A ⥤ A ⥤ A) (U : B ⥤ B ⥤ B)
    (Ti : C × C ⥤ C) (Ui : D × D ⥤ D)
    (r : e ⋙ P ≅ P₀ ⋙ g)
    (t : (postcompose₂.obj e).obj T ≅
      (((whiskeringLeft₂ C).obj e).obj e).obj (curry.obj Ti))
    (s : (postcompose₂.obj g).obj U ≅
      (((whiskeringLeft₂ D).obj g).obj g).obj (curry.obj Ui))
    (μ : (postcompose₂.obj P₀).obj T ⟶
      (((whiskeringLeft₂ B).obj P₀).obj P₀).obj U)
    (ν : Ti ⋙ P ⟶ (P.prod P) ⋙ Ui)
    (h : Adjunction.ComparisonCompatible r μ
      (curry.map ν ≫ (curryObjProdComp P P Ui).hom) s t) (V W : A) :
    g.map ((uncurry_tensor_natTrans P₀ T U μ).app (V, W)) ≫
        (tensor_realization_uncurry g U Ui s).hom.app (P₀.obj V, P₀.obj W) =
      r.inv.app ((uncurry.obj T).obj (V, W)) ≫
        P.map ((tensor_realization_uncurry e T Ti t).hom.app (V, W)) ≫
        ν.app (e.obj V, e.obj W) ≫
        Ui.map (Prod.mkHom (r.hom.app V) (r.hom.app W)) := by
  rw [tensor_realization_uncurry_hom, tensor_realization_uncurry_hom]
  have hh := h V W
  simp only [NatTrans.comp_app, curry_map_app_app, curryObjProdComp_hom_app_app,
    curry_obj_map_app, curry_obj_obj_map, Category.assoc] at hh
  simp only [← Ui.map_comp, prod_comp, Category.comp_id, Category.id_comp] at hh
  erw [Category.id_comp] at hh
  exact hh

private theorem tensor_realization_uncurry_hom
    {A B : Type*} [Category A] [Category B] (F : A ⥤ B)
    (T : A ⥤ A ⥤ A) (U : B × B ⥤ B)
    (t : (postcompose₂.obj F).obj T ≅
      (((whiskeringLeft₂ B).obj F).obj F).obj (curry.obj U)) (V W : A) :
    (tensor_realization_uncurry F T U t).hom.app (V, W) = (t.hom.app V).app W := by
  change (t.hom.app V).app W ≫ 𝟙 _ = _
  exact Category.comp_id _

private def tensor_realization_uncurry
    {A B : Type*} [Category A] [Category B] (F : A ⥤ B)
    (T : A ⥤ A ⥤ A) (U : B × B ⥤ B)
    (t : (postcompose₂.obj F).obj T ≅
      (((whiskeringLeft₂ B).obj F).obj F).obj (curry.obj U)) :
    uncurry.obj T ⋙ F ≅ (F.prod F) ⋙ U :=
  uncurry_tensor_iso F T (curry.obj U) t ≪≫
    isoWhiskerLeft (F.prod F) (currying.counitIso.app U)

private def uncurry_tensor_iso
    {A B : Type*} [Category A] [Category B] (F : A ⥤ B)
    (T : A ⥤ A ⥤ A) (U : B ⥤ B ⥤ B)
    (t : (postcompose₂.obj F).obj T ≅ (((whiskeringLeft₂ B).obj F).obj F).obj U) :
    uncurry.obj T ⋙ F ≅ (F.prod F) ⋙ uncurry.obj U :=
  NatIso.ofComponents (fun Z ↦ (t.app Z.1).app Z.2)
    (by intro X Y f; exact (uncurry_tensor_natTrans F T U t.hom).naturality f)

private def uncurry_tensor_natTrans
    {A B : Type*} [Category A] [Category B] (F : A ⥤ B)
    (T : A ⥤ A ⥤ A) (U : B ⥤ B ⥤ B)
    (t : (postcompose₂.obj F).obj T ⟶ (((whiskeringLeft₂ B).obj F).obj F).obj U) :
    uncurry.obj T ⋙ F ⟶ (F.prod F) ⋙ uncurry.obj U where
  app Z := (t.app Z.1).app Z.2
  naturality := by
    rintro ⟨X, Y⟩ ⟨X', Y'⟩ ⟨f, g⟩
    have h₁ := NatTrans.congr_app (t.naturality f) Y
    have h₂ := (t.app X').naturality g
    dsimp only [postcompose₂_obj_obj_map_app, postcompose₂_obj_obj_obj_map,
      whiskeringLeft₂_obj_obj_obj_map_app, whiskeringLeft₂_obj_obj_obj_obj_map,
      NatTrans.comp_app] at h₁ h₂
    simp only [Functor.comp_map, Functor.prod_map, uncurry_obj_map, Functor.map_comp,
      Category.assoc]
    rw [h₂, ← Category.assoc, h₁, Category.assoc]
    rfl

private theorem tensor_inverseComparison
    {A C : Type*} [Category A] [Category C] (e : A ≌ C)
    (T : A × A ⥤ A) (Ti : C × C ⥤ C)
    (t : T ⋙ e.functor ≅ (e.functor.prod e.functor) ⋙ Ti)
    (s : Ti ≅ (e.inverse.prod e.inverse) ⋙ T ⋙ e.functor)
    (hs : ∀ V W, s.inv.app (V, W) = t.hom.app (e.inverse.obj V, e.inverse.obj W) ≫
      Ti.map (Prod.mkHom (e.counitIso.hom.app V) (e.counitIso.hom.app W))) (V W : C) :
    (inverse_tensor_coordinates e T Ti s).hom.app (V, W) =
      (inverseComparison (e.prod e) e Ti T t.symm).hom.app (V, W) := by
  have he : (s.app (V, W)).symm = t.app (e.inverse.obj V, e.inverse.obj W) ≪≫
      Ti.mapIso (Iso.prod (e.counitIso.app V) (e.counitIso.app W)) := by
    apply Iso.ext
    exact hs V W
  have hi : s.hom.app (V, W) =
      Ti.map (Prod.mkHom (e.counitIso.inv.app V) (e.counitIso.inv.app W)) ≫
        t.inv.app (e.inverse.obj V, e.inverse.obj W) := by
    simpa only [Iso.symm_inv, Iso.trans_inv, Functor.mapIso_inv, Iso.prod_inv,
      Iso.app_inv, Iso.app_hom] using congrArg Iso.inv he
  rw [inverse_tensor_app, hi, Functor.map_comp]
  simp only [inverseComparison, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    isoWhiskerRight_hom, isoWhiskerLeft_hom,
    whiskerRight_app, whiskerLeft_app, Functor.comp_map, Category.assoc]
  rfl

private theorem tensor_compatibility_transport_of_eq
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    (e : A ⥤ C) (g : B ⥤ D) (P P' : C ⥤ D) (P₀ : A ⥤ B)
    (T : A × A ⥤ A) (U : B × B ⥤ B)
    (Ti Ti' : C × C ⥤ C) (Ui Ui' : D × D ⥤ D)
    (r : e ⋙ P ≅ P₀ ⋙ g) (p : P ≅ P') (a : Ti ≅ Ti') (b : Ui ≅ Ui')
    (t : T ⋙ e ≅ (e.prod e) ⋙ Ti) (u : U ⋙ g ≅ (g.prod g) ⋙ Ui)
    (μ : T ⋙ P₀ ⟶ (P₀.prod P₀) ⋙ U)
    (ν : Ti ⋙ P ≅ (P.prod P) ⋙ Ui)
    (r' : e ⋙ P' ≅ P₀ ⋙ g)
    (t' : T ⋙ e ≅ (e.prod e) ⋙ Ti') (u' : U ⋙ g ≅ (g.prod g) ⋙ Ui')
    (k : Ti' ⋙ P' ≅ (P'.prod P') ⋙ Ui')
    (hr : r' = isoWhiskerLeft e p.symm ≪≫ r)
    (ht : t' = t ≪≫ isoWhiskerLeft (e.prod e) a)
    (hu : u' = u ≪≫ isoWhiskerLeft (g.prod g) b)
    (hk : k = isoWhiskerLeft Ti' p.symm ≪≫ isoWhiskerRight a.symm P ≪≫ ν ≪≫
      isoWhiskerLeft (P.prod P) b ≪≫ isoWhiskerRight (NatIso.prod p p) Ui')
    (h : ∀ V W, g.map (μ.app (V, W)) ≫ u.hom.app (P₀.obj V, P₀.obj W) =
      r.inv.app (T.obj (V, W)) ≫ P.map (t.hom.app (V, W)) ≫
        ν.hom.app (e.obj V, e.obj W) ≫
        Ui.map (Prod.mkHom (r.hom.app V) (r.hom.app W))) (V W : A) :
    g.map (μ.app (V, W)) ≫ u'.hom.app (P₀.obj V, P₀.obj W) =
      r'.inv.app (T.obj (V, W)) ≫ P'.map (t'.hom.app (V, W)) ≫
        k.hom.app (e.obj V, e.obj W) ≫
        Ui'.map (Prod.mkHom (r'.hom.app V) (r'.hom.app W)) := by
  subst r' t' u' k
  exact tensor_compatibility_transport_iso e g P P' P₀ T U Ti Ti' Ui Ui' r p a b t u
    μ ν h V W

private theorem tensor_compatibility_transport_iso
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    (e : A ⥤ C) (g : B ⥤ D) (P P' : C ⥤ D) (P₀ : A ⥤ B)
    (T : A × A ⥤ A) (U : B × B ⥤ B)
    (Ti Ti' : C × C ⥤ C) (Ui Ui' : D × D ⥤ D)
    (r : e ⋙ P ≅ P₀ ⋙ g) (p : P ≅ P') (a : Ti ≅ Ti') (b : Ui ≅ Ui')
    (t : T ⋙ e ≅ (e.prod e) ⋙ Ti) (u : U ⋙ g ≅ (g.prod g) ⋙ Ui)
    (μ : T ⋙ P₀ ⟶ (P₀.prod P₀) ⋙ U)
    (ν : Ti ⋙ P ≅ (P.prod P) ⋙ Ui)
    (h : ∀ V W, g.map (μ.app (V, W)) ≫ u.hom.app (P₀.obj V, P₀.obj W) =
      r.inv.app (T.obj (V, W)) ≫ P.map (t.hom.app (V, W)) ≫
        ν.hom.app (e.obj V, e.obj W) ≫
        Ui.map (Prod.mkHom (r.hom.app V) (r.hom.app W))) (V W : A) :
    let r' := isoWhiskerLeft e p.symm ≪≫ r
    let t' := t ≪≫ isoWhiskerLeft (e.prod e) a
    let u' := u ≪≫ isoWhiskerLeft (g.prod g) b
    let k := isoWhiskerLeft Ti' p.symm ≪≫ isoWhiskerRight a.symm P ≪≫ ν ≪≫
      isoWhiskerLeft (P.prod P) b ≪≫ isoWhiskerRight (NatIso.prod p p) Ui'
    g.map (μ.app (V, W)) ≫ u'.hom.app (P₀.obj V, P₀.obj W) =
      r'.inv.app (T.obj (V, W)) ≫ P'.map (t'.hom.app (V, W)) ≫
        k.hom.app (e.obj V, e.obj W) ≫
        Ui'.map (Prod.mkHom (r'.hom.app V) (r'.hom.app W)) := by
  dsimp only
  simpa only [Iso.trans_hom, Iso.symm_hom, Iso.symm_inv, NatTrans.comp_app,
    isoWhiskerLeft_hom, isoWhiskerRight_hom, whiskerLeft_app, whiskerRight_app,
    NatIso.prod_hom, NatTrans.prod, Functor.prod_obj, Category.assoc] using
    tensor_compatibility_transport e g P P' P₀ T U Ti Ti' Ui Ui' r p a b t u μ ν.hom h V W

private theorem tensor_compatibility_transport
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    (e : A ⥤ C) (g : B ⥤ D) (P P' : C ⥤ D) (P₀ : A ⥤ B)
    (T : A × A ⥤ A) (U : B × B ⥤ B)
    (Ti Ti' : C × C ⥤ C) (Ui Ui' : D × D ⥤ D)
    (r : e ⋙ P ≅ P₀ ⋙ g) (p : P ≅ P') (a : Ti ≅ Ti') (b : Ui ≅ Ui')
    (t : T ⋙ e ≅ (e.prod e) ⋙ Ti) (u : U ⋙ g ≅ (g.prod g) ⋙ Ui)
    (μ : T ⋙ P₀ ⟶ (P₀.prod P₀) ⋙ U)
    (ν : Ti ⋙ P ⟶ (P.prod P) ⋙ Ui)
    (h : ∀ V W, g.map (μ.app (V, W)) ≫ u.hom.app (P₀.obj V, P₀.obj W) =
      r.inv.app (T.obj (V, W)) ≫ P.map (t.hom.app (V, W)) ≫
        ν.app (e.obj V, e.obj W) ≫
        Ui.map (Prod.mkHom (r.hom.app V) (r.hom.app W))) (V W : A) :
    let r' := isoWhiskerLeft e p.symm ≪≫ r
    let t' := t ≪≫ isoWhiskerLeft (e.prod e) a
    let u' := u ≪≫ isoWhiskerLeft (g.prod g) b
    g.map (μ.app (V, W)) ≫ u'.hom.app (P₀.obj V, P₀.obj W) =
      r'.inv.app (T.obj (V, W)) ≫ P'.map (t'.hom.app (V, W)) ≫
        p.inv.app (Ti'.obj (e.obj V, e.obj W)) ≫
        P.map (a.inv.app (e.obj V, e.obj W)) ≫ ν.app (e.obj V, e.obj W) ≫
        b.hom.app (P.obj (e.obj V), P.obj (e.obj W)) ≫
        Ui'.map (Prod.mkHom (p.hom.app (e.obj V)) (p.hom.app (e.obj W))) ≫
        Ui'.map (Prod.mkHom (r'.hom.app V) (r'.hom.app W)) := by
  dsimp only
  simp only [Iso.trans_hom, Iso.trans_inv, Iso.symm_inv, Iso.symm_hom,
    NatTrans.comp_app, isoWhiskerLeft_hom, isoWhiskerLeft_inv,
    whiskerLeft_app, Functor.map_comp, Category.assoc]
  rw [← p.hom.naturality_assoc, ← p.hom.naturality_assoc]
  dsimp only [Functor.comp_obj]
  erw [Iso.hom_inv_id_app_assoc]
  dsimp only [Functor.prod_obj]
  rw [← P.map_comp_assoc (a.hom.app _) (a.inv.app _), Iso.hom_inv_id_app]
  erw [P.map_id, Category.id_comp]
  have hp : Prod.mkHom (p.hom.app (e.obj V)) (p.hom.app (e.obj W)) ≫
      Prod.mkHom (p.inv.app (e.obj V) ≫ r.hom.app V)
        (p.inv.app (e.obj W) ≫ r.hom.app W) =
      Prod.mkHom (r.hom.app V) (r.hom.app W) := by
    ext <;> simp
  rw [← Ui'.map_comp, hp]
  rw [reassoc_of% (h V W)]
  erw [b.hom.naturality]
  rfl

private theorem inverse_tensor_compatibility
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    (e : A ≌ C) (g : B ≌ D) (P : C ⥤ D) (P₀ : A ⥤ B)
    (T : A × A ⥤ A) (U : B × B ⥤ B)
    (Ti : C × C ⥤ C) (Ui : D × D ⥤ D)
    (r : e.functor ⋙ P ≅ P₀ ⋙ g.functor)
    (t : T ⋙ e.functor ≅ (e.functor.prod e.functor) ⋙ Ti)
    (u : U ⋙ g.functor ≅ (g.functor.prod g.functor) ⋙ Ui)
    (μ : T ⋙ P₀ ⟶ (P₀.prod P₀) ⋙ U)
    (ν : Ti ⋙ P ⟶ (P.prod P) ⋙ Ui)
    (h : ∀ V W, g.functor.map (μ.app (V, W)) ≫ u.hom.app (P₀.obj V, P₀.obj W) =
      r.inv.app (T.obj (V, W)) ≫ P.map (t.hom.app (V, W)) ≫
        ν.app (e.functor.obj V, e.functor.obj W) ≫
        Ui.map (Prod.mkHom (r.hom.app V) (r.hom.app W))) (V W : C) :
    let z := inverseComparison e g P P₀ r
    let qt := inverseComparison (e.prod e) e Ti T t.symm
    let qu := inverseComparison (g.prod g) g Ui U u.symm
    g.inverse.map (ν.app (V, W)) ≫ qu.hom.app (P.obj V, P.obj W) =
      z.hom.app (Ti.obj (V, W)) ≫ P₀.map (qt.hom.app (V, W)) ≫
        μ.app (e.inverse.obj V, e.inverse.obj W) ≫
        U.map (Prod.mkHom (z.inv.app V) (z.inv.app W)) := by
  dsimp only
  let rF : (e.prod e).functor ⋙ Ti ⋙ P ≅ (T ⋙ P₀) ⋙ g.functor :=
    isoWhiskerRight t.symm P ≪≫ isoWhiskerLeft T r
  let rG : (e.prod e).functor ⋙ (P.prod P) ⋙ Ui ≅
      ((P₀.prod P₀) ⋙ U) ⋙ g.functor :=
    isoWhiskerRight (NatIso.prod r r) Ui ≪≫ isoWhiskerLeft (P₀.prod P₀) u.symm
  have hs (Z : A × A) : ν.app ((e.prod e).functor.obj Z) ≫ rG.hom.app Z =
      rF.hom.app Z ≫ g.functor.map (μ.app Z) := by
    rcases Z with ⟨V, W⟩
    dsimp only [rF, rG, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
      isoWhiskerRight_hom, isoWhiskerLeft_hom, whiskerRight_app, whiskerLeft_app]
    apply (cancel_epi (r.inv.app (T.obj (V, W)) ≫ P.map (t.hom.app (V, W)))).1
    dsimp only [Equivalence.prod_functor, Functor.prod_obj, NatIso.prod, NatTrans.prod]
    simp only [Category.assoc]
    rw [← reassoc_of% (h V W)]
    simp only [← P.map_comp_assoc, Iso.hom_inv_id_app, Iso.hom_inv_id_app]
    dsimp only [Functor.comp_obj]
    erw [P.map_id, Category.id_comp, Iso.inv_hom_id_app_assoc, Category.comp_id]
  have hh := inverseComparison_square (e.prod e) g rF rG ν μ hs (V, W)
  simp only [rF, rG, inverseComparison_comp, Functor.comp_obj, Functor.prod_obj,
    Category.assoc] at hh
  let z := inverseComparison e g P P₀ r
  erw [inverseComparison_comp (e.prod e) (g.prod g) g
    (P.prod P) Ui (P₀.prod P₀) U (NatIso.prod r r) u.symm] at hh
  rw [inverseComparison_prod] at hh
  apply (cancel_mono (U.mapIso (Iso.prod (z.app V) (z.app W))).hom).1
  simp only [Functor.mapIso_hom, Iso.prod_hom, Iso.app_hom, z, Category.assoc]
  rw [← U.map_comp]
  have hc : Prod.mkHom ((inverseComparison e g P P₀ r).inv.app V)
      ((inverseComparison e g P P₀ r).inv.app W) ≫
      Prod.mkHom ((inverseComparison e g P P₀ r).hom.app V)
        ((inverseComparison e g P P₀ r).hom.app W) = 𝟙 _ := by
    ext <;> simp
  rw [hc]
  dsimp only [Functor.comp_obj]
  erw [U.map_id, Category.comp_id]
  exact hh

private theorem inverseComparison_prod
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    (e : A ≌ C) (g : B ≌ D) (P : C ⥤ D) (P₀ : A ⥤ B)
    (r : e.functor ⋙ P ≅ P₀ ⋙ g.functor) (X Y : C) :
    (inverseComparison (e.prod e) (g.prod g) (P.prod P) (P₀.prod P₀)
      (NatIso.prod r r)).hom.app (X, Y) =
      Prod.mkHom ((inverseComparison e g P P₀ r).hom.app X)
        ((inverseComparison e g P P₀ r).hom.app Y) := by
  rfl

private theorem inverseComparison_comp
    {A B C D E F : Type*}
    [Category A] [Category B] [Category C] [Category D] [Category E] [Category F]
    (e : A ≌ C) (g : B ≌ D) (h : E ≌ F)
    (P : C ⥤ D) (Q : D ⥤ F) (P₀ : A ⥤ B) (Q₀ : B ⥤ E)
    (r : e.functor ⋙ P ≅ P₀ ⋙ g.functor)
    (s : g.functor ⋙ Q ≅ Q₀ ⋙ h.functor) (X : C) :
    (inverseComparison e h (P ⋙ Q) (P₀ ⋙ Q₀)
      (isoWhiskerRight r Q ≪≫ isoWhiskerLeft P₀ s)).hom.app X =
      (inverseComparison g h Q Q₀ s).hom.app (P.obj X) ≫
        Q₀.map ((inverseComparison e g P P₀ r).hom.app X) := by
  have he := inverseComparison_evaluation g h Q Q₀ s
    (P.map (e.counitIso.inv.app X) ≫ r.hom.app (e.inverse.obj X))
    (𝟙 (Q₀.obj (P₀.obj (e.inverse.obj X))))
  simp only [Functor.map_comp, Category.assoc] at he
  erw [h.functor.map_id, h.inverse.map_id, Category.comp_id] at he
  simpa only [inverseComparison, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    isoWhiskerRight_hom, isoWhiskerLeft_hom, whiskerRight_app, whiskerLeft_app,
    Functor.comp_map, Functor.map_comp, Category.assoc, Category.id_comp,
    Category.comp_id, Functor.id_obj, Functor.comp_obj] using he

private theorem inverseComparison_square
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    (e : A ≌ C) (g : B ≌ D) {F G : C ⥤ D} {F₀ G₀ : A ⥤ B}
    (r : e.functor ⋙ F ≅ F₀ ⋙ g.functor)
    (s : e.functor ⋙ G ≅ G₀ ⋙ g.functor)
    (α : F ⟶ G) (β : F₀ ⟶ G₀)
    (h : ∀ X, α.app (e.functor.obj X) ≫ s.hom.app X =
      r.hom.app X ≫ g.functor.map (β.app X)) (X : C) :
    g.inverse.map (α.app X) ≫ (inverseComparison e g G G₀ s).hom.app X =
      (inverseComparison e g F F₀ r).hom.app X ≫ β.app (e.inverse.obj X) := by
  simp only [inverseComparison, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    isoWhiskerRight_hom, isoWhiskerLeft_hom, whiskerRight_app, whiskerLeft_app,
    Functor.comp_map, Category.assoc]
  dsimp only [Functor.comp_obj]
  rw [← g.inverse.map_comp_assoc, ← α.naturality]
  simp only [Functor.map_comp, Category.assoc]
  rw [← g.inverse.map_comp_assoc (α.app _) (s.hom.app _), h]
  simp only [g.inverse.map_comp, Category.assoc]
  erw [g.unitIso.inv.naturality]
  rfl

/-- The local open tensor square, before applying any proper direct image.
Source: fix-prop-projection-formula.proof.md, open tensor step; Stacks 0E8I and 07A4.
(blueprint: lem-sf-finite-intrinsic-projection-open-square-core).

Proof: transpose the intrinsic inverse open tensor map under the open adjunction.
Identify the specified unit by the ordinary conjugate adjunction and exact localization.
The scalar tensor comparison on flat-term K-flat representatives identifies the tensor
part of the transpose, and naturality along resolving isomorphisms extends it to arbitrary
derived inputs. The equivalence triangle identities cancel the units. Injectivity of the
adjunction identifies the inverse maps. The fixed open projection is invertible, so the
intrinsic map is invertible and inverseOnDomain is its inverse. Invert the equation and
use naturality in the two tensor inputs, first along k and then along the arbitrary b.
There is no proper direct image, midpoint, beforeCompositor, or constructibility hypothesis
in this equation. Zero inputs, empty and identity opens and m = 0 satisfy the same formulas. -/
theorem finiteIntrinsicProjectionOpenSquareCore
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    {E : Type u} [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] (m : ℕ)
    {X Y : SixFunctorSpace D} (f : X ⟶ Y) (c : Compactification f.hom.left)
    (U M : normalizedDVRDerived C.l E X.obj.left m)
    (N : normalizedDVRDerived C.l E c.Z m) (k : U ≅ M)
    (W : DerivedCategory (Sheaf (ProEt.topology c.Z)
      (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing C.l E (m + 1))))))
    (b : (sfIntrinsicDerivedEquivalence c.Z
      (Padic.coefficientExtensionRing C.l E (m + 1))).inverse.obj N ⟶ W) :
    let A := Padic.coefficientExtensionRing C.l E (m + 1)
    let B := ModuleCat.{u + 1} (ULift.{u + 1} A)
    let Q := compactSupportProjectionSquare f c
    let RX := realization (C := C) (E := E) (n := m + 1) (hn := Nat.le_add_left 1 m) X
    let RZ := realization (C := C) (E := E) (n := m + 1) (hn := Nat.le_add_left 1 m) Q.Z
    let J := (sfIntrinsicExtensionByZero c.i A).mapDerivedCategory
    let P := finiteDerivedPullback C.l E m c.i
    let Jf := (openImmersionLowerShriek B c.i).mapDerivedCategory
    let Pf := (upperStar B c.i).leftDerivedFunctor
    let tx := Functor.uncurry.obj (derivedTensor B X.obj.left)
    let tz := Functor.uncurry.obj (derivedTensor B c.Z)
    let sx := canonicalFiniteIntrinsicTensorComparison (C := C) (E := E) m X
    let sz := canonicalFiniteIntrinsicTensorComparison (C := C) (E := E) m Q.Z
    let ej := FiniteIntrinsicRealization.openComparison (C := C) (E := E) m f c
    let ep := FiniteIntrinsicRealization.inversePullback (C := C) (E := E) m Q.i
    let pj := RZ.inverse.mapIso
      (J.mapIso (k ≪≫ (RX.counitIso.app M).symm) ≪≫ ej.app (RX.inverse.obj M)) ≪≫
        (RZ.unitIso.app _).symm
    sz.hom.app (J.obj U, N) ≫
        RZ.functor.map (tz.map (Prod.mkHom pj.hom b)) ≫
        RZ.functor.map (((derivedOpenImmersionLowerShriekProjectionIso B c.i).inv.app
          (RX.inverse.obj M)).app W) =
      SystemProjectionFormula.inverseOnDomain
          (SystemProjectionFormula.finiteOpenTensorInv C.l E D C.different c.i
            X.obj.hom (c.g ≫ Y.obj.hom) m U N) ≫
        J.map (sx.hom.app (U, P.obj N)) ≫
        ej.hom.app (tx.obj (RX.inverse.obj U, RX.inverse.obj (P.obj N))) ≫
        RZ.functor.map (Jf.map (tx.map (Prod.mkHom (𝟙 _) (ep.hom.app N)))) ≫
        RZ.functor.map (Jf.map
          (tx.map (Prod.mkHom (RX.inverse.map k.hom) (Pf.map b)))) := by sorry

end WeilConjectures.IntegralProjectionReduction
