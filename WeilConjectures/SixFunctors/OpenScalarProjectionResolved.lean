/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.OpenScalarTensorNativeModels
import all WeilConjectures.Algebra.Homology.ScalarTensorExactRepresentative

/-! # Scalar projection through resolved chain adjuncts

Source: Stacks Project, Tags 07A4, 07A6 and 0FPT.
(blueprint: lem-sp-open-scalar-projection-resolved).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory WeilConjectures

private theorem projection_representative_paste
    {A B : Type*} [Category* A] [Category* B]
    {HA : Aᵒᵖ × A ⥤ A} {HB : Bᵒᵖ × B ⥤ B}
    (S : CoefficientClosedStructure HA) (T : CoefficientClosedStructure HB)
    {F : A ⥤ B} {U : B ⥤ A} (adj : F ⊣ U)
    (μ : S.tensor ⋙ F ≅ F.prod F ⋙ T.tensor)
    (P C X : A) (EP EC ET H : B)
    (i : X ≅ S.tensor.obj (P, C)) (eP : F.obj P ≅ EP)
    (eC : F.obj C ⟶ EC) (eT : F.obj X ⟶ ET)
    (g : ET ⟶ T.tensor.obj (EP, EC))
    (u : T.monoidal.tensorUnit ≅ H) (q : U.obj T.monoidal.tensorUnit ≅ C)
    (t : EC ⟶ H)
    (hn : F.map i.hom ≫ μ.hom.app (P, C) ≫
      T.tensor.map (Prod.mkHom eP.hom eC) = eT ≫ g)
    (hc : F.map q.inv ≫ adj.counit.app T.monoidal.tensorUnit = eC ≫ t ≫ u.inv) :
    i.hom ≫ S.tensor.map (Prod.mkHom (𝟙 P) q.inv) ≫
      adj.homEquiv _ _ (μ.hom.app (P, U.obj T.monoidal.tensorUnit) ≫
        T.tensor.map (Prod.mkHom (𝟙 _) (adj.counit.app T.monoidal.tensorUnit)) ≫
        (T.monoidal.rightUnitor (F.obj P)).hom) ≫ U.map eP.hom =
    adj.homEquiv _ _ (eT ≫ g ≫ T.tensor.map (Prod.mkHom (𝟙 EP) t) ≫
      T.tensor.map (Prod.mkHom (𝟙 EP) u.inv) ≫ (T.monoidal.rightUnitor EP).hom) := by
  let := S.monoidal
  let := T.monoidal
  erw [← adj.homEquiv_naturality_right, ← adj.homEquiv_naturality_left,
    ← adj.homEquiv_naturality_left]
  apply congrArg (adj.homEquiv _ _)
  simp only [Category.assoc]
  have hm := μ.hom.naturality (Prod.mkHom (𝟙 P) q.inv)
  change F.map (S.tensor.map (Prod.mkHom (𝟙 P) q.inv)) ≫ μ.hom.app _ =
    μ.hom.app _ ≫ T.tensor.map (Prod.mkHom (F.map (𝟙 P)) (F.map q.inv)) at hm
  erw [F.map_id] at hm
  erw [reassoc_of% hm]
  have hr : T.tensor.map (Prod.mkHom eP.hom (𝟙 T.monoidal.tensorUnit)) ≫
      (T.monoidal.rightUnitor EP).hom =
      (T.monoidal.rightUnitor (F.obj P)).hom ≫ eP.hom := by
    simpa only [CoefficientClosedStructure.tensor, tensor_map, ← tensorHom_id] using
      rightUnitor_naturality eP.hom
  erw [← hr, ← T.tensor.map_comp_assoc, ← T.tensor.map_comp_assoc]
  have hp : Prod.mkHom (𝟙 (F.obj P)) (F.map q.inv) ≫
      Prod.mkHom (𝟙 (F.obj P)) (adj.counit.app T.monoidal.tensorUnit) ≫
      Prod.mkHom eP.hom (𝟙 T.monoidal.tensorUnit) =
      Prod.mkHom eP.hom eC ≫ Prod.mkHom (𝟙 EP) t ≫ Prod.mkHom (𝟙 EP) u.inv := by
    apply Prod.ext
    · simp
    · change F.map q.inv ≫ adj.counit.app T.monoidal.tensorUnit ≫ 𝟙 _ =
        eC ≫ t ≫ u.inv
      simpa only [Category.comp_id] using hc
  simp only [Category.assoc]
  erw [hp, T.tensor.map_comp, T.tensor.map_comp]
  simpa only [Category.assoc] using congrArg
    (fun z ↦ z ≫ T.tensor.map (Prod.mkHom (𝟙 EP) t) ≫
      T.tensor.map (Prod.mkHom (𝟙 EP) u.inv) ≫ (T.monoidal.rightUnitor EP).hom) hn

private theorem counit_from_normalization
    {A B : Type*} [Category* A] [Category* B]
    {F : A ⥤ B} {U : B ⥤ A} (adj : F ⊣ U)
    {C : A} {EC H V : B} (eC : F.obj C ⟶ EC) (t : EC ⟶ H)
    (u : V ≅ H) (q : U.obj V ≅ C) (v : C ⟶ U.obj H)
    (hn : (adj.homEquiv C H).symm v = eC ≫ t)
    (hq : q.inv ≫ U.map u.hom = v) :
    F.map q.inv ≫ adj.counit.app V = eC ≫ t ≫ u.inv := by
  rw [← Category.assoc, ← hn, ← adj.homEquiv_naturality_right_symm, ← hq]
  simp only [Category.assoc, ← U.map_comp, Iso.hom_inv_id, U.map_id,
    Category.comp_id, Adjunction.homEquiv_counit]

universe u
open AlgebraicGeometry AlgebraicGeometry.Scheme SheafOfModules
namespace AlgebraicGeometry.ProEtale.OpenScalarTensor
attribute [local instance] ScalarDerivedPair.extension_additive

set_option maxHeartbeats 2000000 in
-- Pasting compares dependent tensor and adjunction presentations of derived complexes.
/-- A quasi-isomorphism for the balanced chain adjunct proves invertibility of the
specified scalar projection on the first flat K-flat representative.
Source: Stacks Project, Tags 07A4, 07A6 and 0FPT
(blueprint: lem-sp-open-scalar-projection-resolved).

Proof: identify the restricted derived tensor unit with the chosen resolution of
its coefficient complex. The normalized scalar adjunction identifies its counit
with the transpose of the resolution map. Naturality of the scalar tensorator
and the right unitor pastes the projection adjunct into the representative tensor
square. The representative right-unitor equation then gives the localization of
the chain adjunct. The comparison for transposition commutes with localization,
so its quasi-isomorphism makes this localized map invertible. Cancel the tensor
model isomorphism, the coefficient resolution isomorphism, and the scalar
comparison on the first K-flat complex. -/
theorem scalarProjection_isIso_of_chain
    (m : Models.{u}) (c : Choices m)
    {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B) (T : Scheme.{u})
    (β : @SymmetricCategory (proEtaleDerivedCategory T B) _
      ((m T).closed (proEtaleConstantRing T B)).monoidal)
    (hc : RingedDerivedTensorCoherence.{u + 1, u, u + 1, u + 2}
      (Scheme.ProEt.topology T) (proEtaleConstantRing T B)
      ((m T).closed (proEtaleConstantRing T B)) ((m T).model (proEtaleConstantRing T B)) β)
    (P Q : CochainComplex (proEtaleRingModules T (proEtaleConstantRing T A)) ℤ)
    (hp : proEtaleFlatRepresentatives T (proEtaleConstantRing T A) P)
    (hq : proEtaleFlatRepresentatives T (proEtaleConstantRing T A) Q)
    (g : Q ⟶ ((SheafOfModules.scalarRestriction
      (proEtaleConstantRingMap (T := T) φ)).mapHomologicalComplex
      (.up ℤ)).obj (ringedTensorUnitComplex.{u + 1, u, u + 1}
        (Scheme.ProEt.topology T) (proEtaleConstantRing T B))) [QuasiIso g]
    (r : (coefficientTotalTensor.{u + 1, u + 1, u} (Scheme.ProEt.topology T)
      (proEtaleConstantRing T B)).obj
        ((scalarComplex.{u + 1, u, u + 1} (scalarPair m φ T).extension
      (scalarPair m φ T).extension_additive).obj P,
          ringedTensorUnitComplex.{u + 1, u, u + 1}
            (Scheme.ProEt.topology T) (proEtaleConstantRing T B)) ≅
        (scalarComplex.{u + 1, u, u + 1} (scalarPair m φ T).extension
      (scalarPair m φ T).extension_additive).obj P)
    (hr : (hc.tensorIso _ _ (Or.inl ((c.scalarTensor φ T).preservesKFlat P
      ((CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat P).mpr hp.1)))).hom ≫
      ((m T).closed (proEtaleConstantRing T B)).tensor.map
        (Prod.mkHom (𝟙 _) hc.unitIso.inv) ≫
      (((m T).closed (proEtaleConstantRing T B)).monoidal.rightUnitor _).hom =
        DerivedCategory.Q.map r.hom)
    (hk : let adj :=
      (((m T).scalar
        (proEtaleConstantRingMap (T := T) φ)).ordinaryAdjunction).mapHomologicalComplex (.up ℤ)
      QuasiIso (adj.homEquiv _ _ (((c.scalarTensor φ T).complexIso P Q).hom ≫
        (coefficientTotalTensor.{u + 1, u + 1, u} (Scheme.ProEt.topology T)
          (proEtaleConstantRing T B)).map
          (Prod.mkHom (𝟙 _) (scalarChainTranspose
            (proEtaleConstantRingMap (T := T) φ) (scalarPair m φ T).extension
            (scalarPair m φ T).extension_additive (scalarPair m φ T).ordinaryAdjunction
            Q _ g)) ≫ r.hom))) :
    IsIso (scalarProjection m c φ T (DerivedCategory.Q.obj P)) := by
  let J := Scheme.ProEt.topology T
  let RA := proEtaleConstantRing T A
  let RB := proEtaleConstantRing T B
  let a := proEtaleConstantRingMap (T := T) φ
  let s := scalarPair m φ T
  let F := s.derived
  let U := scalarRestriction φ T
  let E := scalarComplex.{u + 1, u, u + 1} s.extension s.extension_additive
  let BA := (m T).closed RA
  let BB := (m T).closed RB
  let TT := coefficientTotalTensor.{u + 1, u + 1, u} J RA
  let TS := coefficientTotalTensor.{u + 1, u + 1, u} J RB
  let O := ringedTensorUnitComplex.{u + 1, u, u + 1} J RB
  let t := scalarChainTranspose a s.extension s.extension_additive s.ordinaryAdjunction Q O g
  let e := fun V ↦ scalarPairComplexComparison s.extension s.extension_additive
    F s.counit V
  have hP := (CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat P).mpr hp.1
  have hQ := (CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat Q).mpr hq.1
  have heP : IsIso (e P) := s.computes P hP
  let ep : F.obj (DerivedCategory.Q.obj P) ≅ DerivedCategory.Q.obj (E.obj P) := asIso (e P)
  let i := (m T).model RA |>.iso J RA BA P Q hP hQ
  let q : U.obj BB.monoidal.tensorUnit ≅ DerivedCategory.Q.obj Q :=
    U.mapIso hc.unitIso ≪≫ (scalarRestrictionComparison a).app O ≪≫
      (asIso (DerivedCategory.Q.map g)).symm
  have hqn : q.inv ≫ U.map hc.unitIso.hom =
      DerivedCategory.Q.map g ≫ (scalarRestrictionComparison a).inv.app O := by
    simp only [q, Iso.trans_inv, Iso.symm_inv, asIso_hom, Functor.mapIso_inv,
      Category.assoc, ← U.map_comp, Iso.inv_hom_id, U.map_id, Category.comp_id,
      Iso.app_inv]
  have hcn : F.map q.inv ≫ s.adjunction.counit.app BB.monoidal.tensorUnit =
      e Q ≫ DerivedCategory.Q.map t ≫ hc.unitIso.inv :=
    counit_from_normalization s.adjunction (e Q) (DerivedCategory.Q.map t) hc.unitIso q
      _ (s.normalization Q hQ hq.2 O g) hqn
  have heP' := (c.scalarTensor φ T).preservesKFlat P hP
  have heQ' := (c.scalarTensor φ T).preservesKFlat Q hQ
  let j := hc.tensorIso (E.obj P) (E.obj Q) (Or.inl heP')
  have hn : F.map i.hom ≫ (c.scalarTensor φ T).iso.hom.app
      (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫
      BB.tensor.map (Prod.mkHom ep.hom (e Q)) =
      e (TT.obj (P, Q)) ≫ DerivedCategory.Q.map ((c.scalarTensor φ T).complexIso P Q).hom ≫
        j.hom := by
    have h := (c.scalarTensor φ T).normalization P Q hP hQ
    rw [← hc.tensorIso_both (E.obj P) (E.obj Q) heP' heQ'] at h
    exact h
  have hh := projection_representative_paste BA BB s.adjunction
    (c.scalarTensor φ T).iso (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj Q)
    (DerivedCategory.Q.obj (TT.obj (P, Q))) (DerivedCategory.Q.obj (E.obj P))
    (DerivedCategory.Q.obj (E.obj Q))
    (DerivedCategory.Q.obj (E.obj (TT.obj (P, Q)))) (DerivedCategory.Q.obj O)
    i ep (e Q) (e (TT.obj (P, Q)))
    (DerivedCategory.Q.map ((c.scalarTensor φ T).complexIso P Q).hom ≫ j.hom)
    hc.unitIso q (DerivedCategory.Q.map t) (by simpa only [Category.assoc] using hn) hcn
  let l := ((c.scalarTensor φ T).complexIso P Q).hom ≫ TS.map (Prod.mkHom (𝟙 _) t) ≫ r.hom
  have hnat := hc.tensorIso_naturality (E.obj P) (E.obj Q) (E.obj P) O
    (Or.inl heP') (Or.inl heP') (𝟙 _) t
  erw [DerivedCategory.Q.map_id] at hnat
  have hmaps : e (TT.obj (P, Q)) ≫
      (DerivedCategory.Q.map ((c.scalarTensor φ T).complexIso P Q).hom ≫ j.hom) ≫
      BB.tensor.map (Prod.mkHom (𝟙 _) (DerivedCategory.Q.map t)) ≫
      BB.tensor.map (Prod.mkHom (𝟙 _) hc.unitIso.inv) ≫
      (BB.monoidal.rightUnitor _).hom = e (TT.obj (P, Q)) ≫ DerivedCategory.Q.map l := by
    dsimp only [l]
    simp only [Category.assoc, DerivedCategory.Q.map_comp]
    erw [← reassoc_of% hnat, hr]
  rw [hmaps] at hh
  have htr := ScalarHomTensor.transpose_comparison (J := J) (m T) a (TT.obj (P, Q))
    (E.obj P) l
  erw [ScalarHomTensor.pairComparison_app.{u + 1, u, u + 1, u + 2}
    (J := J) (m T) a] at htr
  have his : IsIso ((s.adjunction.homEquiv _ _) (e (TT.obj (P, Q)) ≫
      DerivedCategory.Q.map l)) := by
    rw [htr]
    have : QuasiIso (((ScalarHomTensor.chainAdj (J := J) (m T) a).homEquiv _ _) l) := hk
    infer_instance
  have hi : IsIso (BA.tensor.map (Prod.mkHom (𝟙 (DerivedCategory.Q.obj P)) q.inv)) :=
    (BA.tensor.mapIso ((Iso.refl _).prod q.symm)).isIso_hom
  change IsIso (scalarProjection m c φ T (DerivedCategory.Q.obj P))
  have hcomp : IsIso (i.hom ≫ BA.tensor.map
      (Prod.mkHom (𝟙 (DerivedCategory.Q.obj P)) q.inv) ≫
      scalarProjection m c φ T (DerivedCategory.Q.obj P) ≫ U.map ep.hom) := by
    rw [show i.hom ≫ BA.tensor.map _ ≫ scalarProjection m c φ T _ ≫ U.map ep.hom = _ from hh]
    exact his
  have hpre : IsIso (i.hom ≫ BA.tensor.map
      (Prod.mkHom (𝟙 (DerivedCategory.Q.obj P)) q.inv)) := inferInstance
  have hcomp' : IsIso ((i.hom ≫ BA.tensor.map
      (Prod.mkHom (𝟙 (DerivedCategory.Q.obj P)) q.inv)) ≫
      (scalarProjection m c φ T (DerivedCategory.Q.obj P) ≫ U.map ep.hom)) := by
    simpa only [Category.assoc] using hcomp
  have hmid : IsIso (scalarProjection m c φ T (DerivedCategory.Q.obj P) ≫ U.map ep.hom) :=
    IsIso.of_isIso_comp_left (i.hom ≫ BA.tensor.map
      (Prod.mkHom (𝟙 (DerivedCategory.Q.obj P)) q.inv)) _
  exact IsIso.of_isIso_comp_right _ (U.map ep.hom)

end AlgebraicGeometry.ProEtale.OpenScalarTensor
