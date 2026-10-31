/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.StrictEtaleLevelInverseTransport
import WeilConjectures.AlgebraicGeometry.StrictEtaleOrdinaryInverseTransport
import all WeilConjectures.AlgebraicGeometry.CoefficientEvaluationModels
import WeilConjectures.CategoryTheory.SystemEvaluationKFlat
import all WeilConjectures.AlgebraicGeometry.StrictEtaleInverseTensorCoherence
import WeilConjectures.AlgebraicGeometry.EtaleSetInverseImageExact

/-! # Evaluation of inverse-image coefficient transport

Source: Zheng, Construction 5.15, Lemma 5.16 and Proposition 2.29(2).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option genInjectivity false
set_option genSizeOfSpec false
set_option genSizeOf false
set_option genCtorIdx false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor SheafOfModules
namespace AlgebraicGeometry
attribute [local instance 5000] strictEtaleSystemDerived strictEtaleLevelDerived

attribute [local irreducible] coefficientQuotientSheaf coefficientQuotientMap
  siteCoefficientTensorAdj

private theorem scalarInsertion_ext
    {T : Scheme.{u}} {O O' : Type (u + 1)} [CommRing O] [CommRing O']
    {ell : O} {mu : O'} {phi : O →+* O'} {index : ℕ →o ℕ}
    (a : StrictEtaleCoefficientChange O O' ell mu phi index) (n : ℕ)
    (M : strictEtaleLevel T O ell (index n)) (N : strictEtaleLevel T O' mu n)
    (f g : (siteCoefficientTensor.{u + 1, u, u + 1} (a.sheaf T n)).obj M ⟶ N)
    (h : (sheafCompose T.smallEtaleTopology (forget AddCommGrpCat.{u + 1})).map
        (siteTensorUnitUnderlying (a.sheaf T n) M) ≫
          (coefficientUnderlying (J := T.smallEtaleTopology) O' mu n).map f =
      (sheafCompose T.smallEtaleTopology (forget AddCommGrpCat.{u + 1})).map
        (siteTensorUnitUnderlying (a.sheaf T n) M) ≫
          (coefficientUnderlying (J := T.smallEtaleTopology) O' mu n).map g) : f = g := by
  let adj := siteCoefficientTensorAdj.{u + 1, u, u + 1} (a.sheaf T n)
  let U := coefficientUnderlying (J := T.smallEtaleTopology) O ell (index n)
  let V := coefficientUnderlying (J := T.smallEtaleTopology) O' mu n
  let q := isoWhiskerRight (siteScalarUnderlyingIso (a.sheaf T n))
    (sheafCompose T.smallEtaleTopology (forget AddCommGrpCat.{u + 1}))
  apply (adj.homEquiv M N).injective
  apply U.map_injective
  apply (cancel_mono (q.hom.app N)).1
  rw [transpose_underlying adj U V q M N f, transpose_underlying adj U V q M N g]
  simpa only [q, U, V, adj, coefficientUnderlying, Functor.comp_map,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
    siteTensorUnitUnderlying, Functor.map_comp] using h

private theorem scalarInsertion_naturality
    {T : Scheme.{u}} {O O' : Type (u + 1)} [CommRing O] [CommRing O']
    {ell : O} {mu : O'} {phi : O →+* O'} {index : ℕ →o ℕ}
    (a : StrictEtaleCoefficientChange O O' ell mu phi index) (n : ℕ)
    {M N : strictEtaleLevel T O ell (index n)} (f : M ⟶ N) :
    (coefficientUnderlying (J := T.smallEtaleTopology) O ell (index n)).map f ≫
        (sheafCompose T.smallEtaleTopology (forget AddCommGrpCat.{u + 1})).map
          (siteTensorUnitUnderlying (a.sheaf T n) N) =
      (sheafCompose T.smallEtaleTopology (forget AddCommGrpCat.{u + 1})).map
          (siteTensorUnitUnderlying (a.sheaf T n) M) ≫
        (coefficientUnderlying (J := T.smallEtaleTopology) O' mu n).map
          ((siteCoefficientTensor.{u + 1, u, u + 1} (a.sheaf T n)).map f) := by
  let adj := siteCoefficientTensorAdj.{u + 1, u, u + 1} (a.sheaf T n)
  let U := coefficientUnderlying (J := T.smallEtaleTopology) O ell (index n)
  let V := coefficientUnderlying (J := T.smallEtaleTopology) O' mu n
  let q := isoWhiskerRight (siteScalarUnderlyingIso (a.sheaf T n))
    (sheafCompose T.smallEtaleTopology (forget AddCommGrpCat.{u + 1}))
  let η : U ⟶ siteCoefficientTensor.{u + 1, u, u + 1} (a.sheaf T n) ⋙ V :=
    whiskerRight adj.unit U ≫ whiskerLeft _ q.hom
  simpa only [η, U, V, q, adj, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Functor.isoWhiskerRight_hom, Functor.comp_map,
    siteTensorUnitUnderlying, coefficientUnderlying, Functor.map_comp] using η.naturality f

section Ordinary
variable {O O' : Type (u + 1)} [CommRing O] [CommRing O'] {ell : O} {mu : O'}
    {phi : O →+* O'} {index : ℕ →o ℕ}
    {a : StrictEtaleCoefficientChange O O' ell mu phi index}
    {T S : Scheme.{u}} {g : T ⟶ S}
    {PTA : StrictEtaleEvaluation T O ell} {PSA : StrictEtaleEvaluation S O ell}
    {PTB : StrictEtaleEvaluation T O' mu} {PSB : StrictEtaleEvaluation S O' mu}
    (UT : StrictEtaleCoefficientTransport a T PTA PTB)
    (US : StrictEtaleCoefficientTransport a S PSA PSB)
    (A : StrictEtaleOrdinaryImage O ell g) (B : StrictEtaleOrdinaryImage O' mu g)
    (DA : ∀ n, CoefficientDerivedImage (A.lift n).modules (A.right n) (A.levelAdj n))
    (DB : ∀ n, CoefficientDerivedImage (B.lift n).modules (B.right n) (B.levelAdj n))
    (finite : ∀ n, StrictEtaleLevelInverseTransport UT US A B DA DB n)

private theorem finite_unit_forward (n : ℕ) (M : strictEtaleLevel S O ell (index n)) :
    (Scheme.etaleSetPullback g).map
        ((sheafCompose S.smallEtaleTopology (forget AddCommGrpCat.{u + 1})).map
          (siteTensorUnitUnderlying (a.sheaf S n) M)) ≫
        (B.lift n).moduleUnderlying.inv.app _ ≫
        (coefficientUnderlying (J := T.smallEtaleTopology) O' mu n).map
          ((finite n).ordinary.hom.app M) =
      (A.lift (index n)).moduleUnderlying.inv.app M ≫
        (sheafCompose T.smallEtaleTopology (forget AddCommGrpCat.{u + 1})).map
          (siteTensorUnitUnderlying (a.sheaf T n) ((A.lift (index n)).modules.obj M)) := by
  have h := congrArg (fun z ↦ (A.lift (index n)).moduleUnderlying.inv.app M ≫ z ≫
    (B.lift n).moduleUnderlying.inv.app _ ≫
    (coefficientUnderlying (J := T.smallEtaleTopology) O' mu n).map
      ((finite n).ordinary.hom.app M)) ((finite n).unit M)
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc, Iso.inv_hom_id_app_assoc,
    ← Functor.map_comp, Iso.inv_hom_id_app] at h
  erw [CategoryTheory.Functor.map_id, Category.comp_id] at h
  exact h.symm

private theorem ordinary_evaluation
    (ordinary : US.ordinary ⋙ B.inverse ≅ A.inverse ⋙ UT.ordinary)
    (hu : ∀ n M,
      (UT.setUnit n).app (A.inverse.obj M) ≫
        (coefficientUnderlying (J := T.smallEtaleTopology) O' mu n).map
          ((coefficientEvaluation (J := T.smallEtaleTopology) (O := O') (ell := mu) n).map
            (ordinary.inv.app M)) ≫
        (strictEtaleInverseUnderlying B n).hom.app (US.ordinary.obj M) =
      (strictEtaleInverseUnderlying A (index n)).hom.app M ≫
        (Scheme.etaleSetPullback g).map ((US.setUnit n).app M)) (n : ℕ) (M) :
    (coefficientEvaluation (J := T.smallEtaleTopology) (O := O') (ell := mu) n).map
        (ordinary.inv.app M) ≫
      (B.inverseEvaluation n).hom.app (US.ordinary.obj M) ≫
      (B.lift n).modules.map ((US.val.evaluation n).hom.app M) =
    (UT.val.evaluation n).hom.app (A.inverse.obj M) ≫
      (siteCoefficientTensor.{u + 1, u, u + 1} (a.sheaf T n)).map
        ((A.inverseEvaluation (index n)).hom.app M) ≫
      (finite n).ordinary.inv.app (M.level (index n)) := by
  apply (cancel_epi ((UT.val.evaluation n).inv.app (A.inverse.obj M))).1
  simp only [Iso.inv_hom_id_app_assoc]
  apply scalarInsertion_ext a n
  apply (cancel_mono ((B.lift n).moduleUnderlying.hom.app
    ((siteCoefficientTensor.{u + 1, u, u + 1} (a.sheaf S n)).obj (M.level (index n))))).1
  simp only [Functor.map_comp, Category.assoc]
  have h := hu n M
  dsimp only [strictEtaleInverseUnderlying, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app] at h
  simp only [Category.id_comp, Category.assoc] at h
  have hut := UT.property.2.1 n (A.inverse.obj M)
  have hus := US.property.2.1 n M
  have hus' : (US.unit n).app M ≫
      (toSheaf _).map ((US.val.evaluation n).hom.app M) =
      siteTensorUnitUnderlying (a.sheaf S n) (M.level (index n)) := by
    rw [hus, Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_app]
    erw [CategoryTheory.Functor.map_id, Category.comp_id]
  erw [← (sheafCompose T.smallEtaleTopology (forget AddCommGrpCat.{u + 1})).map_comp_assoc,
    ← hut]
  have hn := (B.lift n).moduleUnderlying.hom.naturality ((US.val.evaluation n).hom.app M)
  dsimp only [Functor.comp_map] at hn
  erw [hn, reassoc_of% h]
  dsimp only [StrictEtaleCoefficientTransport.setUnit, Functor.whiskerRight_app]
  erw [← (Scheme.etaleSetPullback g).map_comp,
    ← (sheafCompose S.smallEtaleTopology (forget AddCommGrpCat.{u + 1})).map_comp, hus']
  have hi := scalarInsertion_naturality a n ((A.inverseEvaluation (index n)).hom.app M)
  have hu' := (finite n).unit (M.level (index n))
  have hu'' := congrArg (fun z ↦
    (coefficientUnderlying (J := T.smallEtaleTopology) O ell (index n)).map
      ((A.inverseEvaluation (index n)).hom.app M) ≫ z) hu'
  erw [← reassoc_of% hi]
  simpa only [coefficientUnderlying, coefficientEvaluation, Functor.comp_obj,
    Functor.comp_map, Category.assoc] using hu''.symm

end Ordinary

private theorem derived_square_exists
    {O O' : Type (u + 1)} [CommRing O] [CommRing O'] {ell : O} {mu : O'}
    {phi : O →+* O'} {index : ℕ →o ℕ}
    {a : StrictEtaleCoefficientChange O O' ell mu phi index}
    {T S : Scheme.{u}} {g : T ⟶ S}
    {PTA : StrictEtaleEvaluation T O ell} {PSA : StrictEtaleEvaluation S O ell}
    {PTB : StrictEtaleEvaluation T O' mu} {PSB : StrictEtaleEvaluation S O' mu}
    (UT : StrictEtaleCoefficientTransport a T PTA PTB)
    (US : StrictEtaleCoefficientTransport a S PSA PSB)
    (A : StrictEtaleOrdinaryImage O ell g) (B : StrictEtaleOrdinaryImage O' mu g)
    (DA : CoefficientDerivedImage A.inverse A.rightSystem A.systemAdj)
    (DB : CoefficientDerivedImage B.inverse B.rightSystem B.systemAdj)
    (ordinary : US.ordinary ⋙ B.inverse ≅ A.inverse ⋙ UT.ordinary) :
    ∃ derived : US.derived ⋙ DB.inverse ≅ DA.inverse ⋙ UT.derived,
      ∀ K,
        derived.hom.app (DerivedCategory.Q.obj K) ≫
            UT.derived.map (DA.inverseFactors.hom.app K) ≫
            UT.factors.hom.app ((A.inverse.mapHomologicalComplex (.up ℤ)).obj K) =
          DB.inverse.map (US.factors.hom.app K) ≫
            DB.inverseFactors.hom.app ((US.ordinary.mapHomologicalComplex (.up ℤ)).obj K) ≫
            DerivedCategory.Q.map
              ((NatIso.mapHomologicalComplex ordinary (.up ℤ)).hom.app K) := by
  let FC := US.ordinary.mapHomologicalComplex (.up ℤ)
  let GC := B.inverse.mapHomologicalComplex (.up ℤ)
  let HC := A.inverse.mapHomologicalComplex (.up ℤ)
  let IC := UT.ordinary.mapHomologicalComplex (.up ℤ)
  let l : DerivedCategory.Q ⋙ (US.derived ⋙ DB.inverse) ≅
      (FC ⋙ GC) ⋙ DerivedCategory.Q :=
    (Functor.associator _ _ _).symm ≪≫
      isoWhiskerRight US.factors DB.inverse ≪≫ Functor.associator _ _ _ ≪≫
        isoWhiskerLeft FC DB.inverseFactors ≪≫ (Functor.associator _ _ _).symm
  let r : DerivedCategory.Q ⋙ (DA.inverse ⋙ UT.derived) ≅
      (HC ⋙ IC) ⋙ DerivedCategory.Q :=
    (Functor.associator _ _ _).symm ≪≫
      isoWhiskerRight DA.inverseFactors UT.derived ≪≫ Functor.associator _ _ _ ≪≫
        isoWhiskerLeft HC UT.factors ≪≫ (Functor.associator _ _ _).symm
  let W := HomologicalComplex.quasiIso (strictEtaleCoefficientSystem S O ell) (.up ℤ)
  let : Localization.Lifting DerivedCategory.Q W
      ((FC ⋙ GC) ⋙ DerivedCategory.Q) (US.derived ⋙ DB.inverse) := ⟨l⟩
  let : Localization.Lifting DerivedCategory.Q W
      ((HC ⋙ IC) ⋙ DerivedCategory.Q) (DA.inverse ⋙ UT.derived) := ⟨r⟩
  let e : (FC ⋙ GC) ⋙ DerivedCategory.Q ≅ (HC ⋙ IC) ⋙ DerivedCategory.Q :=
    isoWhiskerRight (Functor.mapHomologicalComplexCompIso ordinary (.up ℤ)) DerivedCategory.Q
  let d : US.derived ⋙ DB.inverse ≅ DA.inverse ⋙ UT.derived :=
    Localization.liftNatIso DerivedCategory.Q W _ _
      (US.derived ⋙ DB.inverse) (DA.inverse ⋙ UT.derived) e
  refine ⟨d, ?_⟩
  intro K
  have hd : d.hom.app (DerivedCategory.Q.obj K) =
      l.hom.app K ≫ e.hom.app K ≫ r.inv.app K :=
    Localization.liftNatTrans_app DerivedCategory.Q W _ _
      (US.derived ⋙ DB.inverse) (DA.inverse ⋙ UT.derived) e.hom K
  have hc := congrArg (fun z ↦ z ≫ r.hom.app K) hd
  simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id] at hc
  dsimp only [l, r, e, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    associator_inv_app, associator_hom_app, isoWhiskerRight_hom, isoWhiskerLeft_hom,
    whiskerRight_app, whiskerLeft_app, Functor.comp_obj, FC, GC, HC, IC,
    Functor.mapHomologicalComplexCompIso] at hc
  simp only [Category.comp_id, Category.id_comp, Category.assoc] at hc
  exact hc

private theorem system_resolution
    {S : Scheme.{u}} {O : Type (u + 1)} [CommRing O] {ell : O}
    (K : CochainComplex (strictEtaleCoefficientSystem S O ell) ℤ) :
    ∃ (P : CochainComplex (strictEtaleCoefficientSystem S O ell) ℤ) (q : P ⟶ K),
      (∀ n,
        CochainComplex.IsKFlatIndependentCoefficients
          (R := coefficientQuotientSheaf (J := S.smallEtaleTopology) O ell n)
          (((coefficientEvaluation (J := S.smallEtaleTopology) (O := O) (ell := ell)
            n).mapHomologicalComplex (.up ℤ)).obj P) ∧
        ∀ i : ℤ, IsFlatOnSite (J := S.smallEtaleTopology)
          (R := coefficientQuotientSheaf (J := S.smallEtaleTopology) O ell n)
          (P.X i |>.level n)) ∧ QuasiIso q := by
  let E := coefficientSystemEquivalence (J := S.smallEtaleTopology) (O := O) (ell := ell)
  let e := E.mapHomologicalComplex (.up ℤ)
  obtain ⟨L, q, hL, hq⟩ := strictRingSystem_kFlatResolution
    (coefficientRings (J := S.smallEtaleTopology) (O := O) (ell := ell)) (e.functor.obj K)
  have : QuasiIso q := hq
  refine ⟨e.inverse.obj L, e.inverse.map q ≫ e.unitIso.inv.app K, ?_, ?_⟩
  · intro n
    exact hL n
  · have : QuasiIso (e.inverse.map q) := by
      change QuasiIso ((E.inverse.mapHomologicalComplex (.up ℤ)).map q)
      infer_instance
    infer_instance

section Evaluation
variable {O O' : Type (u + 1)} [CommRing O] [CommRing O'] {ell : O} {mu : O'}
    {phi : O →+* O'} {index : ℕ →o ℕ}
    {a : StrictEtaleCoefficientChange O O' ell mu phi index}
    {X Y : Scheme.{u}} {f : X ⟶ Y} {c : Compactification f}
    (SA : StrictEtaleCompactSupport O ell c) (SB : StrictEtaleCompactSupport O' mu c)
    (TX : StrictEtaleCoefficientTransport a X SA.PX SB.PX)
    (TZ : StrictEtaleCoefficientTransport a c.Z SA.PZ SB.PZ)
    (finite : ∀ n, StrictEtaleLevelInverseTransport TX TZ SA.openImage SB.openImage
      SA.openDerived.level SB.openDerived.level n)
    (square : StrictEtaleInverseTransport TX TZ SA.openImage SB.openImage
      SA.openDerived.system SB.openDerived.system)

private theorem ordinary_forward (n : ℕ) (M) :
    (coefficientEvaluation (J := X.smallEtaleTopology) (O := O') (ell := mu) n).map
        (square.val.1.hom.app M) ≫
      (TX.val.evaluation n).hom.app (SA.openImage.inverse.obj M) ≫
      (siteCoefficientTensor.{u + 1, u, u + 1} (a.sheaf X n)).map
        ((SA.openImage.inverseEvaluation (index n)).hom.app M) =
    (SB.openImage.inverseEvaluation n).hom.app (TZ.ordinary.obj M) ≫
      (SB.openImage.lift n).modules.map ((TZ.val.evaluation n).hom.app M) ≫
      (finite n).ordinary.hom.app (M.level (index n)) := by
  have h := ordinary_evaluation TX TZ SA.openImage SB.openImage
    SA.openDerived.level SB.openDerived.level finite square.val.1 square.property.1 n M
  have h' := congrArg (fun z ↦
    (coefficientEvaluation (J := X.smallEtaleTopology) (O := O') (ell := mu) n).map
      (square.val.1.hom.app M) ≫ z ≫
      (finite n).ordinary.hom.app (M.level (index n))) h
  simp only [Category.assoc, ← Functor.map_comp_assoc, Iso.hom_inv_id_app,
    Iso.inv_hom_id_app, CategoryTheory.Functor.map_id, Category.id_comp] at h'
  exact h'.symm

set_option maxHeartbeats 2000000 in
-- The representative comparison expands several nested evaluation functors.
private theorem evaluation_on_good (n : ℕ)
    (K : CochainComplex (strictEtaleCoefficientSystem c.Z O ell) ℤ)
    (hk : CochainComplex.IsKFlatIndependentCoefficients
      (R := coefficientQuotientSheaf (J := c.Z.smallEtaleTopology) O ell (index n))
      (((coefficientEvaluation (J := c.Z.smallEtaleTopology) (O := O) (ell := ell)
        (index n)).mapHomologicalComplex (.up ℤ)).obj K))
    (hflat : ∀ i : ℤ, IsFlatOnSite (J := c.Z.smallEtaleTopology)
      (R := coefficientQuotientSheaf (J := c.Z.smallEtaleTopology) O ell (index n))
      (K.X i |>.level (index n))) :
    (SB.PX.evaluation n).map (square.derived.hom.app (DerivedCategory.Q.obj K)) ≫
        (TX.derivedEvaluation n).hom.app
          (SA.openDerived.system.inverse.obj (DerivedCategory.Q.obj K)) ≫
        (TX.level n).derived.map
          ((SA.openDerived.inverseEvaluation (index n)).hom.app (DerivedCategory.Q.obj K)) =
      (SB.openDerived.inverseEvaluation n).hom.app (TZ.derived.obj (DerivedCategory.Q.obj K)) ≫
        (SB.openDerived.level n).inverse.map
          ((TZ.derivedEvaluation n).hom.app (DerivedCategory.Q.obj K)) ≫
        (finite n).derived.hom.app ((SA.PZ.evaluation (index n)).obj
          (DerivedCategory.Q.obj K)) := by
  let H := (SA.openImage.inverse.mapHomologicalComplex (.up ℤ)).obj K
  let k := ((coefficientEvaluation (J := c.Z.smallEtaleTopology) (O := O) (ell := ell)
    (index n)).mapHomologicalComplex (.up ℤ)).obj K
  let t := (TZ.ordinary.mapHomologicalComplex (.up ℤ)).obj K
  let j := ((SA.openImage.lift (index n)).modules.mapHomologicalComplex (.up ℤ)).obj k
  have : PreservesFiniteLimits (Scheme.etaleSetPullback c.i) :=
    (etaleSetInverseImage_exact c.i).2.2.1
  have hj := inverse_good (PV := SA.PX) (A := SA.openImage) (index n) k hk hflat
  have := (TX.level n).computes j hj.1
  apply (cancel_mono ((TX.level n).derived.map
      ((SA.openDerived.level (index n)).inverse.map
        ((SA.PZ.evaluationFactors (index n)).hom.app K)) ≫
    (TX.level n).derived.map ((SA.openDerived.level (index n)).inverseFactors.hom.app k) ≫
    (TX.level n).counit.app j)).1
  have hA := SA.openDerived.inverseEvaluation_rep (index n) K
  have hB := SB.openDerived.inverseEvaluation_rep n t
  have hX := TX.property.2.2.2 n H
  have hZ := TZ.property.2.2.2 n K
  have hS := square.property.2 K
  have hF := (finite n).representative k hk hflat
  have nX := (TX.derivedEvaluation n).hom.naturality
    (SA.openDerived.system.inverseFactors.hom.app K)
  have nB := (SB.openDerived.inverseEvaluation n).hom.naturality (TZ.factors.hom.app K)
  have nF := (finite n).derived.hom.naturality
    ((SA.PZ.evaluationFactors (index n)).hom.app K)
  have nC := (TX.level n).counit.naturality
    ((NatIso.mapHomologicalComplex (SA.openImage.inverseEvaluation (index n))
      (.up ℤ)).hom.app K)
  have nI := (SB.openDerived.level n).inverseFactors.hom.naturality
    ((NatIso.mapHomologicalComplex (TZ.val.evaluation n) (.up ℤ)).hom.app K)
  have nE := (SB.PX.evaluationFactors n).hom.naturality
    ((NatIso.mapHomologicalComplex square.val.1 (.up ℤ)).hom.app K)
  dsimp only [Functor.comp_map, Functor.comp_obj] at nX nB nF nC nI nE
  simp only [Category.assoc]
  -- First substitute the inverse-image computation on the A side.
  rw [← (TX.level n).derived.map_comp_assoc, ← (TX.level n).derived.map_comp_assoc]
  simp only [Category.assoc]
  rw [hA]
  simp only [Functor.map_comp, Category.assoc]
  erw [nC, ← reassoc_of% nX, reassoc_of% hX]
  -- On the B side use naturality of the finite comparison and its computation equation.
  erw [← reassoc_of% nF, hF]
  rw [← (SB.openDerived.level n).inverse.map_comp_assoc,
    ← (SB.openDerived.level n).inverse.map_comp_assoc]
  simp only [Category.assoc]
  rw [hZ]
  simp only [Functor.map_comp, Category.assoc]
  erw [← reassoc_of% nB, reassoc_of% nI, reassoc_of% hB]
  -- The common system computation cancels, leaving the ordinary component square.
  rw [← (SB.PX.evaluation n).map_comp_assoc,
    ← (SB.PX.evaluation n).map_comp_assoc]
  simp only [Category.assoc]
  erw [hS]
  simp only [Functor.map_comp, Category.assoc]
  erw [reassoc_of% nE]
  simp only [← Functor.map_comp]
  congr 4
  ext i : 1
  exact ordinary_forward SA SB TX TZ finite square n (K.X i)

end Evaluation

/-- The normalized inverse-image transport squares commute with evaluation.
This statement only constructs inverse-image comparisons; it involves no open mate,
no invertibility of an open-extension mate, and no quotient cube.
Source: Zheng, Construction 5.15 and Lemma 5.16.
(blueprint: lem-pur-strict-etale-open-inverse-evaluation).

Proof: write r = index. For an ordinary system M on c.Z, define the n-th
component of the ordinary comparison by this ordered sequence of isomorphisms:
evaluate B.inverse on TZ.ordinary(M); use B.inverseEvaluation to pass to the
finite B-lift; apply that lift to TZ.val.evaluation to expose scalar extension of
M.level(r n); apply (finite n).ordinary; apply scalar extension on X to the
inverse of A.inverseEvaluation; finally use the inverse of TX.val.evaluation.
Here A = SA.openImage and B = SB.openImage.

The finite comparisons are already normalized by their tensor-unit and
computation-counit equations. Their unit normalization makes the successor transition
squares commute: transposing both transition words under the scalar adjunction
reduces them to inverse image of the same semilinear transition, using the transport
transition equations and the geometric transition equations. The two transposes
are the same inverse image of the transition from M.level(r(n+1)) to M.level(r n),
followed by the n-th scalar insertion. Thus the component maps commute with
successors; the same calculation applies to their inverses. Their naturality
follows from naturality of all five component isomorphisms. The set-unit equation
reduces to (finite n).unit after substituting the two transport unit definitions.
The component maps therefore assemble an ordinary strict-system isomorphism. Exact
localization with the given factorization isomorphisms gives square and its
representative equation. Choose a strict-system resolution whose every selected
component has flat terms and independent K-flatness.
For the resolution, apply strictRingSystem_kFlatResolution after the ordinary
coefficient-system/StrictRingSystem equivalence and transport back; its evaluation
identifications preserve the flat-term independently K-flat component property.
The system and finite representative equations and the four evaluation representative
equations identify the two right-square evaluation words after their computation
counits. Those counits are invertible on this resolution; cancellation yields the
displayed equality. Naturality across the resolution isomorphism gives every derived
system object. The ordinary tensor-unit normalization and derived representative
equations are the fields of each finite record. -/
theorem nonempty_strictEtaleOpenInverseEvaluation
    {O O' : Type (u + 1)} [CommRing O] [CommRing O'] {ell : O} {mu : O'}
    {phi : O →+* O'} {index : ℕ →o ℕ}
    (a : StrictEtaleCoefficientChange O O' ell mu phi index)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (SA : StrictEtaleCompactSupport O ell c) (SB : StrictEtaleCompactSupport O' mu c)
    (TX : StrictEtaleCoefficientTransport a X SA.PX SB.PX)
    (TZ : StrictEtaleCoefficientTransport a c.Z SA.PZ SB.PZ)
    (finite : ∀ n, StrictEtaleLevelInverseTransport TX TZ SA.openImage SB.openImage
      SA.openDerived.level SB.openDerived.level n) :
    ∃ (square : StrictEtaleInverseTransport TX TZ SA.openImage SB.openImage
      SA.openDerived.system SB.openDerived.system),
      ∀ n M,
      (SB.PX.evaluation n).map (square.derived.inv.app M) ≫
          (SB.openDerived.inverseEvaluation n).hom.app (TZ.derived.obj M) ≫
          (SB.openDerived.level n).inverse.map ((TZ.derivedEvaluation n).hom.app M) =
        (TX.derivedEvaluation n).hom.app (SA.openDerived.system.inverse.obj M) ≫
          (TX.level n).derived.map
            ((SA.openDerived.inverseEvaluation (index n)).hom.app M) ≫
          (finite n).derived.inv.app ((SA.PZ.evaluation (index n)).obj M) := by
  obtain ⟨ordinary, hu⟩ := nonempty_strictEtaleOrdinaryInverseTransport TX TZ
    SA.openImage SB.openImage (fun n ↦ (finite n).ordinary)
    (finite_unit_forward TX TZ SA.openImage SB.openImage
      SA.openDerived.level SB.openDerived.level finite)
  obtain ⟨derived, hd⟩ := derived_square_exists TX TZ SA.openImage SB.openImage
    SA.openDerived.system SB.openDerived.system ordinary
  let square : StrictEtaleInverseTransport TX TZ SA.openImage SB.openImage
      SA.openDerived.system SB.openDerived.system := ⟨(ordinary, derived), hu, hd⟩
  refine ⟨square, ?_⟩
  intro n
  let α : (TZ.derived ⋙ SB.openDerived.system.inverse) ⋙ SB.PX.evaluation n ⟶
      SA.PZ.evaluation (index n) ⋙
        ((SA.openDerived.level (index n)).inverse ⋙ (TX.level n).derived) :=
    whiskerRight square.derived.hom (SB.PX.evaluation n) ≫
      whiskerLeft SA.openDerived.system.inverse (TX.derivedEvaluation n).hom ≫
      whiskerRight (SA.openDerived.inverseEvaluation (index n)).hom (TX.level n).derived
  let β : (TZ.derived ⋙ SB.openDerived.system.inverse) ⋙ SB.PX.evaluation n ⟶
      SA.PZ.evaluation (index n) ⋙
        ((SA.openDerived.level (index n)).inverse ⋙ (TX.level n).derived) :=
    whiskerLeft TZ.derived (SB.openDerived.inverseEvaluation n).hom ≫
      whiskerRight (TZ.derivedEvaluation n).hom (SB.openDerived.level n).inverse ≫
      whiskerLeft (SA.PZ.evaluation (index n)) (finite n).derived.hom
  have he : α = β := by
    ext M
    obtain ⟨P, q, hP, hq⟩ := system_resolution (DerivedCategory.Q.objPreimage M)
    have : QuasiIso q := hq
    let i : DerivedCategory.Q.obj P ≅ M :=
      asIso (DerivedCategory.Q.map q) ≪≫ DerivedCategory.Q.objObjPreimageIso M
    apply (cancel_epi (((TZ.derived ⋙ SB.openDerived.system.inverse) ⋙
      SB.PX.evaluation n).map i.hom)).1
    rw [α.naturality, β.naturality]
    have hp := evaluation_on_good SA SB TX TZ finite square n P
      (hP (index n)).1 (hP (index n)).2
    exact congrArg (fun z ↦ z ≫
      (SA.PZ.evaluation (index n) ⋙
        ((SA.openDerived.level (index n)).inverse ⋙ (TX.level n).derived)).map i.hom) hp
  intro M
  have h := NatTrans.congr_app he M
  change (SB.PX.evaluation n).map (square.derived.hom.app M) ≫
      (TX.derivedEvaluation n).hom.app (SA.openDerived.system.inverse.obj M) ≫
      (TX.level n).derived.map ((SA.openDerived.inverseEvaluation (index n)).hom.app M) =
    (SB.openDerived.inverseEvaluation n).hom.app (TZ.derived.obj M) ≫
      (SB.openDerived.level n).inverse.map ((TZ.derivedEvaluation n).hom.app M) ≫
      (finite n).derived.hom.app ((SA.PZ.evaluation (index n)).obj M) at h
  have h' := congrArg (fun z ↦ (SB.PX.evaluation n).map (square.derived.inv.app M) ≫ z ≫
    (finite n).derived.inv.app ((SA.PZ.evaluation (index n)).obj M)) h
  simp only [Category.assoc, ← Functor.map_comp_assoc, Iso.inv_hom_id_app,
    CategoryTheory.Functor.map_id, Category.id_comp, Iso.hom_inv_id_app] at h'
  erw [Category.comp_id] at h'
  exact h'.symm

end AlgebraicGeometry
