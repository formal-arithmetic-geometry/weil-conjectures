/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.OrdinaryCompactificationCoherence
public import WeilConjectures.AlgebraicGeometry.MixedBaseChangeInput
public import WeilConjectures.AlgebraicGeometry.Scalar.ScalarExtensionFunctor
import WeilConjectures.AlgebraicGeometry.MixedBaseChangeOperations
public import WeilConjectures.AlgebraicGeometry.CoefficientCompatibility.EtaleProEtaleCompactScalarSquare
public import WeilConjectures.AlgebraicGeometry.CoefficientCompatibility.RecordedCompactScalarNormalization
public import WeilConjectures.AlgebraicGeometry.CoefficientCompatibility.RecordedOpenScalarNormalization
public import WeilConjectures.AlgebraicGeometry.CoefficientCompatibility.RecordedRestrictionNormalization
public import WeilConjectures.AlgebraicGeometry.Finite.Ring.FiniteRingConstructibleDerivedOrigin
public import WeilConjectures.AlgebraicGeometry.MixedCompactSupportScalar
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantOpenSquareExchange

/-!
# Scalar extension and chosen compact-support exchange

Source: latest blueprint, thm-pur-finite-reduction-of-purity.proof.md, Step 4,
base-change coherence; det-sp-reduction-compatibilities.proof.md, (3), compatibility
with b (blueprint: lem-pur-compact-scalar-base-change).

All operations use ordinary uncompleted constant-ring module derived categories on
small pro-etale sites. Both compactifications are independent of coefficients.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.ProEtale

section Geometry

variable (ℓ pchar : ℕ) [Fact ℓ.Prime] (hp : 0 < pchar) (hℓ : pchar ≠ ℓ)
  (k : Type u) [Field k] [CharP k pchar]
  {X Y X' Y' : Scheme.{u}}
  [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
  [X'.Over (Spec (.of k))] [Y'.Over (Spec (.of k))]
  [LocallyOfFiniteType (X ↘ Spec (.of k))]
  [QuasiCompact (X ↘ Spec (.of k))] [IsSeparated (X ↘ Spec (.of k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of k))]
  [QuasiCompact (Y ↘ Spec (.of k))] [IsSeparated (Y ↘ Spec (.of k))]
  [LocallyOfFiniteType (X' ↘ Spec (.of k))]
  [QuasiCompact (X' ↘ Spec (.of k))] [IsSeparated (X' ↘ Spec (.of k))]
  [LocallyOfFiniteType (Y' ↘ Spec (.of k))]
  [QuasiCompact (Y' ↘ Spec (.of k))] [IsSeparated (Y' ↘ Spec (.of k))]
  (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
  (c : Compactification f) [c.Z.Over (Spec (.of k))]
  [LocallyOfFiniteType (c.Z ↘ Spec (.of k))]
  [QuasiCompact (c.Z ↘ Spec (.of k))] [IsSeparated (c.Z ↘ Spec (.of k))]
  [c.i.IsOver (Spec (.of k))] [c.g.IsOver (Spec (.of k))]
  (h : X' ⟶ X) (f' : X' ⟶ Y') (g : Y' ⟶ Y)
  [h.IsOver (Spec (.of k))] [f'.IsOver (Spec (.of k))] [g.IsOver (Spec (.of k))]
  (sq : ChosenCartesianSquare h f' f g)

private theorem iso_square_forward
    {C : Type*} [Category C] {A B X Y : C} (e : A ≅ B) (t : X ≅ Y)
    (q : A ⟶ X) (r : B ⟶ Y) (h : e.inv ≫ q = r ≫ t.inv) :
    q ≫ t.hom = e.hom ≫ r := by
  apply (cancel_epi e.inv).mp
  simp only [Iso.inv_hom_id_assoc]
  rw [← Category.assoc, h]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

private theorem iso_square_backward
    {C : Type*} [Category C] {A B X Y : C} (e : A ≅ B) (t : X ≅ Y)
    (q : A ⟶ X) (r : B ⟶ Y) (h : e.hom ≫ r = q ≫ t.hom) :
    e.inv ≫ q = r ≫ t.inv := by
  apply (cancel_mono t.hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [← h]
  simp only [Iso.inv_hom_id_assoc]

private theorem paste_exchange_postcompose
    {C : Type*} [Category C] {A B P Q R T G H : C}
    {p : A ⟶ B} {z : B ⟶ Q} {l : Q ⟶ T}
    {e : B ⟶ P} {l' : P ⟶ R} {r' : R ⟶ T}
    {a : A ⟶ G} {b : G ⟶ H} {q : H ⟶ R}
    (hz : z ≫ l = e ≫ l' ≫ r') (he : p ≫ e ≫ l' = a ≫ b ≫ q) :
    p ≫ z ≫ l = a ≫ b ≫ q ≫ r' := by
  rw [hz, reassoc_of% he]

private theorem recorded_model_eq (A : Type u) [CommRing A] [Finite A]
    {Z Y : Scheme.{u}} (g : Z ⟶ Y) :
    directImagePresentation A g =
      isoWhiskerLeft (sfIntrinsicDerivedEquivalence Z A).functor (properOriginPushIso A g) ≪≫
        sfIntrinsicDerivedDirectImageComparison g A := by
  unfold directImagePresentation
  rw [directImageModel_eq]
  unfold openSquare_directImageModel properOriginPushIso
  rfl

private theorem support_model_eq (A : Type u) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :
    supportPresentation A c =
      isoWhiskerLeft (sfIntrinsicDerivedEquivalence X A).functor
        (ordinaryCompactificationModel A c) ≪≫
          FiniteCompactScalar.compactRealizationIso A c := by
  apply Iso.ext
  ext K
  rw [supportPresentation_hom_app, recorded_model_eq]
  have hn := (properOriginPushIso A c.g).hom.naturality
    ((FiniteCompactScalar.openRealizationIso A c.i).hom.app K)
  dsimp only [Functor.comp_obj] at hn
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, isoWhiskerLeft_hom,
    whiskerLeft_app, ordinaryCompactificationModel,
    FiniteCompactScalar.compactRealizationIso, isoWhiskerRight_hom,
    whiskerRight_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.comp_id]
  erw [← Category.assoc, hn]
  simp only [FiniteCompactScalar.openRealizationIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Category.assoc]
  erw [Category.id_comp]

private theorem recorded_scalar_square
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (K : DerivedCategory
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} (ULift.{u + 1, u} A)))) :
    (scalarExtensionFunctor φ Y).map ((supportPresentation A c).hom.app K) ≫
      (scalarPresentation φ Y).hom.app
        ((rightDerivedLowerShriekOfCompactification
          (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) c).obj K) ≫
      (sfIntrinsicDerivedEquivalence Y B).functor.map
        ((transportedRecordedReductionDirectImageComparison φ c
          (reductionDirectImageComparison φ c.i c.g)).app K) =
    (reductionDirectImageComparison φ c.i c.g).app
        ((sfIntrinsicDerivedEquivalence X A).functor.obj K) ≫
      (reductionCompactSupport B c.i c.g).map ((scalarPresentation φ X).hom.app K) ≫
      (supportPresentation B c).hom.app ((liftedScalarExtension φ X).obj K) := by
  let FF := (Functor.FullyFaithful.ofFullyFaithful
    (sfIntrinsicDerivedEquivalence Y B).functor).whiskeringRight
      (DerivedCategory
        (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} (ULift.{u + 1, u} A))))
  have he := congrArg (fun t ↦ t.app K) (FF.map_preimage
    (X := rightDerivedLowerShriekOfCompactification
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) c ⋙ liftedScalarExtension φ Y)
    (Y := liftedScalarExtension φ X ⋙ rightDerivedLowerShriekOfCompactification
      (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) c)
    (whiskerLeft (rightDerivedLowerShriekOfCompactification
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) c) (scalarPresentation φ Y).inv ≫
      whiskerRight (supportPresentation A c).inv (scalarExtensionFunctor φ Y) ≫
      whiskerLeft (sfIntrinsicDerivedEquivalence X A).functor
        (reductionDirectImageComparison φ c.i c.g) ≫
      whiskerRight (scalarPresentation φ X).hom (reductionCompactSupport B c.i c.g) ≫
      whiskerLeft (liftedScalarExtension φ X) (supportPresentation B c).hom))
  change (sfIntrinsicDerivedEquivalence Y B).functor.map
      ((transportedRecordedReductionDirectImageComparison φ c
        (reductionDirectImageComparison φ c.i c.g)).app K) = _ at he
  rw [he]
  simp only [NatTrans.comp_app, whiskerLeft_app, whiskerRight_app,
    Iso.hom_inv_id_app_assoc, ← Functor.map_comp_assoc, Iso.hom_inv_id_app]
  erw [(scalarExtensionFunctor φ Y).map_id, Category.id_comp]

private def recordedSiteIso (A : Type u) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (L : DerivedCategory.Plus
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1, u} A)))) :
    (reductionCompactSupport A c.i c.g).obj
        ((finiteCoefficientIntrinsicDerivedComparison X A).obj L.obj) ≅
      (finiteCoefficientIntrinsicDerivedComparison Y A).obj
        ((Etale.rightDerivedLowerShriekOfCompactification
          (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) c).obj L.obj) :=
  (ordinaryCompactificationModel A c).app _ ≪≫
    (FiniteCompactScalar.compactSiteIso A c L).symm

private theorem recordedSiteIso_hom (A : Type u) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (L : DerivedCategory.Plus
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1, u} A)))) :
    (recordedSiteIso A c L).hom =
      (reductionCompactSupport A c.i c.g).map
        ((FiniteCompactScalar.intrinsicSiteFunctorIso A X).hom.app L.obj) ≫
      (supportPresentation A c).hom.app
        ((comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A))
          X).mapDerivedCategory.obj L.obj) ≫
      (sfIntrinsicDerivedEquivalence Y A).functor.map
        ((compactSupportSiteComparison (ULift.{u + 1, u} A) c).hom.app L) ≫
      (FiniteCompactScalar.intrinsicSiteFunctorIso A Y).inv.app
        ((Etale.rightDerivedLowerShriekOfCompactification
          (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) c).obj L.obj) := by
  rw [support_model_eq]
  simp only [recordedSiteIso, FiniteCompactScalar.compactSiteIso,
    Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv,
    Iso.app_hom, Iso.app_inv, Functor.mapIso_inv, ObjectProperty.ι_obj,
    isoWhiskerLeft_hom, whiskerLeft_app, NatTrans.comp_app, Category.assoc]
  rw [← (ordinaryCompactificationModel A c).hom.naturality_assoc]

/-- Transport the fixed-module scalar/site square through the specified realization
coordinates. The inverse pairs at X and Y cancel by naturality. -/
private theorem recorded_site_scalar_square
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (L : DerivedCategory.Plus
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1, u} A))))
    (hLB : DerivedCategory.TStructure.t.plus ((Etale.scalarExtension (uliftRingHom φ) X).obj
      L.obj)) :
    (scalarExtensionFunctor φ Y).map ((recordedSiteIso A c L).hom) ≫
      (FiniteCompactScalar.siteScalarIso φ Y).hom.app
        ((Etale.rightDerivedLowerShriekOfCompactification
          (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) c).obj L.obj) ≫
      (finiteCoefficientIntrinsicDerivedComparison Y B).map
        ((Etale.compactScalarMap (uliftRingHom φ) c).app L.obj) =
    (reductionDirectImageComparison φ c.i c.g).app
        ((finiteCoefficientIntrinsicDerivedComparison X A).obj L.obj) ≫
      (reductionCompactSupport B c.i c.g).map
        ((FiniteCompactScalar.siteScalarIso φ X).hom.app L.obj) ≫
      (recordedSiteIso B c ⟨_, hLB⟩).hom := by
  let CA (T : Scheme.{u}) :=
    (comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) T).mapDerivedCategory
  let CB (T : Scheme.{u}) :=
    (comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) T).mapDerivedCategory
  let EA (T : Scheme.{u}) := (sfIntrinsicDerivedEquivalence T A).functor
  let EB (T : Scheme.{u}) := (sfIntrinsicDerivedEquivalence T B).functor
  let RA := reductionCompactSupport A c.i c.g
  let RB := reductionCompactSupport B c.i c.g
  let S := scalarExtensionFunctor φ Y
  let SX := scalarExtensionFunctor φ X
  let FB := rightDerivedLowerShriekOfCompactification
    (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) c
  let Lb : DerivedCategory.Plus
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1, u} B))) := ⟨_, hLB⟩
  let a := (compactSupportSiteComparison (ULift.{u + 1, u} A) c).app L
  let b := (compactSupportSiteComparison (ULift.{u + 1, u} B) c).app Lb
  let q := transportedRecordedReductionDirectImageComparison φ c
    (reductionDirectImageComparison φ c.i c.g)
  let v := (Etale.compactScalarMap (uliftRingHom φ) c).app L.obj
  let dx := (pbcComparisonReduction X (uliftRingHom φ)).hom.app L.obj
  let dy := (pbcComparisonReduction Y (uliftRingHom φ)).hom.app
    ((Etale.rightDerivedLowerShriekOfCompactification
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) c).obj L.obj)
  have hs := transportedCompactScalar_site_square φ c L hLB
  change (liftedScalarExtension φ Y).map a.inv ≫ q.app ((CA X).obj L.obj) ≫ FB.map dx =
    dy ≫ (CB Y).map v ≫ b.inv at hs
  have hs' : q.app ((CA X).obj L.obj) ≫ FB.map dx ≫ b.hom =
      (liftedScalarExtension φ Y).map a.hom ≫ dy ≫ (CB Y).map v := by
    simpa only [Category.assoc, Functor.mapIso_hom] using iso_square_forward
      ((liftedScalarExtension φ Y).mapIso a) b
      (q.app ((CA X).obj L.obj) ≫ FB.map dx) (dy ≫ (CB Y).map v)
      (by simpa only [Category.assoc, Functor.mapIso_inv, Functor.comp_obj,
        ObjectProperty.ι_obj, Lb] using hs)
  have hq := (reductionDirectImageComparison φ c.i c.g).naturality
    ((FiniteCompactScalar.intrinsicSiteFunctorIso A X).hom.app L.obj)
  have ht := (scalarPresentation φ Y).hom.naturality a.hom
  have hb := (supportPresentation B c).hom.naturality dx
  have hv := (FiniteCompactScalar.intrinsicSiteFunctorIso B Y).inv.naturality v
  dsimp only [Functor.comp_map] at hq ht hb hv
  have hp := recorded_scalar_square φ c ((CA X).obj L.obj)
  have he := congrArg ((EB Y).map) hs'
  simp only [Functor.map_comp] at he
  let ax := (FiniteCompactScalar.intrinsicSiteFunctorIso A X).app L.obj
  let ay := (FiniteCompactScalar.intrinsicSiteFunctorIso A Y).app
    ((Etale.rightDerivedLowerShriekOfCompactification
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) c).obj L.obj)
  let bx := (FiniteCompactScalar.intrinsicSiteFunctorIso B X).app Lb.obj
  let byIso := (FiniteCompactScalar.intrinsicSiteFunctorIso B Y).app
    ((Etale.scalarExtension (uliftRingHom φ) Y).obj
      ((Etale.rightDerivedLowerShriekOfCompactification
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) c).obj L.obj))
  let bz := (FiniteCompactScalar.intrinsicSiteFunctorIso B Y).app
    ((Etale.rightDerivedLowerShriekOfCompactification
      (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) c).obj Lb.obj)
  simp only [recordedSiteIso_hom, FiniteCompactScalar.siteScalarIso,
    ← scalarPresentation_eq, Iso.trans_hom, Iso.symm_hom,
    isoWhiskerLeft_hom, isoWhiskerRight_hom, whiskerLeft_app, whiskerRight_app,
    NatTrans.comp_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Functor.map_comp, Category.assoc]
  change S.map (RA.map ax.hom) ≫
      S.map ((supportPresentation A c).hom.app ((CA X).obj L.obj)) ≫
      S.map ((EA Y).map a.hom) ≫ S.map ay.inv ≫ S.map ay.hom ≫
      (scalarPresentation φ Y).hom.app
        ((CA Y).obj ((Etale.rightDerivedLowerShriekOfCompactification
          (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) c).obj L.obj)) ≫
      (EB Y).map dy ≫ byIso.inv ≫
      (finiteCoefficientIntrinsicDerivedComparison Y B).map v =
    (reductionDirectImageComparison φ c.i c.g).app
        ((finiteCoefficientIntrinsicDerivedComparison X A).obj L.obj) ≫
      RB.map (SX.map ax.hom) ≫
      RB.map ((scalarPresentation φ X).hom.app ((CA X).obj L.obj)) ≫
      RB.map ((EB X).map dx) ≫ RB.map bx.inv ≫ RB.map bx.hom ≫
      (supportPresentation B c).hom.app ((CB X).obj Lb.obj) ≫
      (EB Y).map b.hom ≫ bz.inv
  erw [(S.mapIso ay).inv_hom_id_assoc, (RB.mapIso bx).inv_hom_id_assoc]
  erw [← hv, reassoc_of% ht]
  erw [← reassoc_of% he, reassoc_of% hp, ← reassoc_of% hb, reassoc_of% hq]
  rfl

private theorem refinement_transport
    {C : Type*} [Category C] {Uc Vc Ud Vd Wc Wd Pc Pd Qc Qd : C}
    (ec : Uc ≅ Vc) (ed : Ud ≅ Vd) (cc : Wc ≅ Qc) (cd : Wd ≅ Qd)
    {rc : Vc ⟶ Wc} {rd : Vd ⟶ Wd} {δc : Uc ⟶ Pc} {δd : Ud ⟶ Pd}
    {βc : Pc ⟶ Qc} {βd : Pd ⟶ Qd} {t : Uc ⟶ Ud} {t' : Pc ⟶ Pd} {s : Qc ⟶ Qd}
    (hc : ec.hom ≫ rc = δc ≫ βc ≫ cc.inv)
    (hd : ed.hom ≫ rd = δd ≫ βd ≫ cd.inv)
    (hn : t ≫ δd = δc ≫ t') (hb : t' ≫ βd = βc ≫ s) :
    (ec.inv ≫ t ≫ ed.hom) ≫ rd = rc ≫ cc.hom ≫ s ≫ cd.inv := by
  apply (cancel_epi ec.hom).mp
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [hd, reassoc_of% hc, reassoc_of% hn, reassoc_of% hb]
  simp only [Iso.inv_hom_id_assoc]

private theorem recorded_origin_refinement
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c d : Compactification f)
    (L : DerivedCategory.Plus
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1, u} A))))
    (hLB : DerivedCategory.TStructure.t.plus ((Etale.scalarExtension (uliftRingHom φ) X).obj
      L.obj)) :
    (scalarExtensionFunctor φ Y).map
      ((recordedSiteIso A c L).hom ≫
        (finiteCoefficientIntrinsicDerivedComparison Y A).map
          ((Etale.rightDerivedLowerShriekOfCompactificationIso
            (ULift.{u + 1, u} A) c d).hom.app L.obj) ≫
        (recordedSiteIso A d L).inv) ≫
      (reductionDirectImageComparison φ d.i d.g).app
        ((finiteCoefficientIntrinsicDerivedComparison X A).obj L.obj) ≫
      (reductionCompactSupport B d.i d.g).map
        ((FiniteCompactScalar.siteScalarIso φ X).hom.app L.obj) =
    (reductionDirectImageComparison φ c.i c.g).app
        ((finiteCoefficientIntrinsicDerivedComparison X A).obj L.obj) ≫
      (reductionCompactSupport B c.i c.g).map
        ((FiniteCompactScalar.siteScalarIso φ X).hom.app L.obj) ≫
      (recordedSiteIso B c ⟨_, hLB⟩).hom ≫
      (finiteCoefficientIntrinsicDerivedComparison Y B).map
        ((Etale.rightDerivedLowerShriekOfCompactificationIso
          (ULift.{u + 1, u} B) c d).hom.app
            ((Etale.scalarExtension (uliftRingHom φ) X).obj L.obj)) ≫
      (recordedSiteIso B d ⟨_, hLB⟩).inv := by
  let LB : DerivedCategory.Plus
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1, u} B))) := ⟨_, hLB⟩
  have hs (e : Compactification f) :
      (scalarExtensionFunctor φ Y).map (recordedSiteIso A e L).inv ≫
        (reductionDirectImageComparison φ e.i e.g).app
          ((finiteCoefficientIntrinsicDerivedComparison X A).obj L.obj) ≫
        (reductionCompactSupport B e.i e.g).map
          ((FiniteCompactScalar.siteScalarIso φ X).hom.app L.obj) =
      (FiniteCompactScalar.siteScalarIso φ Y).hom.app
        ((Etale.rightDerivedLowerShriekOfCompactification
          (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) e).obj L.obj) ≫
        (finiteCoefficientIntrinsicDerivedComparison Y B).map
          ((Etale.compactScalarMap (uliftRingHom φ) e).app L.obj) ≫
        (recordedSiteIso B e LB).inv := by
    simpa only [Category.assoc, Functor.mapIso_inv] using iso_square_backward
      ((scalarExtensionFunctor φ Y).mapIso (recordedSiteIso A e L))
      (recordedSiteIso B e LB)
      ((reductionDirectImageComparison φ e.i e.g).app
          ((finiteCoefficientIntrinsicDerivedComparison X A).obj L.obj) ≫
        (reductionCompactSupport B e.i e.g).map
          ((FiniteCompactScalar.siteScalarIso φ X).hom.app L.obj))
      ((FiniteCompactScalar.siteScalarIso φ Y).hom.app
          ((Etale.rightDerivedLowerShriekOfCompactification
            (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) e).obj L.obj) ≫
        (finiteCoefficientIntrinsicDerivedComparison Y B).map
          ((Etale.compactScalarMap (uliftRingHom φ) e).app L.obj))
      (by simpa only [Category.assoc, Functor.mapIso_hom, LB] using
        recorded_site_scalar_square φ e L hLB)
  have he := (Etale.etaleCompactScalarCoherence (uliftRingHom φ) f c).2.2 d L ⟨LB, rfl⟩
  have hn := (FiniteCompactScalar.siteScalarIso φ Y).hom.naturality
    ((Etale.rightDerivedLowerShriekOfCompactificationIso
      (ULift.{u + 1, u} A) c d).hom.app L.obj)
  dsimp only [Functor.comp_map] at hn
  have hb := congrArg ((finiteCoefficientIntrinsicDerivedComparison Y B).map) he
  simp only [Functor.map_comp] at hb
  have ht := refinement_transport
    ((scalarExtensionFunctor φ Y).mapIso (recordedSiteIso A c L).symm)
    ((scalarExtensionFunctor φ Y).mapIso (recordedSiteIso A d L).symm)
    (recordedSiteIso B c LB) (recordedSiteIso B d LB)
    (hs c) (hs d) hn hb
  simpa only [Functor.map_comp, Category.assoc, Functor.mapIso_hom,
    Functor.mapIso_inv, Iso.symm_hom, Iso.symm_inv, scalarExtensionFunctor,
    scalarExtension, proEtaleRingDerivedExtension, pbcDerivedExtend,
    FiniteCompactScalar.scalarRingMap, LB, Functor.comp_obj] using ht

private theorem scalar_refinement_transport
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    (T : C ⥤ D) (S : E ⥤ F) (G G' : C ⥤ E) (H H' : D ⥤ F)
    (q : G ⋙ S ⟶ T ⋙ H) (q' : G' ⋙ S ⟶ T ⋙ H')
    {U K : C} {V : D} (e : U ≅ K) (t : T.obj U ≅ V)
    (a : G.obj U ⟶ G'.obj U) (b : H.obj V ⟶ H'.obj V)
    (h : S.map a ≫ q'.app U ≫ H'.map t.hom =
      q.app U ≫ H.map t.hom ≫ b) :
    S.map (G.map e.inv ≫ a ≫ G'.map e.hom) ≫ q'.app K =
      q.app K ≫ H.map (T.map e.inv ≫ t.hom) ≫ b ≫
        H'.map (t.inv ≫ T.map e.hom) := by
  have hr : S.map a ≫ q'.app U =
      q.app U ≫ H.map t.hom ≫ b ≫ H'.map t.inv := by
    apply (cancel_mono (H'.map t.hom)).mp
    simpa only [Category.assoc, ← H'.map_comp, t.inv_hom_id, H'.map_id,
      Category.comp_id] using h
  have hq := q.naturality e.inv
  have hq' := q'.naturality e.hom
  dsimp only [Functor.comp_map] at hq hq'
  simp only [Functor.map_comp, Category.assoc]
  rw [hq', reassoc_of% hr, reassoc_of% hq]

/-- Compute the common-refinement square at an etale origin and use its defining
normalization to identify the comparison on arbitrary intrinsic Dctf inputs. -/
private theorem ordinary_scalar_refinement
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c d : Compactification f)
    (N : spFiniteConstructibleTorCategory X A)
    (hS : spFiniteConstructibleTor X B ((scalarExtensionFunctor φ X).obj N.obj)) :
    (scalarExtensionFunctor φ Y).map
        ((ordinaryCompactificationComparison A c d).hom.app N) ≫
      (reductionDirectImageComparison φ d.i d.g).app N.obj =
    (reductionDirectImageComparison φ c.i c.g).app N.obj ≫
      (ordinaryCompactificationComparison B c d).hom.app ⟨_, hS⟩ := by
  classical
  let NS : spFiniteConstructibleTorCategory X B := ⟨_, hS⟩
  obtain ⟨G, ⟨eG⟩⟩ := ((finiteRing_constructibleDerived_origin X A).2.2.1 N.obj).mpr
    ⟨N.property.2.1, N.property.1⟩
  obtain ⟨lo, hi, _, hG⟩ := G.property.2
  let L : DerivedCategory.Plus
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1, u} A))) :=
    ⟨G.obj, lo, (DerivedCategory.isGE_iff G.obj lo).mpr
      (fun i hi ↦ hG i (Or.inl hi))⟩
  let GB := (Etale.scalarExtension (uliftRingHom φ) X).obj L.obj
  let eS : (finiteCoefficientIntrinsicDerivedComparison X B).obj GB ≅ NS.obj :=
    (FiniteCompactScalar.siteScalarIso φ X).symm.app L.obj ≪≫
      (scalarExtensionFunctor φ X).mapIso eG
  obtain ⟨a, b, _, hv⟩ := NS.property.1
  have hGB : DerivedCategory.TStructure.t.plus GB := by
    refine ⟨a, (DerivedCategory.isGE_iff GB a).mpr ?_⟩
    intro i hi
    apply ((finiteRing_constructibleDerived_origin X B).2.2.2 GB a b).mpr
      (fun j hj ↦ (hv j hj).of_iso
        ((DerivedCategory.homologyFunctor _ j).mapIso eS)) i (Or.inl hi)
  let LB : DerivedCategory.Plus
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1, u} B))) :=
    ⟨GB, hGB⟩
  have hA := (ordinaryCompactificationComparison_existsUnique A c d).exists.choose_spec N L eG
  have hB := (ordinaryCompactificationComparison_existsUnique B c d).exists.choose_spec NS LB eS
  change (ordinaryCompactificationComparison A c d).app N = _ at hA
  change (ordinaryCompactificationComparison B c d).app NS = _ at hB
  rw [← Iso.app_hom, hA, ← Iso.app_hom, hB]
  have hr := recorded_origin_refinement φ f c d L hGB
  have ht := scalar_refinement_transport
    (scalarExtensionFunctor φ X) (scalarExtensionFunctor φ Y)
    (reductionCompactSupport A c.i c.g) (reductionCompactSupport A d.i d.g)
    (reductionCompactSupport B c.i c.g) (reductionCompactSupport B d.i d.g)
    (reductionDirectImageComparison φ c.i c.g)
    (reductionDirectImageComparison φ d.i d.g)
    eG ((FiniteCompactScalar.siteScalarIso φ X).app L.obj)
    ((recordedSiteIso A c L).hom ≫
      (finiteCoefficientIntrinsicDerivedComparison Y A).map
        ((Etale.rightDerivedLowerShriekOfCompactificationIso
          (ULift.{u + 1, u} A) c d).hom.app L.obj) ≫
      (recordedSiteIso A d L).inv)
    ((recordedSiteIso B c LB).hom ≫
      (finiteCoefficientIntrinsicDerivedComparison Y B).map
        ((Etale.rightDerivedLowerShriekOfCompactificationIso
          (ULift.{u + 1, u} B) c d).hom.app GB) ≫
      (recordedSiteIso B d LB).inv) hr
  simpa only [ordinaryCompactificationAtOrigin, recordedSiteIso,
    Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv,
    Iso.app_hom, Iso.app_inv, Functor.mapIso_hom, Functor.mapIso_inv,
    Functor.map_comp, Category.assoc, eS, Iso.refl_hom, Iso.refl_inv,
    Category.id_comp, Category.comp_id] using ht

private theorem ordinary_comparison_naturality
    (A : Type u) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    {f : X ⟶ Y} [QuasiCompact f] (c d : Compactification f)
    (M N : spFiniteConstructibleTorCategory X A) (t : M.obj ⟶ N.obj) :
    (reductionCompactSupport A c.i c.g).map t ≫
        (ordinaryCompactificationComparison A c d).hom.app N =
      (ordinaryCompactificationComparison A c d).hom.app M ≫
        (reductionCompactSupport A d.i d.g).map t := by
  have hn := (ordinaryCompactificationComparison A c d).hom.naturality
    (show M ⟶ N from ObjectProperty.homMk t)
  change (reductionCompactSupport A c.i c.g).map t ≫
      (ordinaryCompactificationComparison A c d).hom.app N =
    (ordinaryCompactificationComparison A c d).hom.app M ≫
      (reductionCompactSupport A d.i d.g).map t at hn
  exact hn

private theorem mixed_scalar_forward
    {X' X Y' Y : Scheme.{u}} {h : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : ChosenCartesianSquare h f' f g)
    (c : Compactification f)
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (M : proEtaleDerivedCategory X A) :
    (proEtaleConstantRingDerivedPullback B g).map
        ((reductionDirectImageComparison φ c.i c.g).app M) ≫
      (mixedCompactSupportExchange B sq c).app ((scalarExtensionFunctor φ X).obj M) ≫
      (reductionCompactSupport B (mixedPullbackCompactification sq c).i
        (mixedPullbackCompactification sq c).g).map
        ((directImageScalarPullbackIso φ h).hom.app M) =
    (directImageScalarPullbackIso φ g).hom.app
        ((reductionCompactSupport A c.i c.g).obj M) ≫
      (scalarExtensionFunctor φ Y').map ((mixedCompactSupportExchange A sq c).app M) ≫
      (reductionDirectImageComparison φ (mixedPullbackCompactification sq c).i
        (mixedPullbackCompactification sq c).g).app
        ((proEtaleConstantRingDerivedPullback A h).obj M) := by
  simpa only [Category.assoc, Functor.mapIso_hom, Iso.app_hom] using iso_square_forward
    (C := proEtaleDerivedCategory Y' B)
    ((directImageScalarPullbackIso φ g).app ((reductionCompactSupport A c.i c.g).obj M))
    ((reductionCompactSupport B (mixedPullbackCompactification sq c).i
      (mixedPullbackCompactification sq c).g).mapIso ((directImageScalarPullbackIso φ h).app M))
    ((proEtaleConstantRingDerivedPullback B g).map
        ((reductionDirectImageComparison φ c.i c.g).app M) ≫
      (mixedCompactSupportExchange B sq c).app ((scalarExtensionFunctor φ X).obj M))
    ((scalarExtensionFunctor φ Y').map ((mixedCompactSupportExchange A sq c).app M) ≫
      (reductionDirectImageComparison φ (mixedPullbackCompactification sq c).i
        (mixedPullbackCompactification sq c).g).app
        ((proEtaleConstantRingDerivedPullback A h).obj M))
    (by simpa only [Category.assoc, Functor.mapIso_inv, Iso.app_inv] using
      mixedCompactSupportScalar sq c φ M)

/-- Regard the actual scalar-extended object as an object of Dctf, using the recorded
same-interval scalar preservation theorem. Only the membership proof is added.
Source: latest blueprint, finite reduction Step 2
(blueprint: lem-pur-compact-scalar-base-change). -/
def compactScalarObject (ℓ : ℕ) [Fact ℓ.Prime]
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (hA : ∃ n : ℕ, ∀ x : A, (ℓ ^ n) • x = 0)
    (hB : ∃ n : ℕ, ∀ x : B, (ℓ ^ n) • x = 0)
    (φ : A →+* B) (T : Scheme.{u}) (M : spFiniteConstructibleTorCategory T A) :
    spFiniteConstructibleTorCategory T B := by
  refine ⟨(scalarExtensionFunctor φ T).obj M.obj, ?_⟩
  obtain ⟨a, b, hab, hv⟩ := M.property.1
  have hf : Set.Finite {i : ℤ | ¬ IsZero
      ((DerivedCategory.homologyFunctor _ i).obj M.obj)} :=
    (Set.finite_Icc a b).subset (fun i hi ↦
      ⟨le_of_not_gt (fun h ↦ hi (hv i (Or.inl h))),
        le_of_not_gt (fun h ↦ hi (hv i (Or.inr h)))⟩)
  obtain ⟨r, s, ht⟩ := M.property.2.2
  obtain ⟨hb, hc, htor⟩ := scalarExtensionFunctor_preserves_constructible_tor
    ℓ hA hB φ T M.obj hf M.property.2.1 r s ht
  obtain ⟨lo, hlo⟩ := hb.bddBelow
  obtain ⟨hi, hhi⟩ := hb.bddAbove
  refine ⟨⟨min lo hi, max lo hi, min_le_max, ?_⟩, hc, r, s, htor⟩
  intro i hv
  by_contra hz
  rcases hv with hv | hv
  · exact (not_lt_of_ge (hlo hz)) (hv.trans_le (min_le_left _ _))
  · exact (not_lt_of_ge (hhi hz)) ((le_max_right _ _).trans_lt hv)

/-- Exact inverse image on these Dctf inputs, with its automatic membership certificate.
The existing input theorem imposes no smoothness condition on f.
Source: latest blueprint, finite reduction Step 4
(blueprint: lem-pur-compact-scalar-base-change). -/
def compactExchangePullObject (A : Type u) [CommRing A] [Finite A]
    (hA : ∃ n : ℕ, ∀ x : A, (ℓ ^ n) • x = 0)
    (M : spFiniteConstructibleTorCategory X A) : spFiniteConstructibleTorCategory X' A :=
  ⟨(proEtaleConstantRingDerivedPullback A h).obj M.obj,
    (mixedBaseChange_input ℓ pchar hp hℓ k f c h f' g sq A hA M.obj M.property).1⟩

/-- The specified proper/open exchange followed by the normalized comparison to the
independently chosen primed compactification. Source: latest blueprint finite reduction
Step 4 (blueprint: lem-pur-compact-scalar-base-change). -/
def compactChosenExchange (A : Type u) [CommRing A] [Finite A]
    (hA : ∃ n : ℕ, ∀ x : A, (ℓ ^ n) • x = 0)
    (d : Compactification f') (M : spFiniteConstructibleTorCategory X A) :
    (proEtaleConstantRingDerivedPullback A g).obj
        ((reductionCompactSupport A c.i c.g).obj M.obj) ⟶
      (reductionCompactSupport A d.i d.g).obj
        ((proEtaleConstantRingDerivedPullback A h).obj M.obj) := by
  letI : IsNoetherian X' := isNoetherian_of_locallyOfFiniteType (X' ↘ Spec (.of k))
  letI : IsNoetherian Y' := isNoetherian_of_locallyOfFiniteType (Y' ↘ Spec (.of k))
  letI : QuasiCompact f' := inferInstance
  exact (mixedCompactSupportExchange A sq c).app M.obj ≫
    (ordinaryCompactificationComparison A (mixedPullbackCompactification sq c) d).hom.app
      (compactExchangePullObject ℓ pchar hp hℓ k f c h f' g sq A hA M)

private def scalar_pullback_iso
    {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B)
    {T V : Scheme.{u}} (f : T ⟶ V) :
    scalarExtensionFunctor φ V ⋙ proEtaleConstantRingDerivedPullback B f ≅
      proEtaleConstantRingDerivedPullback A f ⋙ scalarExtensionFunctor φ T :=
  directImageScalarPullbackIso φ f

private def scalar_pullback_hom
    {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B)
    {T V : Scheme.{u}} (f : T ⟶ V) (M : proEtaleDerivedCategory V A) :
    (proEtaleConstantRingDerivedPullback B f).obj ((scalarExtensionFunctor φ V).obj M) ⟶
      (scalarExtensionFunctor φ T).obj ((proEtaleConstantRingDerivedPullback A f).obj M) :=
  (scalar_pullback_iso φ f).hom.app M

private theorem scalar_pullback_hom_eq
    {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B)
    {T V : Scheme.{u}} (f : T ⟶ V) (M : proEtaleDerivedCategory V A) :
    scalar_pullback_hom φ f M = (directImageScalarPullbackIso φ f).hom.app M := by rfl

private def raw_comparison (A : Type u) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    {f : X ⟶ Y} [QuasiCompact f] (c d : Compactification f)
    (M : proEtaleDerivedCategory X A) (hM : spFiniteConstructibleTor X A M) :
    (reductionCompactSupport A c.i c.g).obj M ⟶
      (reductionCompactSupport A d.i d.g).obj M :=
  (ordinaryCompactificationComparison A c d).hom.app ⟨M, hM⟩

private theorem raw_comparison_naturality (A : Type u) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    {f : X ⟶ Y} [QuasiCompact f] (c d : Compactification f)
    (M N : proEtaleDerivedCategory X A)
    (hM : spFiniteConstructibleTor X A M) (hN : spFiniteConstructibleTor X A N)
    (t : M ⟶ N) :
    (reductionCompactSupport A c.i c.g).map t ≫ raw_comparison A c d N hN =
      raw_comparison A c d M hM ≫ (reductionCompactSupport A d.i d.g).map t := by
  simpa only [raw_comparison] using
    ordinary_comparison_naturality A c d ⟨M, hM⟩ ⟨N, hN⟩ t

private def raw_chosen (A : Type u) [CommRing A] [Finite A]
    (hA : ∃ n : ℕ, ∀ x : A, (ℓ ^ n) • x = 0)
    (d : Compactification f') (M : proEtaleDerivedCategory X A)
    (hM : spFiniteConstructibleTor X A M) :
    (proEtaleConstantRingDerivedPullback A g).obj
        ((reductionCompactSupport A c.i c.g).obj M) ⟶
      (reductionCompactSupport A d.i d.g).obj
        ((proEtaleConstantRingDerivedPullback A h).obj M) := by
  let : IsNoetherian X' := isNoetherian_of_locallyOfFiniteType (X' ↘ Spec (.of k))
  let : IsNoetherian Y' := isNoetherian_of_locallyOfFiniteType (Y' ↘ Spec (.of k))
  let : QuasiCompact f' := inferInstance
  exact (mixedCompactSupportExchange A sq c).app M ≫
    raw_comparison A (mixedPullbackCompactification sq c) d
      ((proEtaleConstantRingDerivedPullback A h).obj M)
      (mixedBaseChange_input ℓ pchar hp hℓ k f c h f' g sq A hA M hM).1

private theorem raw_chosen_postcompose
    [IsNoetherian X'] [IsNoetherian Y'] [QuasiCompact f']
    (A : Type u) [CommRing A] [Finite A]
    (hA : ∃ n : ℕ, ∀ x : A, (ℓ ^ n) • x = 0)
    (d : Compactification f') (M : proEtaleDerivedCategory X A)
    (hM : spFiniteConstructibleTor X A M) (N : proEtaleDerivedCategory X' A)
    (hN : spFiniteConstructibleTor X' A N)
    (t : (proEtaleConstantRingDerivedPullback A h).obj M ⟶ N) :
    raw_chosen ℓ pchar hp hℓ k f c h f' g sq A hA d M hM ≫
        (reductionCompactSupport A d.i d.g).map t =
      (mixedCompactSupportExchange A sq c).app M ≫
        (reductionCompactSupport A (mixedPullbackCompactification sq c).i
          (mixedPullbackCompactification sq c).g).map t ≫
        raw_comparison A (mixedPullbackCompactification sq c) d N hN := by
  unfold raw_chosen
  rw [Category.assoc]
  exact congrArg (fun z ↦ (mixedCompactSupportExchange A sq c).app M ≫ z)
    (raw_comparison_naturality A (mixedPullbackCompactification sq c) d
      ((proEtaleConstantRingDerivedPullback A h).obj M) N
      (mixedBaseChange_input ℓ pchar hp hℓ k f c h f' g sq A hA M hM).1 hN t).symm

private theorem chosen_raw_eq (A : Type u) [CommRing A] [Finite A]
    (hA : ∃ n : ℕ, ∀ x : A, (ℓ ^ n) • x = 0) (d : Compactification f')
    (M : spFiniteConstructibleTorCategory X A) :
    compactChosenExchange ℓ pchar hp hℓ k f c h f' g sq A hA d M =
      raw_chosen ℓ pchar hp hℓ k f c h f' g sq A hA d M.obj M.property := by
  unfold compactChosenExchange raw_chosen raw_comparison
  rfl

private theorem raw_component_left
    (ℓ pchar : ℕ) [Fact ℓ.Prime] (hp : 0 < pchar) (hℓ : pchar ≠ ℓ)
    (k : Type u) [Field k] [CharP k pchar]
    {X Y X' Y' : Scheme.{u}}
    [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [X'.Over (Spec (.of k))] [Y'.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))] [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))]
    [QuasiCompact (Y ↘ Spec (.of k))] [IsSeparated (Y ↘ Spec (.of k))]
    [LocallyOfFiniteType (X' ↘ Spec (.of k))]
    [QuasiCompact (X' ↘ Spec (.of k))] [IsSeparated (X' ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y' ↘ Spec (.of k))]
    [QuasiCompact (Y' ↘ Spec (.of k))] [IsSeparated (Y' ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
    (c : Compactification f) [c.Z.Over (Spec (.of k))]
    [LocallyOfFiniteType (c.Z ↘ Spec (.of k))]
    [QuasiCompact (c.Z ↘ Spec (.of k))] [IsSeparated (c.Z ↘ Spec (.of k))]
    [c.i.IsOver (Spec (.of k))] [c.g.IsOver (Spec (.of k))]
    (h : X' ⟶ X) (f' : X' ⟶ Y') (g : Y' ⟶ Y)
    [h.IsOver (Spec (.of k))] [f'.IsOver (Spec (.of k))] [g.IsOver (Spec (.of k))]
    (sq : ChosenCartesianSquare h f' f g)
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (_hA : ∃ n : ℕ, ∀ x : A, (ℓ ^ n) • x = 0)
    (hB : ∃ n : ℕ, ∀ x : B, (ℓ ^ n) • x = 0)
    (φ : A →+* B) (d : Compactification f')
    (M : spFiniteConstructibleTorCategory X A)
    (hSM : spFiniteConstructibleTor X B ((scalarExtensionFunctor φ X).obj M.obj))
    (hSN : spFiniteConstructibleTor X' B ((scalarExtensionFunctor φ X').obj
      ((proEtaleConstantRingDerivedPullback A h).obj M.obj)))
    [IsNoetherian X'] [IsNoetherian Y'] [QuasiCompact f'] :
    (proEtaleConstantRingDerivedPullback B g).map
        ((reductionDirectImageComparison φ c.i c.g).app M.obj) ≫
      raw_chosen ℓ pchar hp hℓ k f c h f' g sq B hB d
        ((scalarExtensionFunctor φ X).obj M.obj) hSM ≫
      (reductionCompactSupport B d.i d.g).map
        (scalar_pullback_hom φ h M.obj) =
    scalar_pullback_hom φ g
        ((reductionCompactSupport A c.i c.g).obj M.obj) ≫
      (scalarExtensionFunctor φ Y').map ((mixedCompactSupportExchange A sq c).app M.obj) ≫
      (reductionDirectImageComparison φ (mixedPullbackCompactification sq c).i
        (mixedPullbackCompactification sq c).g).app
        ((proEtaleConstantRingDerivedPullback A h).obj M.obj) ≫
      raw_comparison B (mixedPullbackCompactification sq c) d
        ((scalarExtensionFunctor φ X').obj ((proEtaleConstantRingDerivedPullback A h).obj M.obj))
        hSN := by
  have hz := raw_chosen_postcompose ℓ pchar hp hℓ k f c h f' g sq B hB d
    ((scalarExtensionFunctor φ X).obj M.obj) hSM
    ((scalarExtensionFunctor φ X').obj ((proEtaleConstantRingDerivedPullback A h).obj M.obj))
    hSN (scalar_pullback_hom φ h M.obj)
  have he := mixed_scalar_forward sq c φ M.obj
  simp (config := { dsimp := false, implicitDefEqProofs := false }) only
    [← scalar_pullback_hom_eq] at he
  exact paste_exchange_postcompose hz he

private theorem native_scalar_left
    (ℓ pchar : ℕ) [Fact ℓ.Prime] (hp : 0 < pchar) (hℓ : pchar ≠ ℓ)
    (k : Type u) [Field k] [CharP k pchar]
    {X Y X' Y' : Scheme.{u}}
    [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [X'.Over (Spec (.of k))] [Y'.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))] [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))]
    [QuasiCompact (Y ↘ Spec (.of k))] [IsSeparated (Y ↘ Spec (.of k))]
    [LocallyOfFiniteType (X' ↘ Spec (.of k))]
    [QuasiCompact (X' ↘ Spec (.of k))] [IsSeparated (X' ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y' ↘ Spec (.of k))]
    [QuasiCompact (Y' ↘ Spec (.of k))] [IsSeparated (Y' ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
    (c : Compactification f) [c.Z.Over (Spec (.of k))]
    [LocallyOfFiniteType (c.Z ↘ Spec (.of k))]
    [QuasiCompact (c.Z ↘ Spec (.of k))] [IsSeparated (c.Z ↘ Spec (.of k))]
    [c.i.IsOver (Spec (.of k))] [c.g.IsOver (Spec (.of k))]
    (h : X' ⟶ X) (f' : X' ⟶ Y') (g : Y' ⟶ Y)
    [h.IsOver (Spec (.of k))] [f'.IsOver (Spec (.of k))] [g.IsOver (Spec (.of k))]
    (sq : ChosenCartesianSquare h f' f g)
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (hA : ∃ n : ℕ, ∀ x : A, (ℓ ^ n) • x = 0)
    (hB : ∃ n : ℕ, ∀ x : B, (ℓ ^ n) • x = 0)
    (φ : A →+* B) (d : Compactification f')
    (M : spFiniteConstructibleTorCategory X A)
    [IsNoetherian X'] [IsNoetherian Y'] [QuasiCompact f'] :
    (proEtaleConstantRingDerivedPullback B g).map
        ((reductionDirectImageComparison φ c.i c.g).app M.obj) ≫
      compactChosenExchange ℓ pchar hp hℓ k f c h f' g sq B hB d
        (compactScalarObject ℓ hA hB φ X M) ≫
      (reductionCompactSupport B d.i d.g).map
        ((directImageScalarPullbackIso φ h).hom.app M.obj) =
    (directImageScalarPullbackIso φ g).hom.app
        ((reductionCompactSupport A c.i c.g).obj M.obj) ≫
      (scalarExtensionFunctor φ Y').map ((mixedCompactSupportExchange A sq c).app M.obj) ≫
      (reductionDirectImageComparison φ (mixedPullbackCompactification sq c).i
        (mixedPullbackCompactification sq c).g).app
        ((proEtaleConstantRingDerivedPullback A h).obj M.obj) ≫
      (ordinaryCompactificationComparison B (mixedPullbackCompactification sq c) d).hom.app
        (compactScalarObject ℓ hA hB φ X'
          (compactExchangePullObject ℓ pchar hp hℓ k f c h f' g sq A hA M)) := by
  rw [chosen_raw_eq]
  simp only [← scalar_pullback_hom_eq]
  simpa only [raw_comparison, compactScalarObject, compactExchangePullObject, Functor.comp_obj]
    using raw_component_left ℓ pchar hp hℓ k f c h f' g sq hA hB φ d M
      (compactScalarObject ℓ hA hB φ X M).property
      (compactScalarObject ℓ hA hB φ X'
        (compactExchangePullObject ℓ pchar hp hℓ k f c h f' g sq A hA M)).property

private theorem native_scalar_right
    (ℓ pchar : ℕ) [Fact ℓ.Prime] (hp : 0 < pchar) (hℓ : pchar ≠ ℓ)
    (k : Type u) [Field k] [CharP k pchar]
    {X Y X' Y' : Scheme.{u}}
    [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [X'.Over (Spec (.of k))] [Y'.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))] [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))]
    [QuasiCompact (Y ↘ Spec (.of k))] [IsSeparated (Y ↘ Spec (.of k))]
    [LocallyOfFiniteType (X' ↘ Spec (.of k))]
    [QuasiCompact (X' ↘ Spec (.of k))] [IsSeparated (X' ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y' ↘ Spec (.of k))]
    [QuasiCompact (Y' ↘ Spec (.of k))] [IsSeparated (Y' ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
    (c : Compactification f) [c.Z.Over (Spec (.of k))]
    [LocallyOfFiniteType (c.Z ↘ Spec (.of k))]
    [QuasiCompact (c.Z ↘ Spec (.of k))] [IsSeparated (c.Z ↘ Spec (.of k))]
    [c.i.IsOver (Spec (.of k))] [c.g.IsOver (Spec (.of k))]
    (h : X' ⟶ X) (f' : X' ⟶ Y') (g : Y' ⟶ Y)
    [h.IsOver (Spec (.of k))] [f'.IsOver (Spec (.of k))] [g.IsOver (Spec (.of k))]
    (sq : ChosenCartesianSquare h f' f g)
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (hA : ∃ n : ℕ, ∀ x : A, (ℓ ^ n) • x = 0)
    (hB : ∃ n : ℕ, ∀ x : B, (ℓ ^ n) • x = 0)
    (φ : A →+* B) (d : Compactification f')
    (M : spFiniteConstructibleTorCategory X A)
    [IsNoetherian X'] [IsNoetherian Y'] [QuasiCompact f'] :
    (directImageScalarPullbackIso φ g).hom.app
        ((reductionCompactSupport A c.i c.g).obj M.obj) ≫
      (scalarExtensionFunctor φ Y').map
        (compactChosenExchange ℓ pchar hp hℓ k f c h f' g sq A hA d M) ≫
      (reductionDirectImageComparison φ d.i d.g).app
        ((proEtaleConstantRingDerivedPullback A h).obj M.obj) =
    (directImageScalarPullbackIso φ g).hom.app
        ((reductionCompactSupport A c.i c.g).obj M.obj) ≫
      (scalarExtensionFunctor φ Y').map ((mixedCompactSupportExchange A sq c).app M.obj) ≫
      (reductionDirectImageComparison φ (mixedPullbackCompactification sq c).i
        (mixedPullbackCompactification sq c).g).app
        ((proEtaleConstantRingDerivedPullback A h).obj M.obj) ≫
      (ordinaryCompactificationComparison B (mixedPullbackCompactification sq c) d).hom.app
        (compactScalarObject ℓ hA hB φ X'
          (compactExchangePullObject ℓ pchar hp hℓ k f c h f' g sq A hA M)) := by
  let : IsSeparated (f' ≫ Y' ↘ Spec (.of k)) := by
    rw [comp_over]
    infer_instance
  let : IsSeparated f' := IsSeparated.of_comp f' (Y' ↘ Spec (.of k))
  let : LocallyOfFiniteType (f' ≫ Y' ↘ Spec (.of k)) := by
    rw [comp_over]
    infer_instance
  let : LocallyOfFiniteType f' := locallyOfFiniteType_of_comp f' (Y' ↘ Spec (.of k))
  let cp := mixedPullbackCompactification sq c
  let N := compactExchangePullObject ℓ pchar hp hℓ k f c h f' g sq A hA M
  let NS := compactScalarObject ℓ hA hB φ X' N
  have hc : (scalarExtensionFunctor φ Y').map
      ((ordinaryCompactificationComparison A cp d).hom.app N) ≫
        (reductionDirectImageComparison φ d.i d.g).app N.obj =
      (reductionDirectImageComparison φ cp.i cp.g).app N.obj ≫
        (ordinaryCompactificationComparison B cp d).hom.app NS := by
    exact ordinary_scalar_refinement φ f' cp d N NS.property
  unfold compactChosenExchange
  dsimp only [compactScalarObject, compactExchangePullObject, cp, N, NS,
    Iso.app_hom, Functor.comp_obj, Functor.comp_map, scalarExtensionFunctor]
    at hc ⊢
  simp (config := { dsimp := false, implicitDefEqProofs := false }) only
    [Functor.map_comp, Category.assoc]
    at hc ⊢
  rw [hc]

/-- The coefficient/base-change square with the actual b, on every intrinsic Dctf input.
The source is g_B^* S_Y F_f,A M, and the target is F_f',B S_X' h_A^* M.
The two scalar/pullback maps have the forward lambda direction. All maps are natural
in M. No flatness or projective-dimension assumption is made on B over A.

Source: latest blueprint, thm-pur-finite-reduction-of-purity.proof.md Step 4;
det-sp-reduction-compatibilities.proof.md (3), compatibility with b
(blueprint: lem-pur-compact-scalar-base-change).

Proof: apply mixedCompactSupportScalar to the coefficient-independent pullback
compactification. Postcompose with the forward source lambda and cancel its inverse;
precompose with the target lambda to obtain the forward scalar/exchange cube.
For the independently chosen d, use a bounded etale origin of the pulled-back Dctf
object. The bound on its actual scalar extension reflects to the etale scalar
extension, so the normalized scalar/site square applies for both compactifications.
The recorded direct-image presentation is the proper-origin model followed by
intrinsic realization. Naturality identifies its support/site presentation with
ordinaryCompactificationModel followed by compactSiteIso inverse. Thus the published
scalar/site square transports to these exact recorded compact-support functors.
Paste its two instances with etale compact scalar coherence for the canonical
common-refinement comparison. Naturality transports the resulting scalar/refinement
square along the origin identification. The defining normalization of the ordinary
comparison identifies its two horizontal arrows on every Dctf input. Finally move
the forward source lambda through the B-comparison by naturality and paste the
pullback cube with this scalar/refinement square. Associativity yields the statement.
All membership witnesses add only proofs; the objects and the specified maps stay
unchanged. No scalar mate or non-flat coefficient map is inverted.
-/
theorem compactScalarBaseChange
    (ℓ pchar : ℕ) [Fact ℓ.Prime] (hp : 0 < pchar) (hℓ : pchar ≠ ℓ)
    (k : Type u) [Field k] [CharP k pchar]
    {X Y X' Y' : Scheme.{u}}
    [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [X'.Over (Spec (.of k))] [Y'.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))] [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))]
    [QuasiCompact (Y ↘ Spec (.of k))] [IsSeparated (Y ↘ Spec (.of k))]
    [LocallyOfFiniteType (X' ↘ Spec (.of k))]
    [QuasiCompact (X' ↘ Spec (.of k))] [IsSeparated (X' ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y' ↘ Spec (.of k))]
    [QuasiCompact (Y' ↘ Spec (.of k))] [IsSeparated (Y' ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
    (c : Compactification f) [c.Z.Over (Spec (.of k))]
    [LocallyOfFiniteType (c.Z ↘ Spec (.of k))]
    [QuasiCompact (c.Z ↘ Spec (.of k))] [IsSeparated (c.Z ↘ Spec (.of k))]
    [c.i.IsOver (Spec (.of k))] [c.g.IsOver (Spec (.of k))]
    (h : X' ⟶ X) (f' : X' ⟶ Y') (g : Y' ⟶ Y)
    [h.IsOver (Spec (.of k))] [f'.IsOver (Spec (.of k))] [g.IsOver (Spec (.of k))]
    (sq : ChosenCartesianSquare h f' f g)
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (hA : ∃ n : ℕ, ∀ x : A, (ℓ ^ n) • x = 0)
    (hB : ∃ n : ℕ, ∀ x : B, (ℓ ^ n) • x = 0)
    (φ : A →+* B) (d : Compactification f')
    (M : spFiniteConstructibleTorCategory X A) :
    (proEtaleConstantRingDerivedPullback B g).map
        ((reductionDirectImageComparison φ c.i c.g).app M.obj) ≫
      compactChosenExchange ℓ pchar hp hℓ k f c h f' g sq B hB d
        (compactScalarObject ℓ hA hB φ X M) ≫
      (reductionCompactSupport B d.i d.g).map
        ((directImageScalarPullbackIso φ h).hom.app M.obj) =
    (directImageScalarPullbackIso φ g).hom.app
        ((reductionCompactSupport A c.i c.g).obj M.obj) ≫
      (scalarExtensionFunctor φ Y').map
        (compactChosenExchange ℓ pchar hp hℓ k f c h f' g sq A hA d M) ≫
      (reductionDirectImageComparison φ d.i d.g).app
        ((proEtaleConstantRingDerivedPullback A h).obj M.obj) := by
  let : IsNoetherian X' := isNoetherian_of_locallyOfFiniteType (X' ↘ Spec (.of k))
  let : IsNoetherian Y' := isNoetherian_of_locallyOfFiniteType (Y' ↘ Spec (.of k))
  let : QuasiCompact f' := inferInstance
  exact (native_scalar_left ℓ pchar hp hℓ k f c h f' g sq hA hB φ d M).trans
    (native_scalar_right ℓ pchar hp hℓ k f c h f' g sq hA hB φ d M).symm

end Geometry

end AlgebraicGeometry.ProEtale
