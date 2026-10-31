/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.StrictEtaleIsomorphicStageProjectionInterfaces
import all WeilConjectures.AlgebraicGeometry.StrictEtaleOpenProjectionFaces
import WeilConjectures.CategoryTheory.InverseImageScalarRestrictionComparison
import all WeilConjectures.AlgebraicGeometry.StrictEtaleFiniteOrdinaryInverseTransport
import WeilConjectures.AlgebraicGeometry.StrictEtaleOpenOrdinaryCalculation
import WeilConjectures.AlgebraicGeometry.StrictEtaleOpenInverseEvaluation
import WeilConjectures.AlgebraicGeometry.StrictEtaleLevelInverseQuotient
import WeilConjectures.CategoryTheory.DerivedCategory.DerivedMateComparison
import WeilConjectures.CategoryTheory.DerivedSquareIndependentUniverses
import WeilConjectures.AlgebraicGeometry.EtaleSetInverseImageExact
/-! Finite-free open projection face for strict étale systems. -/
@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor SheafOfModules
namespace AlgebraicGeometry
attribute [local instance 5000] strictEtaleSystemDerived strictEtaleLevelDerived
set_option maxHeartbeats 1000000 in
-- The normalized transport uses several derived-factorization comparisons.
private theorem exactFiniteInverse_with_scalarMate
    {O O' : Type (u + 1)} [CommRing O] [CommRing O'] {ell : O} {mu : O'}
    {phi : O →+* O'} {index : ℕ →o ℕ}
    (a : StrictEtaleCoefficientChange O O' ell mu phi index)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (SA : StrictEtaleCompactSupport O ell c) (SB : StrictEtaleCompactSupport O' mu c)
    (TX : StrictEtaleCoefficientTransport a X SA.PX SB.PX)
    (TZ : StrictEtaleCoefficientTransport a c.Z SA.PZ SB.PZ)
    (hTX : ∀ n, IsIso (TX.level n).counit)
    (hTZ : ∀ n, IsIso (TZ.level n).counit) (n : ℕ) :
    ∃ finite : StrictEtaleLevelInverseTransport TX TZ SA.openImage SB.openImage
        SA.openDerived.level SB.openDerived.level n,
      IsIso ((mateEquiv (TZ.level n).derivedAdj (TX.level n).derivedAdj
        (.mk _ _ _ _ finite.derived.inv)).natTrans) := by
  classical
  let : PreservesFiniteLimits (Scheme.etaleSetPullback c.i) :=
    (etaleSetInverseImage_exact c.i).2.2.1
  let az := siteCoefficientTensorAdj.{u + 1, u, u + 1} (a.sheaf c.Z n)
  let ax := siteCoefficientTensorAdj.{u + 1, u, u + 1} (a.sheaf X n)
  obtain ⟨ordinary, hu⟩ := inverseCoefficient_ordinary_exists a c.i SA.openImage
    SB.openImage n
  obtain ⟨ρ, hρ⟩ := SheafOfModules.InverseImageScalarRestriction.exists_comparison
    (SA.openImage.lift (index n)) (SB.openImage.lift n)
    (a.sheaf c.Z n) (a.sheaf X n)
    (constantRing_square a SA.openImage SB.openImage n)
  let θ := ρ.symm
  have hθ M :
      (coefficientUnderlying (J := X.smallEtaleTopology) O ell (index n)).map
          (θ.hom.app M) =
        (SA.openImage.lift (index n)).moduleUnderlying.hom.app
            ((SheafOfModules.restrictScalars ((sheafCompose c.Z.smallEtaleTopology
              (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
                (a.sheaf c.Z n))).obj M) ≫ (SB.openImage.lift n).moduleUnderlying.inv.app M := by
    apply (cancel_epi
      ((coefficientUnderlying (J := X.smallEtaleTopology) O ell (index n)).map
        (ρ.hom.app M))).1
    change _ ≫ (coefficientUnderlying (J := X.smallEtaleTopology) O ell (index n)).map
      (ρ.inv.app M) = _
    rw [← Functor.map_comp, Iso.hom_inv_id_app, CategoryTheory.Functor.map_id]
    rw [← Category.assoc, hρ, Iso.hom_inv_id_app]
    rfl
  have hordinary : ((mateEquiv az ax).symm (.mk _ _ _ _ θ.hom)).natTrans =
      ordinary.inv := by
    apply NatTrans.ext
    funext M
    apply (ax.homEquiv _ _).injective
    have hm := unit_mateEquiv_symm az ax (.mk _ _ _ _ θ.hom) M
    change (SA.openImage.lift (index n)).modules.map (az.unit.app M) ≫
        θ.hom.app ((siteCoefficientTensor (a.sheaf c.Z n)).obj M) =
      ax.unit.app ((SA.openImage.lift (index n)).modules.obj M) ≫
        (SheafOfModules.restrictScalars ((sheafCompose X.smallEtaleTopology
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map (a.sheaf X n))).map
            (((mateEquiv az ax).symm (.mk _ _ _ _ θ.hom)).natTrans.app M) at hm
    simp only [Adjunction.homEquiv_unit]
    rw [← hm]
    apply (coefficientUnderlying (J := X.smallEtaleTopology) O ell (index n)).map_injective
    simp only [Functor.map_comp, hθ]
    have hn := (SA.openImage.lift (index n)).moduleUnderlying.hom.naturality
      (az.unit.app M)
    dsimp only [Functor.comp_map] at hn
    erw [← Category.assoc, hn, Category.assoc]
    have hh := hu M
    have hz := insertionUnderlying a c.Z n M
    have hx := insertionUnderlying a X n ((SA.openImage.lift (index n)).modules.obj M)
    rw [hz, hx] at hh
    apply (cancel_mono ((SB.openImage.lift n).moduleUnderlying.hom.app
      ((siteCoefficientTensor (a.sheaf c.Z n)).obj M))).1
    simp only [Category.assoc, Iso.inv_hom_id_app]
    erw [Category.comp_id]
    exact hh.symm
  obtain ⟨θD, hθD⟩ := exists_derivedSquare_independentUniverses
    (SheafOfModules.restrictScalars ((sheafCompose c.Z.smallEtaleTopology
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map (a.sheaf c.Z n)))
    (SB.openImage.lift n).modules (SA.openImage.lift (index n)).modules
    (SheafOfModules.restrictScalars ((sheafCompose X.smallEtaleTopology
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map (a.sheaf X n)))
    (TZ.level n).restriction (SB.openDerived.level n).inverse
    (SA.openDerived.level (index n)).inverse (TX.level n).restriction
    (TZ.level n).restrictionFactors (SB.openDerived.level n).inverseFactors
    (SA.openDerived.level (index n)).inverseFactors (TX.level n).restrictionFactors θ
  let b := ((mateEquiv (TZ.level n).derivedAdj (TX.level n).derivedAdj).symm
    (.mk _ _ _ _ θD.hom)).natTrans
  have hb P :
      b.app (DerivedCategory.Q.obj P) ≫
          (SB.openDerived.level n).inverse.map ((TZ.level n).counit.app P) ≫
          (SB.openDerived.level n).inverseFactors.hom.app
            (((siteCoefficientTensor (a.sheaf c.Z n)).mapHomologicalComplex (.up ℤ)).obj P) =
        (TX.level n).derived.map
            ((SA.openDerived.level (index n)).inverseFactors.hom.app P) ≫
          (TX.level n).counit.app
            (((SA.openImage.lift (index n)).modules.mapHomologicalComplex (.up ℤ)).obj P) ≫
          DerivedCategory.Q.map
            ((NatIso.mapHomologicalComplex ordinary (.up ℤ)).inv.app P) := by
    apply derivedMate_comparison (az.mapHomologicalComplex (.up ℤ))
      (ax.mapHomologicalComplex (.up ℤ)) (TZ.level n).derivedAdj (TX.level n).derivedAdj
      (TZ.level n).counit (TX.level n).counit
      (TZ.level n).restrictionFactors (TX.level n).restrictionFactors
      (SA.openDerived.level (index n)).inverseFactors (SB.openDerived.level n).inverseFactors
      (TZ.level n).transpose (TX.level n).transpose
      (.mk _ _ _ _ (NatIso.mapHomologicalComplex θ (.up ℤ)).hom)
      (.mk _ _ _ _ θD.hom) hθD
      (NatIso.mapHomologicalComplex ordinary (.up ℤ)).inv
    intro K
    rw [Adjunction.homEquiv_unit]
    ext k : 1
    change ax.unit.app ((SA.openImage.lift (index n)).modules.obj (K.X k)) ≫
        (SheafOfModules.restrictScalars ((sheafCompose X.smallEtaleTopology
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map (a.sheaf X n))).map
            (ordinary.inv.app (K.X k)) =
      (SA.openImage.lift (index n)).modules.map (az.unit.app (K.X k)) ≫
        θ.hom.app ((siteCoefficientTensor (a.sheaf c.Z n)).obj (K.X k))
    have h := unit_mateEquiv_symm az ax (.mk _ _ _ _ θ.hom) (K.X k)
    change (SA.openImage.lift (index n)).modules.map (az.unit.app (K.X k)) ≫
        θ.hom.app ((siteCoefficientTensor (a.sheaf c.Z n)).obj (K.X k)) =
      ax.unit.app ((SA.openImage.lift (index n)).modules.obj (K.X k)) ≫
        (SheafOfModules.restrictScalars ((sheafCompose X.smallEtaleTopology
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map (a.sheaf X n))).map
            (((mateEquiv az ax).symm (.mk _ _ _ _ θ.hom)).natTrans.app (K.X k)) at h
    rw [hordinary] at h
    exact h.symm
  have hbi P : IsIso (b.app (DerivedCategory.Q.obj P)) := by
    have := hTX n
    have := hTZ n
    have : IsIso (b.app (DerivedCategory.Q.obj P) ≫
        (SB.openDerived.level n).inverse.map ((TZ.level n).counit.app P) ≫
        (SB.openDerived.level n).inverseFactors.hom.app
          (((siteCoefficientTensor (a.sheaf c.Z n)).mapHomologicalComplex (.up ℤ)).obj P)) := by
      rw [hb]
      infer_instance
    exact IsIso.of_isIso_comp_right _
      ((SB.openDerived.level n).inverse.map ((TZ.level n).counit.app P) ≫
        (SB.openDerived.level n).inverseFactors.hom.app
          (((siteCoefficientTensor (a.sheaf c.Z n)).mapHomologicalComplex (.up ℤ)).obj P))
  have hbiso : IsIso b := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro K
    let P := DerivedCategory.Q.objPreimage K
    let e := DerivedCategory.Q.objObjPreimageIso K
    have := hbi P
    have : IsIso ((b.app (DerivedCategory.Q.obj P)) ≫
        ((TZ.level n).derived ⋙ (SB.openDerived.level n).inverse).map e.hom) :=
      inferInstance
    have hn := b.naturality e.hom
    have : IsIso (((SA.openDerived.level (index n)).inverse ⋙
        (TX.level n).derived).map e.hom ≫ b.app K) := by
      rw [hn]
      infer_instance
    exact IsIso.of_isIso_comp_left
      (((SA.openDerived.level (index n)).inverse ⋙ (TX.level n).derived).map e.hom)
      (b.app K)
  let := hbiso
  let finite : StrictEtaleLevelInverseTransport TX TZ SA.openImage SB.openImage
      SA.openDerived.level SB.openDerived.level n :=
    { ordinary := ordinary
      derived := (asIso b).symm
      unit := hu
      representative := by
        intro K _ _
        apply (Iso.inv_comp_eq ((asIso b).app (DerivedCategory.Q.obj K))).2
        have hh := congrArg (fun z ↦ z ≫ DerivedCategory.Q.map
          ((NatIso.mapHomologicalComplex ordinary (.up ℤ)).hom.app K)) (hb K)
        simp only [Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_app] at hh
        erw [CategoryTheory.Functor.map_id, Category.comp_id] at hh
        exact hh.symm }
  refine ⟨finite, ?_⟩
  have he : (mateEquiv (TZ.level n).derivedAdj (TX.level n).derivedAdj
      (.mk _ _ _ _ finite.derived.inv)).natTrans = θD.hom :=
    congrArg TwoSquare.natTrans
      ((mateEquiv (TZ.level n).derivedAdj (TX.level n).derivedAdj).apply_symm_apply
        (.mk _ _ _ _ θD.hom))
  rw [he]
  infer_instance

private theorem openMate_isIso_of_scalarMate
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {L : A ⥤ B} {R : B ⥤ A} {L' : C ⥤ D} {R' : D ⥤ C}
    {F : A ⥤ C} {U : C ⥤ A} {G : B ⥤ D} {V : D ⥤ B}
    (a : L ⊣ R) (a' : L' ⊣ R') (af : F ⊣ U) (ag : G ⊣ V)
    (s : R ⋙ F ⟶ G ⋙ R')
    [IsIso ((mateEquiv ag af (.mk _ _ _ _ s)).natTrans)] :
    IsIso (((mateEquiv a a').symm (.mk _ _ _ _ s)).natTrans) := by
  let t := (mateEquiv ag af (.mk _ _ _ _ s)).natTrans
  have hi : IsIso ((conjugateEquiv (a.comp ag) (af.comp a')).symm t) := inferInstance
  have h := iterated_mateEquiv_conjugateEquiv_symm a a' af ag (.mk _ _ _ _ t)
  rw [(mateEquiv ag af).symm_apply_apply] at h
  change IsIso (((mateEquiv a a').symm (.mk _ _ _ _ s)).natTrans)
  rw [h]
  exact hi

set_option maxHeartbeats 1000000 in
-- The two mate cubes include several normalized system comparison maps.
/-- The exact-scalar open face used by the compact-support projection assembly.
Source: Zheng, Construction 5.15 and Lemma 5.22.
(blueprint: new-pur-etale-finite-free-open-projection-face).

Proof: the normalized restriction-of-scalars/inverse-image comparison is an
isomorphism. Its inverse scalar mate equals the ordinary tensor/inverse-image
comparison, by their tensor-unit normalization. Localize the restriction square
using the supplied factorization isomorphisms. The derived-mate representative
formula, together with hTX and hTZ, makes its inverse scalar mate invertible on
complex representatives and hence on every derived object. Its inverse supplies
the normalized finite inverse transports. Their scalar mates are the localized
restriction comparisons. The iterated-mates identity therefore makes their open
mates invertible, since conjugation preserves isomorphisms. Apply the existing
system inverse/evaluation and finite inverse/quotient equations to these transports.
The left-mate cube identity turns those equations into the two required open cubes,
using the defining mate equations for arbitrary QA and QB. The proved open-face
assembly detects the system mate's invertibility by level evaluation and returns
the asserted data. Empty opens and zero coefficient rings obey the same identities.
-/
theorem nonempty_strictEtaleFiniteFreeOpenProjectionFace
    {O O' : Type (u + 1)} [CommRing O] [CommRing O'] {ell : O} {mu : O'}
    {phi : O →+* O'} {index : ℕ →o ℕ}
    (a : StrictEtaleCoefficientChange O O' ell mu phi index)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (SA : StrictEtaleCompactSupport O ell c) (SB : StrictEtaleCompactSupport O' mu c)
    (TX : StrictEtaleCoefficientTransport a X SA.PX SB.PX)
    (TZ : StrictEtaleCoefficientTransport a c.Z SA.PZ SB.PZ)
    (qX : StrictEtaleTransportQuotient TX) (qZ : StrictEtaleTransportQuotient TZ)
    (hTX : ∀ n, IsIso (TX.level n).counit)
    (hTZ : ∀ n, IsIso (TZ.level n).counit) :
    ∃ (square : StrictEtaleInverseTransport TX TZ SA.openImage SB.openImage
        SA.openDerived.system SB.openDerived.system)
      (openComparison : SA.derivedOpen ⋙ TZ.derived ≅ TX.derived ⋙ SB.derivedOpen)
      (level : ∀ n, SA.levelDerivedOpen (index n) ⋙ (TZ.level n).derived ≅
        (TX.level n).derived ⋙ SB.levelDerivedOpen n),
      ((mateEquiv SA.derivedOpenAdjunction SB.derivedOpenAdjunction
          (.mk _ _ _ _ openComparison.inv)).natTrans = square.derived.inv) ∧
      (∀ n K,
        (TZ.derivedEvaluation n).hom.app (SA.derivedOpen.obj K) ≫
            (TZ.level n).derived.map ((SA.openDerivedEvaluation (index n)).hom.app K) ≫
            (level n).hom.app ((SA.PX.evaluation (index n)).obj K) =
          (SB.PZ.evaluation n).map (openComparison.hom.app K) ≫
            (SB.openDerivedEvaluation n).hom.app (TX.derived.obj K) ≫
            (SB.levelDerivedOpen n).map ((TX.derivedEvaluation n).hom.app K)) ∧
      (∀ (QA : StrictEtaleQuotientProjection SA) (QB : StrictEtaleQuotientProjection SB)
          {m n : ℕ} (h : n ≤ m) K,
        (SB.levelDerivedOpen n).map ((qX.derived h).hom.app K) ≫
            (QB.openProjection h).hom.app ((TX.level m).derived.obj K) ≫
            (SB.PZ.scalar h).derived.map ((level m).inv.app K) =
          (level n).inv.app ((SA.PX.scalar (index.monotone h)).derived.obj K) ≫
            (TZ.level n).derived.map ((QA.openProjection (index.monotone h)).hom.app K) ≫
            (qZ.derived h).hom.app ((SA.levelDerivedOpen (index m)).obj K)) := by
  classical
  choose finite hfinite using
    (fun n ↦ exactFiniteInverse_with_scalarMate a c SA SB TX TZ hTX hTZ n)
  obtain ⟨square, rightEval⟩ :=
    nonempty_strictEtaleOpenInverseEvaluation a c SA SB TX TZ finite
  let b := ((mateEquiv SA.derivedOpenAdjunction SB.derivedOpenAdjunction).symm
    (.mk _ _ _ _ square.derived.inv)).natTrans
  let bn n := ((mateEquiv (SA.levelDerivedOpenAdjunction (index n))
    (SB.levelDerivedOpenAdjunction n)).symm (.mk _ _ _ _ (finite n).derived.inv)).natTrans
  have hb : (mateEquiv SA.derivedOpenAdjunction SB.derivedOpenAdjunction
      (.mk _ _ _ _ b)).natTrans = square.derived.inv := by
    exact congrArg TwoSquare.natTrans
      ((mateEquiv SA.derivedOpenAdjunction SB.derivedOpenAdjunction).apply_symm_apply _)
  have hbn n : IsIso (bn n) := by
    have := hfinite n
    exact openMate_isIso_of_scalarMate (SA.levelDerivedOpenAdjunction (index n))
      (SB.levelDerivedOpenAdjunction n) (TX.level n).derivedAdj (TZ.level n).derivedAdj
      (finite n).derived.inv
  apply openProjectionFaces_of_mates a c SA SB TX TZ qX qZ square b hb bn hbn
  · intro n K
    have ht := openLeftMate_cube SA.derivedOpenAdjunction SB.derivedOpenAdjunction
      (SA.levelDerivedOpenAdjunction (index n)) (SB.levelDerivedOpenAdjunction n)
      (SA.PX.evaluation (index n)) (SA.PZ.evaluation (index n))
      (SB.PX.evaluation n) (SB.PZ.evaluation n)
      (TX.derivedEvaluation n) (TZ.derivedEvaluation n)
      square.derived.inv (finite n).derived.inv
      (SA.openDerivedEvaluation (index n)).inv (SB.openDerivedEvaluation n).inv
      (by simpa only [openDerivedEvaluation_mate] using rightEval n) K
    have ht' := congrArg (fun z ↦
      (SB.openDerivedEvaluation n).hom.app (TX.derived.obj K) ≫ z ≫
        (TZ.level n).derived.map ((SA.openDerivedEvaluation (index n)).hom.app K)) ht
    simp only [Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_app,
      Iso.hom_inv_id_app_assoc] at ht'
    erw [CategoryTheory.Functor.map_id, Category.comp_id] at ht'
    exact ht'
  · intro QA QB m n h K
    have ht := openLeftMate_cube
      (SA.levelDerivedOpenAdjunction (index m)) (SB.levelDerivedOpenAdjunction m)
      (SA.levelDerivedOpenAdjunction (index n)) (SB.levelDerivedOpenAdjunction n)
      (SA.PX.scalar (index.monotone h)).derived
      (SA.PZ.scalar (index.monotone h)).derived
      (SB.PX.scalar h).derived (SB.PZ.scalar h).derived
      (qX.derived h).symm (qZ.derived h).symm
      (finite m).derived.inv (finite n).derived.inv
      (QA.openProjection (index.monotone h)).hom (QB.openProjection h).hom
      (by simpa only [QA.open_mate, QB.open_mate, Iso.symm_hom, TwoSquare.natTrans]
        using strictEtaleLevelInverse_quotient a c SA SB TX TZ qX qZ finite h) K
    have ht' := congrArg (fun z ↦
      (SB.levelDerivedOpen n).map ((qX.derived h).hom.app K) ≫ z ≫
        (qZ.derived h).hom.app ((SA.levelDerivedOpen (index m)).obj K)) ht
    simp only [Iso.symm_hom, Category.assoc, ← Functor.map_comp_assoc, Iso.hom_inv_id_app,
      CategoryTheory.Functor.map_id, Category.id_comp, Iso.inv_hom_id_app] at ht'
    erw [Category.comp_id] at ht'
    exact ht'.symm

end AlgebraicGeometry
