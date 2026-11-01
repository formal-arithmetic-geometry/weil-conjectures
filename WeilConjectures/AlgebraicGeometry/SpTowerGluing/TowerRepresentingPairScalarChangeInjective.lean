/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerCalculus.CoefficientTowerShriekInterfaces
public import WeilConjectures.AlgebraicGeometry.Reduction.ReductionCtfFunctors
import all WeilConjectures.AlgebraicGeometry.Reduction.ReductionExceptionalRealization
import all WeilConjectures.AlgebraicGeometry.Reduction.ReductionExceptionalChart
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.OpenCover

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme SheafOfModules

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.SpTowerGluing

attribute [local irreducible] Functor.leftDerivedFunctor Functor.rightDerivedFunctor
  Functor.mapDerivedCategory
  AlgebraicGeometry.ProEtale.pbcFixedScalarExtension
  AlgebraicGeometry.Etale.upperStar AlgebraicGeometry.Etale.lowerStar
  AlgebraicGeometry.ProEtale.reductionSiteScalarIso
  AlgebraicGeometry.ProEtale.reductionSitePullbackIso
  AlgebraicGeometry.ProEtale.reductionSiteCompactSupportIso
  AlgebraicGeometry.ProEtale.reductionDirectImageComparison
  AlgebraicGeometry.ProEtale.reductionSite
  AlgebraicGeometry.Scheme.reductionDerivedChange
  AlgebraicGeometry.ProEtale.reductionEtaleChartRightIso
  AlgebraicGeometry.ProEtale.reductionEtaleChartScalarIso

-- The ordinary smooth local normal form, with the base-open affine space included in
-- the affine space over the full target (blueprint: sbc-thm-etale-local-normal-form).
private theorem smooth_coordinate_chart
    {V S : Scheme.{u}} [IsNoetherian V] [IsNoetherian S]
    (g : V ⟶ S) [IsSeparated g] (d : ℕ) [SmoothOfRelativeDimension d g] (x : V) :
    ∃ (W : V.Opens) (_ : x ∈ W) (e : W.toScheme ⟶ affineTraceTower S d),
      AlgebraicGeometry.Etale e ∧ IsSeparated e ∧ LocallyOfFiniteType e ∧
        QuasiCompact e ∧ W.ι ≫ g = e ≫ affineTraceProjection S d := by
  obtain ⟨T, W, hT, hW, _, hx, hWT, e₀, he₀, he₀g⟩ :=
    Smooth.exists_etale_to_affineSpace g d x
  have : IsAffine W.toScheme := hW
  have : AlgebraicGeometry.Etale e₀ := he₀
  have : IsOpenImmersion (AffineSpace.map (ULift.{u} (Fin d)) T.ι) :=
    MorphismProperty.of_isPullback
      (AffineSpace.isPullback_map (n := ULift.{u} (Fin d)) T.ι).flip
      (inferInstance : IsOpenImmersion T.ι)
  let a := e₀ ≫ AffineSpace.map (ULift.{u} (Fin d)) T.ι
  have ha : W.ι ≫ g = a ≫ (AffineSpace (ULift.{u} (Fin d)) S ↘ S) := by
    dsimp only [a]
    rw [Category.assoc, AffineSpace.map_over, ← Category.assoc, he₀g,
      Scheme.Hom.resLE_comp_ι]
  have : IsSeparated a := inferInstance
  let e := a ≫ (affineTraceAffineSpaceIso S d).inv
  have : AlgebraicGeometry.Etale e := inferInstance
  have : IsSeparated e := inferInstance
  have : LocallyOfFiniteType e := inferInstance
  have : QuasiCompact e := inferInstance
  refine ⟨W, hx, e, inferInstance, inferInstance, inferInstance, inferInstance, ?_⟩
  have hp : affineTraceToAffineSpace S d ≫
      (AffineSpace (ULift.{u} (Fin d)) S ↘ S) = affineTraceProjection S d :=
    AffineSpace.homOfVector_over _ _
  rw [ha, ← hp]
  change a ≫ _ = a ≫ (affineTraceAffineSpaceIso S d).inv ≫
    (affineTraceAffineSpaceIso S d).hom ≫ _
  rw [Iso.inv_hom_id_assoc]

-- The proof of reductionExceptional_chartEquation, with invertibility on Y supplied
-- directly instead of deduced from positive characteristic. All counit normalizations
-- and the scalar/site/pullback cube are the published ones.
private theorem scalar_chart_equation
    (ℓ : ℕ) [Fact ℓ.Prime] {X Z Y : Scheme.{u}}
    [IsNoetherian X] [IsNoetherian Y]
    (hunit : ∀ n : ℕ, IsUnit ((ℓ ^ n : ℕ) : Γ(Y, ⊤)))
    (d : ℕ) (j : X ⟶ Z) [IsOpenImmersion j] (p : Z ⟶ Y) [IsProper p]
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B)
    (hFA : ∀ M : spFiniteConstructibleTorCategory X A,
      spFiniteConstructibleTor Y A ((reductionCompactSupport A j p).obj M.obj))
    (hFB : ∀ M : spFiniteConstructibleTorCategory X B,
      spFiniteConstructibleTor Y B ((reductionCompactSupport B j p).obj M.obj))
    (hSX : ∀ M : spFiniteConstructibleTorCategory X A,
      spFiniteConstructibleTor X B ((scalarExtensionFunctor φ X).obj M.obj))
    (hSY : ∀ K : spFiniteConstructibleTorCategory Y A,
      spFiniteConstructibleTor Y B ((scalarExtensionFunctor φ Y).obj K.obj))
    (GA : spFiniteConstructibleTorCategory Y A ⥤ spFiniteConstructibleTorCategory X A)
    (GB : spFiniteConstructibleTorCategory Y B ⥤ spFiniteConstructibleTorCategory X B)
    (adjA : reductionCtfCompactSupport A j p hFA ⊣ GA)
    (adjB : reductionCtfCompactSupport B j p hFB ⊣ GB)
    (RA : ReductionExceptionalRealization A j p hFA GA adjA)
    (RB : ReductionExceptionalRealization B j p hFB GB adjB)
    (c : GA ⋙ reductionCtfScalar φ X hSX ⟶ reductionCtfScalar φ Y hSY ⋙ GB)
    (hb : ∀ K : spFiniteConstructibleTorCategory Y A,
      IsIso ((reductionDirectImageComparison φ j p).app (GA.obj K).obj))
    (hc : ∀ K : spFiniteConstructibleTorCategory Y A,
      (reductionCompactSupport B j p).map (c.app K).hom ≫
          (adjB.counit.app ((reductionCtfScalar φ Y hSY).obj K)).hom =
        @inv _ _ _ _ ((reductionDirectImageComparison φ j p).app (GA.obj K).obj)
            (hb K) ≫
          (scalarExtensionFunctor φ Y).map (adjA.counit.app K).hom) :
    ReductionExceptionalChartEquation ℓ φ j p d hFA hFB hSX hSY GA GB adjA adjB RA RB c := by
  classical
  let F := RA.origin ⋙ Etale.scalarExtension (RingHom.ulift.{u + 1, u + 1, u, u} φ) Y
  let H := reductionCtfScalar φ Y hSY ⋙ RB.origin
  have hF (K) : _root_.DerivedCategory.TStructure.t.plus (F.obj K) :=
    (AdjunctionTransfer.bounded_of_constructible _ Y _
      (AdjunctionTransfer.scalar_preserves_etale _ Y _
        ⟨(AdjunctionTransfer.boundedConstructible_iff _ Y _).2
          (RA.origin_ctf K).1, (RA.origin_ctf K).2⟩).1).1
  have hH (K) : _root_.DerivedCategory.TStructure.t.plus (H.obj K) :=
    (RB.origin_ctf ((reductionCtfScalar φ Y hSY).obj K)).1.1.1
  let Fp := ObjectProperty.lift _ F hF
  let Hp := ObjectProperty.lift _ H hH
  let S := DerivedCategory.Plus.ι ⋙ reductionSite B Y
  have : S.Full := site_plus_full B Y
  have : S.Faithful := site_plus_faithful B Y
  let e : Fp ⋙ S ≅ Hp ⋙ S :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerLeft RA.origin (reductionSiteScalarIso φ Y).symm ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight RA.originIso (scalarExtensionFunctor φ Y) ≪≫
      (Functor.isoWhiskerLeft (reductionCtfScalar φ Y hSY) RB.originIso).symm
  let op := Functor.fullyFaithfulCancelRight S e
  let o : F ≅ H := Functor.isoWhiskerRight op DerivedCategory.Plus.ι
  have ho (K : spFiniteConstructibleTorCategory Y A) :
      (reductionSite B Y).map (o.hom.app K) ≫
          RB.originIso.hom.app ((reductionCtfScalar φ Y hSY).obj K) =
        (reductionSiteScalarIso φ Y).inv.app (RA.origin.obj K) ≫
          (scalarExtensionFunctor φ Y).map (RA.originIso.hom.app K) := by
    change S.map (op.hom.app K) ≫ _ = _
    dsimp only [op]
    rw [Functor.fullyFaithfulCancelRight_hom_app, Functor.map_preimage]
    simp only [ObjectProperty.ι, reductionCtfScalar, ObjectProperty.lift, Functor.comp_obj,
      inducedFunctor_obj, Functor.comp_map, inducedFunctor_map, Iso.trans_hom, Iso.symm_hom,
      Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_inv,
      NatTrans.comp_app, Functor.associator_inv_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app, Category.id_comp, Category.assoc, Iso.inv_hom_id_app,
      Category.comp_id, e]
    exact Category.id_comp _
  refine ⟨o, ho, ?_⟩
  intro n hnA hnB
  have hunit := hunit n
  refine ⟨hunit, ?_⟩
  intro MA MB tA DA tB DB hX hY U hU i hi e hee hse hlfe hqce he K
  let KB := (reductionCtfScalar φ Y hSY).obj K
  let L := RA.origin.obj K
  let LB := RB.origin.obj KB
  let m := reductionExceptionalComponent φ X Y hSX hSY GA GB c K
  obtain ⟨q, hq⟩ := (site_map_bijective B X
    ((Etale.scalarExtension (RingHom.ulift.{u + 1, u + 1, u, u} φ) X).obj
      (RA.right.obj L)) (RB.right.obj LB) (RB.right_plus KB)).2
    ((reductionSiteScalarIso φ X).inv.app (RA.right.obj L) ≫
      (scalarExtensionFunctor φ X).map (RA.rightIso.inv.app K) ≫
      m ≫ RB.rightIso.hom.app KB)
  have cq := reductionExceptional_counit_descent φ j p hFA hFB GA GB adjA adjB RA RB
    K KB (𝟙 _) (o.hom.app K)
    (by
      change _ = _ ≫ _ ≫ 𝟙 _
      rw [Category.comp_id]
      exact ho K)
    m (hb K) (by
      change _ = _ ≫ _ ≫ 𝟙 _
      rw [Category.comp_id]
      exact hc K)
    q hq
  let cf : Compactification (j ≫ p) :=
    ⟨Z, p, j, rfl, inferInstance, inferInstance⟩
  let rA := (reductionEtaleChartRightIso (ULift.{u + 1, u} A) MA (j ≫ p) i d e he cf
    RA.right RA.adjunction (ℓ ^ n) hnA tA DA hunit).app L
  let rB := (reductionEtaleChartRightIso (ULift.{u + 1, u} B) MB (j ≫ p) i d e he cf
    RB.right RB.adjunction (ℓ ^ n) hnB tB DB hunit).app LB
  let v := (reductionEtaleChartScalarIso (RingHom.ulift.{u + 1, u + 1, u, u} φ)
    (ℓ ^ n) hnA hnB hunit d e L).hom ≫
      (Etale.affineTraceRight (ULift.{u + 1, u} B) (ℓ ^ n) hnB Y d ⋙
        Etale.ordinaryFinitePullback (ULift.{u + 1, u} B) e).map (o.hom.app K)
  have chart := reductionExceptional_ordinary_chart
    (RingHom.ulift.{u + 1, u + 1, u, u} φ) (ℓ ^ n)
    (pow_pos (Fact.out : ℓ.Prime).pos n) hnA hnB (j ≫ p) i d e he cf MA MB
    tA DA tB DB hunit RA.right RB.right RA.adjunction RB.adjunction
    L (RA.origin_ctf K) LB (o.hom.app K) q cq
  have h := transfer_chart
    (reductionSite A X) (reductionSite A U) (reductionSite B X) (reductionSite B U)
    (Etale.scalarExtension (RingHom.ulift.{u + 1, u + 1, u, u} φ) X)
    (Etale.scalarExtension (RingHom.ulift.{u + 1, u + 1, u, u} φ) U)
    (scalarExtensionFunctor φ X) (scalarExtensionFunctor φ U)
    (Etale.ordinaryFinitePullback (ULift.{u + 1, u} A) i)
    (Etale.ordinaryFinitePullback (ULift.{u + 1, u} B) i)
    (proEtaleConstantRingDerivedPullback A i) (proEtaleConstantRingDerivedPullback B i)
    (reductionSiteScalarIso φ X) (reductionSiteScalarIso φ U)
    (reductionSitePullbackIso A i) (reductionSitePullbackIso B i)
    (directImageScalarPullbackIso φ i)
    (Etale.scalarPullbackIso (RingHom.ulift.{u + 1, u + 1, u, u} φ) i)
    (RA.rightIso.app K) (RB.rightIso.app KB) m q rA rB v hq
    (reductionSite_scalar_pullback φ i (RA.right.obj L)) chart
  simpa only [reductionIntrinsicChartIso, Iso.trans_hom, Functor.mapIso_hom,
    Iso.app_hom, Functor.map_comp, Functor.comp_obj, ObjectProperty.ι_obj,
    scalarExtensionFunctor, scalarExtension, directImageScalarExtension,
    Category.assoc, cf, rA, rB, v, L, LB, KB, m] using h


-- The proof of reductionExceptional_components_isIso, using the ordinary point-indexed
-- smooth chart cover. No admissible-cover condition or characteristic is required for
-- the open-cover isomorphism-detection argument.
private theorem scalar_components_isIso
    (ℓ : ℕ) [Fact ℓ.Prime] {X Z Y : Scheme.{u}}
    [IsNoetherian X] [IsNoetherian Y]
    (f : X ⟶ Y) [IsSeparated f] (d : ℕ) [SmoothOfRelativeDimension d f]
    (j : X ⟶ Z) [IsOpenImmersion j] (p : Z ⟶ Y) [IsProper p] (hf : j ≫ p = f)
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (hA : ∃ n : ℕ, ∀ x : A, (ℓ ^ n) • x = 0)
    (hB : ∃ n : ℕ, ∀ x : B, (ℓ ^ n) • x = 0) (φ : A →+* B)
    (hFA : ∀ M : spFiniteConstructibleTorCategory X A,
      spFiniteConstructibleTor Y A ((reductionCompactSupport A j p).obj M.obj))
    (hFB : ∀ M : spFiniteConstructibleTorCategory X B,
      spFiniteConstructibleTor Y B ((reductionCompactSupport B j p).obj M.obj))
    (hSX : ∀ M : spFiniteConstructibleTorCategory X A,
      spFiniteConstructibleTor X B ((scalarExtensionFunctor φ X).obj M.obj))
    (hSY : ∀ K : spFiniteConstructibleTorCategory Y A,
      spFiniteConstructibleTor Y B ((scalarExtensionFunctor φ Y).obj K.obj))
    (GA : spFiniteConstructibleTorCategory Y A ⥤ spFiniteConstructibleTorCategory X A)
    (GB : spFiniteConstructibleTorCategory Y B ⥤ spFiniteConstructibleTorCategory X B)
    (adjA : reductionCtfCompactSupport A j p hFA ⊣ GA)
    (adjB : reductionCtfCompactSupport B j p hFB ⊣ GB)
    (RA : ReductionExceptionalRealization A j p hFA GA adjA)
    (RB : ReductionExceptionalRealization B j p hFB GB adjB)
    (c : GA ⋙ reductionCtfScalar φ X hSX ⟶ reductionCtfScalar φ Y hSY ⋙ GB)
    (hchart : ReductionExceptionalChartEquation ℓ φ j p d hFA hFB hSX hSY GA GB adjA adjB RA RB c) :
    ∀ K : spFiniteConstructibleTorCategory Y A, IsIso (c.app K)  := by
  classical
  intro K
  obtain ⟨r, hr⟩ := hA
  obtain ⟨s, hs⟩ := hB
  let n := r + s
  have hnA : ((ℓ ^ n : ℕ) : ULift.{u + 1, u} A) = 0 := by
    apply ULift.ext
    change ((ℓ ^ (r + s) : ℕ) : A) = 0
    rw [pow_add, Nat.cast_mul]
    have hz : ((ℓ ^ r : ℕ) : A) = 0 := by
      simpa only [nsmul_eq_mul, mul_one] using hr 1
    rw [hz, zero_mul]
  have hnB : ((ℓ ^ n : ℕ) : ULift.{u + 1, u} B) = 0 := by
    apply ULift.ext
    change ((ℓ ^ (r + s) : ℕ) : B) = 0
    rw [pow_add, Nat.cast_mul]
    have hz : ((ℓ ^ s : ℕ) : B) = 0 := by
      simpa only [nsmul_eq_mul, mul_one] using hs 1
    rw [hz, mul_zero]
  obtain ⟨o, ho, hchart⟩ := hchart
  obtain ⟨hY, hchart⟩ := hchart n hnA hnB
  obtain ⟨MA⟩ := Etale.nonempty_etaleCompactSupportNormalization (ULift.{u + 1, u} A)
  obtain ⟨MB⟩ := Etale.nonempty_etaleCompactSupportNormalization (ULift.{u + 1, u} B)
  obtain ⟨tA, DA, _⟩ := Etale.exists_ordinaryFiniteP1Adjunction (ℓ ^ n)
    (pow_pos (Fact.out : ℓ.Prime).pos n) (ULift.{u + 1, u} A) hnA
  obtain ⟨tB, DB, _⟩ := Etale.exists_ordinaryFiniteP1Adjunction (ℓ ^ n)
    (pow_pos (Fact.out : ℓ.Prime).pos n) (ULift.{u + 1, u} B) hnB
  choose U hx e he hs hft hqc hg using smooth_coordinate_chart f d
  have hcover : ∀ x : X, ∃ a, x ∈ U a := fun x ↦ ⟨x, hx x⟩
  have hlocal (a : X) :
      IsIso ((proEtaleConstantRingDerivedPullback B (U a).ι).map (c.app K).hom) := by
    have : IsLocallyNoetherian (U a).toScheme := inferInstance
    have : TopologicalSpace.NoetherianSpace (U a).toScheme :=
      (U a).ι.isOpenEmbedding.isInducing.noetherianSpace
    have : CompactSpace (U a).toScheme := TopologicalSpace.NoetherianSpace.compactSpace _
    have : IsNoetherian (U a).toScheme := ⟨⟩
    have : IsSeparated (e a) := hs a
    have : AlgebraicGeometry.Etale (e a) := he a
    have : LocallyOfFiniteType (e a) := hft a
    have : QuasiCompact (e a) := hqc a
    let v := e a
    have hv : (U a).ι ≫ (j ≫ p) = v ≫ affineTraceProjection Y d := by
      rw [hf]
      exact hg a
    have h := hchart MA MB tA DA tB DB inferInstance inferInstance
      (U a).toScheme (U a).ι v hv K
    have : IsIso ((directImageScalarPullbackIso φ (U a).ι).inv.app (GA.obj K).obj ≫
        (proEtaleConstantRingDerivedPullback B (U a).ι).map (c.app K).hom ≫
        (reductionIntrinsicChartIso B j p hFB GB adjB RB MB (U a).ι d v hv
          (ℓ ^ n) hnB tB DB hY ((reductionCtfScalar φ Y hSY).obj K)).hom) := by
      change IsIso ((directImageScalarPullbackIso φ (U a).ι).inv.app
        (GA.obj K).obj ≫ (proEtaleConstantRingDerivedPullback B (U a).ι).map
          (reductionExceptionalComponent φ X Y hSX hSY GA GB c K) ≫ _)
      rw [h]
      infer_instance
    have := IsIso.of_isIso_comp_left
      ((directImageScalarPullbackIso φ (U a).ι).inv.app (GA.obj K).obj)
      ((proEtaleConstantRingDerivedPullback B (U a).ι).map (c.app K).hom ≫
        (reductionIntrinsicChartIso B j p hFB GB adjB RB MB (U a).ι d v hv
          (ℓ ^ n) hnB tB DB hY ((reductionCtfScalar φ Y hSY).obj K)).hom)
    exact IsIso.of_isIso_comp_right _
      (reductionIntrinsicChartIso B j p hFB GB adjB RB MB (U a).ι d v hv
        (ℓ ^ n) hnB tB DB hY ((reductionCtfScalar φ Y hSY).obj K)).hom
  let E := sfIntrinsicDerivedEquivalence X B
  let g := E.inverse.map (c.app K).hom
  have hfixed (a : X) : IsIso ((sfFixedDerivedPullback B (U a).ι).map g) := by
    have hi : IsIso ((proEtaleConstantRingDerivedPullback B (U a).ι).map
        (E.functor.map g)) := by
      have := hlocal a
      exact (NatIso.isIso_map_iff
        (Functor.isoWhiskerRight E.counitIso
          (proEtaleConstantRingDerivedPullback B (U a).ι)) (c.app K).hom).mpr
          (by simpa only [Functor.comp_map, Functor.id_map] using hlocal a)
    have hi' : IsIso ((sfIntrinsicDerivedEquivalence (U a).toScheme B).functor.map
        ((sfFixedDerivedPullback B (U a).ι).map g)) :=
      (NatIso.isIso_map_iff (reductionRealizationPullbackIso B (U a).ι) g).mp hi
    exact isIso_of_reflects_iso _ (sfIntrinsicDerivedEquivalence (U a).toScheme B).functor
  have hg : IsIso g := by
    obtain ⟨C, v, δ, ht⟩ := Pretriangulated.distinguished_cocone_triangle g
    apply (Pretriangulated.Triangle.isZero₃_iff_isIso₁ _ ht).mp
    apply isZero_of_forall_isZero_mapDerivedCategory_upperStar
      (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) U hcover
    intro a
    have := hfixed a
    apply (Pretriangulated.Triangle.isZero₃_iff_isIso₁ _
      ((sfFixedDerivedPullback B (U a).ι).map_distinguished _ ht)).mpr
    exact hfixed a
  have : IsIso (c.app K).hom := isIso_of_reflects_iso _ E.inverse
  exact (ObjectProperty.isIso_hom_iff (c.app K)).mp inferInstance

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
  (q : SpTowerCalculus.Coordinates l E b)

/-- The finite adjunction square used for scalar change, in characteristic zero.
Source: latest blueprint, Levels paragraph (blueprint:
lem-dla1-tower-representing-pair-scalar-change-injective).

Given finite-Tor preservation at both levels and invertibility of the direct-image
comparison, there are the two restricted compact-support adjunctions, the scalar
comparison `beta` (whose inverse is pinned to the inverse direct-image comparison), and
an invertible `gamma` satisfying the counit equation of the mate transport.  In positive
characteristic this is `reductionExceptional_isIso`, applied in the item module; that
theorem needs `0 < pchar` for its finite admissible coordinate cover, so only the
characteristic-zero case is left here.

Proof: the finite compact-support and scalar functors are restricted to their full
finite-Tor subcategories, and finite smooth purity gives their right adjoints `f^!`
(the pullback followed by the Tate line and shift).  `beta` is the direct-image
comparison, an isomorphism by `hcomp`.  Its mate `gamma` is the unique transformation with
the displayed counit equation; it is invertible because derived scalar extension commutes
with pullback, the finite free Tate line and the shift, checked on smooth coordinate
charts and glued by conservativity of pullback on the chart cover.  In characteristic
zero the coordinate charts come from the smooth local normal form over `k` directly.
-/
theorem tower_representing_pair_scalar_change_adjunction_square
    (k : Type u) [Field k] [PerfectField k] (_hell : IsUnit (l : k))
    (_hchar : ringChar k = 0)
    (X Y : Over (Spec (CommRingCat.of k)))
    [IsSeparated X.hom] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [IsSeparated Y.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    (f : X ⟶ Y) [IsSeparated f.left] [LocallyOfFiniteType f.left]
    [QuasiCompact f.left] (r : ℕ) [SmoothOfRelativeDimension r f.left]
    (c : Compactification f.left) (m n : ℕ) (h : m ≤ n)
    (hFA : ∀ M : spFiniteConstructibleTorCategory X.left (SpTowerShriek.R l E n),
      spFiniteConstructibleTor Y.left (SpTowerShriek.R l E n)
        ((reductionCompactSupport (SpTowerShriek.R l E n) c.i c.g).obj M.obj))
    (hFB : ∀ M : spFiniteConstructibleTorCategory X.left (SpTowerShriek.R l E m),
      spFiniteConstructibleTor Y.left (SpTowerShriek.R l E m)
        ((reductionCompactSupport (SpTowerShriek.R l E m) c.i c.g).obj M.obj))
    (hSX : ∀ M : spFiniteConstructibleTorCategory X.left (SpTowerShriek.R l E n),
      spFiniteConstructibleTor X.left (SpTowerShriek.R l E m)
        ((scalarExtensionFunctor (SpTowerCalculus.quotient l E h) X.left).obj M.obj))
    (hSY : ∀ M : spFiniteConstructibleTorCategory Y.left (SpTowerShriek.R l E n),
      spFiniteConstructibleTor Y.left (SpTowerShriek.R l E m)
        ((scalarExtensionFunctor (SpTowerCalculus.quotient l E h) Y.left).obj M.obj))
    (hcomp : ∀ M : spFiniteConstructibleTorCategory X.left (SpTowerShriek.R l E n),
      IsIso ((reductionDirectImageComparison (SpTowerCalculus.quotient l E h)
        c.i c.g).app M.obj)) :
    ∃ (GA : spFiniteConstructibleTorCategory Y.left (SpTowerShriek.R l E n) ⥤
        spFiniteConstructibleTorCategory X.left (SpTowerShriek.R l E n))
      (GB : spFiniteConstructibleTorCategory Y.left (SpTowerShriek.R l E m) ⥤
        spFiniteConstructibleTorCategory X.left (SpTowerShriek.R l E m))
      (adjA : reductionCtfCompactSupport (SpTowerShriek.R l E n) c.i c.g hFA ⊣ GA)
      (adjB : reductionCtfCompactSupport (SpTowerShriek.R l E m) c.i c.g hFB ⊣ GB)
      (beta : reductionCtfCompactSupport (SpTowerShriek.R l E n) c.i c.g hFA ⋙
          reductionCtfScalar (SpTowerCalculus.quotient l E h) Y.left hSY ≅
        reductionCtfScalar (SpTowerCalculus.quotient l E h) X.left hSX ⋙
          reductionCtfCompactSupport (SpTowerShriek.R l E m) c.i c.g hFB)
      (gamma : GA ⋙ reductionCtfScalar (SpTowerCalculus.quotient l E h) X.left hSX ≅
        reductionCtfScalar (SpTowerCalculus.quotient l E h) Y.left hSY ⋙ GB),
      (∀ M, (beta.inv.app M).hom =
        @inv _ _ _ _ ((reductionDirectImageComparison (SpTowerCalculus.quotient l E h)
          c.i c.g).app M.obj) (hcomp M)) ∧
      (∀ K, (reductionCtfCompactSupport (SpTowerShriek.R l E m) c.i c.g hFB).map
          (gamma.hom.app K) ≫
          adjB.counit.app ((reductionCtfScalar (SpTowerCalculus.quotient l E h)
            Y.left hSY).obj K) =
        beta.inv.app (GA.obj K) ≫
          (reductionCtfScalar (SpTowerCalculus.quotient l E h) Y.left hSY).map
            (adjA.counit.app K)) := by
  classical
  have : IsNoetherian X.left := isNoetherian_of_locallyOfFiniteType X.hom
  have : IsNoetherian Y.left := isNoetherian_of_locallyOfFiniteType Y.hom
  have hpow (a : ℕ) : IsUnit ((l ^ a : ℕ) : Γ(Y.left, ⊤)) := by
    have hu := (_hell.pow a).map (Scheme.ΓSpecIso (.of k)).inv.hom
    simpa only [map_pow, map_natCast, Nat.cast_pow] using hu.map Y.hom.appTop.hom
  have htors (a : ℕ) : ∃ t : ℕ, ∀ x : SpTowerShriek.R l E a, (l ^ t) • x = 0 := by
    refine ⟨a + 1, fun x ↦ ?_⟩
    have hz : ((l ^ (a + 1) : ℕ) : SpTowerShriek.R l E a) = 0 := by
      have hz := Ideal.Quotient.eq_zero_iff_mem.mpr
        (Ideal.pow_mem_pow (I := spEllIdeal l E)
          (Ideal.subset_span (Set.mem_singleton (l : Padic.coefficientExtensionIntegers l E)))
          (a + 1))
      simpa only [map_pow, map_natCast, Nat.cast_pow] using hz
    rw [nsmul_eq_mul, hz, zero_mul]
  have hexp (a : ℕ) : HasInvertibleExponent (ULift.{u + 1} (SpTowerShriek.R l E a))
      Y.left := by
    obtain ⟨t, ht⟩ := htors a
    refine ⟨l ^ t, pow_pos (Fact.out : l.Prime).pos _, ?_, hpow t⟩
    apply ULift.ext
    change ((l ^ t : ℕ) : SpTowerShriek.R l E a) = 0
    simpa only [nsmul_eq_mul, mul_one] using ht 1
  have := hexp n
  have := hexp m
  obtain ⟨GA, adjA, ⟨RA⟩⟩ := realizationFromData (SpTowerShriek.R l E n) c.i c.g hFA
    (ordinaryCtfData (SpTowerShriek.R l E n) k Y.hom c.i c.g)
  obtain ⟨GB, adjB, ⟨RB⟩⟩ := realizationFromData (SpTowerShriek.R l E m) c.i c.g hFB
    (ordinaryCtfData (SpTowerShriek.R l E m) k Y.hom c.i c.g)
  let beta : reductionCtfCompactSupport (SpTowerShriek.R l E n) c.i c.g hFA ⋙
      reductionCtfScalar (SpTowerCalculus.quotient l E h) Y.left hSY ≅
      reductionCtfScalar (SpTowerCalculus.quotient l E h) X.left hSX ⋙
        reductionCtfCompactSupport (SpTowerShriek.R l E m) c.i c.g hFB :=
    NatIso.ofComponents
      (fun M ↦ by
        have := hcomp M
        exact (spFiniteConstructibleTor Y.left (SpTowerShriek.R l E m)).fullyFaithfulι.preimageIso
          (asIso ((reductionDirectImageComparison (SpTowerCalculus.quotient l E h)
            c.i c.g).app M.obj)))
      (by
        intro M N g
        apply ObjectProperty.hom_ext
        exact (reductionDirectImageComparison (SpTowerCalculus.quotient l E h)
          c.i c.g).naturality g.hom)
  let c0 := (mateEquiv adjA adjB (TwoSquare.mk
    (reductionCtfScalar (SpTowerCalculus.quotient l E h) X.left hSX) _ _
    (reductionCtfScalar (SpTowerCalculus.quotient l E h) Y.left hSY) beta.inv)).natTrans
  have hc (K) :
      (reductionCtfCompactSupport (SpTowerShriek.R l E m) c.i c.g hFB).map (c0.app K) ≫
          adjB.counit.app ((reductionCtfScalar (SpTowerCalculus.quotient l E h)
            Y.left hSY).obj K) =
        beta.inv.app (GA.obj K) ≫
          (reductionCtfScalar (SpTowerCalculus.quotient l E h) Y.left hSY).map
            (adjA.counit.app K) :=
    mateEquiv_counit adjA adjB (TwoSquare.mk
      (reductionCtfScalar (SpTowerCalculus.quotient l E h) X.left hSX) _ _
      (reductionCtfScalar (SpTowerCalculus.quotient l E h) Y.left hSY) beta.inv) K
  have hc' (K) :
      (reductionCompactSupport (SpTowerShriek.R l E m) c.i c.g).map (c0.app K).hom ≫
          (adjB.counit.app ((reductionCtfScalar (SpTowerCalculus.quotient l E h)
            Y.left hSY).obj K)).hom =
        @inv _ _ _ _ ((reductionDirectImageComparison (SpTowerCalculus.quotient l E h)
          c.i c.g).app (GA.obj K).obj) (hcomp (GA.obj K)) ≫
          (scalarExtensionFunctor (SpTowerCalculus.quotient l E h) Y.left).map
            (adjA.counit.app K).hom :=
    congrArg (fun v ↦ v.hom) (hc K)
  have hchart := scalar_chart_equation l hpow r c.i c.g
    (SpTowerCalculus.quotient l E h) hFA hFB hSX hSY GA GB adjA adjB RA RB c0
    (fun K ↦ hcomp (GA.obj K)) hc'
  have : ∀ K, IsIso (c0.app K) := scalar_components_isIso l f.left r c.i c.g c.comm.symm
    (htors n) (htors m) (SpTowerCalculus.quotient l E h)
    hFA hFB hSX hSY GA GB adjA adjB RA RB c0 hchart
  have : IsIso c0 := NatIso.isIso_of_isIso_app c0
  exact ⟨GA, GB, adjA, adjB, beta, asIso c0, fun M ↦ rfl, hc⟩

end AlgebraicGeometry.ProEtale.SpTowerGluing
