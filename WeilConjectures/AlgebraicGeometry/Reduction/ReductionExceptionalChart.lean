/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Reduction.ReductionExceptionalObjects
import WeilConjectures.AlgebraicGeometry.Reduction.ReductionExceptionalObjects
import WeilConjectures.AlgebraicGeometry.Reduction.ReductionExceptionalCounitDescent
import WeilConjectures.AlgebraicGeometry.Reduction.ReductionExceptionalOrdinaryChart
import all WeilConjectures.AlgebraicGeometry.AdjunctionTransfer.EtaleCtfChartDomain
import all WeilConjectures.AlgebraicGeometry.AdjunctionTransfer.EtaleProEtaleAdjunctionTransfer
public import WeilConjectures.AlgebraicGeometry.Reduction.ReductionSiteScalarPullback

/-! # Canonical chart equation for the exceptional coefficient transpose -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.ProEtale

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

end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.ProEtale

private theorem transfer_chart
    {C D E F C' D' E' F' : Type*}
    [Category* C] [Category* D] [Category* E] [Category* F]
    [Category* C'] [Category* D'] [Category* E'] [Category* F']
    (SA : C ⥤ C') (SAU : D ⥤ D') (SB : E ⥤ E') (SBU : F ⥤ F')
    (TX : C ⥤ E) (TU : D ⥤ F) (IX : C' ⥤ E') (IU : D' ⥤ F')
    (PA : C ⥤ D) (PB : E ⥤ F) (IPA : C' ⥤ D') (IPB : E' ⥤ F')
    (sx : SA ⋙ IX ≅ TX ⋙ SB) (su : SAU ⋙ IU ≅ TU ⋙ SBU)
    (pa : SA ⋙ IPA ≅ PA ⋙ SAU) (pb : SB ⋙ IPB ≅ PB ⋙ SBU)
    (dx : IX ⋙ IPB ≅ IPA ⋙ IU) (de : TX ⋙ PB ≅ PA ⋙ TU)
    {M : C'} {N : E'} {L : C} {Q : E} {L' : D} {Q' : F}
    (a : M ≅ SA.obj L) (b : N ≅ SB.obj Q)
    (m : IX.obj M ⟶ N) (q : TX.obj L ⟶ Q)
    (rA : PA.obj L ≅ L') (rB : PB.obj Q ≅ Q')
    (v : TU.obj L' ⟶ Q')
    (hq : SB.map q = sx.inv.app L ≫ IX.map a.inv ≫ m ≫ b.hom)
    (cube : dx.inv.app (SA.obj L) ≫ IPB.map (sx.hom.app L) ≫
      pb.hom.app (TX.obj L) = IU.map (pa.hom.app L) ≫
        su.hom.app (PA.obj L) ≫ SBU.map (de.inv.app L))
    (chart : de.inv.app L ≫ PB.map q ≫ rB.hom = TU.map rA.hom ≫ v) :
    dx.inv.app M ≫ IPB.map m ≫ IPB.map b.hom ≫ pb.hom.app Q ≫ SBU.map rB.hom =
      IU.map (IPA.map a.hom ≫ pa.hom.app L ≫ SAU.map rA.hom) ≫
        su.hom.app L' ≫ SBU.map v := by
  have hm : m ≫ b.hom = IX.map a.hom ≫ sx.hom.app L ≫ SB.map q := by
    rw [hq]
    simp only [Iso.hom_inv_id_app_assoc]
    rw [← IX.map_comp_assoc, Iso.hom_inv_id, IX.map_id, Category.id_comp]
  have hd := dx.inv.naturality a.hom
  have hp := pb.hom.naturality q
  have hs := su.hom.naturality rA.hom
  dsimp only [Functor.comp_map] at hd hp hs
  simp only [Functor.map_comp, Category.assoc] at ⊢
  calc
    _ = dx.inv.app M ≫ IPB.map (m ≫ b.hom) ≫
        pb.hom.app Q ≫ SBU.map rB.hom := by rw [IPB.map_comp, Category.assoc]
    _ = IU.map (IPA.map a.hom) ≫ dx.inv.app (SA.obj L) ≫
        IPB.map (sx.hom.app L) ≫ pb.hom.app (TX.obj L) ≫
        SBU.map (PB.map q ≫ rB.hom) := by
      rw [hm]
      simp only [IPB.map_comp, SBU.map_comp, Category.assoc]
      rw [← reassoc_of% hd, reassoc_of% hp]
    _ = IU.map (IPA.map a.hom) ≫ IU.map (pa.hom.app L) ≫
        su.hom.app (PA.obj L) ≫ SBU.map (de.inv.app L ≫ PB.map q ≫ rB.hom) := by
      simp only [SBU.map_comp]
      rw [reassoc_of% cube]
    _ = IU.map (IPA.map a.hom) ≫ IU.map (pa.hom.app L) ≫
        IU.map (SAU.map rA.hom) ≫ su.hom.app L' ≫ SBU.map v := by
      rw [chart, SBU.map_comp]
      rw [← reassoc_of% hs]

private theorem site_map_bijective
    (A : Type u) [CommRing A] [Finite A] (T : Scheme.{u})
    (K L : Etale.DerivedCategoryModule (ULift.{u + 1, u} A) T)
    (hL : _root_.DerivedCategory.TStructure.t.plus L) :
    Function.Bijective ((reductionSite A T).map : (K ⟶ L) → _) := by
  exact ((sfIntrinsicDerivedEquivalence T A).fullyFaithfulFunctor.map_bijective _ _).comp
    (bijective_comparisonUpperStar_mapDerivedCategory_map K L hL)

private theorem site_plus_full
    (A : Type u) [CommRing A] [Finite A] (T : Scheme.{u}) :
    (DerivedCategory.Plus.ι ⋙ reductionSite A T).Full := by
  constructor
  intro K L f
  obtain ⟨g, hg⟩ := (site_map_bijective A T K.obj L.obj L.property).2 f
  exact ⟨ObjectProperty.homMk g, hg⟩

private theorem site_plus_faithful
    (A : Type u) [CommRing A] [Finite A] (T : Scheme.{u}) :
    (DerivedCategory.Plus.ι ⋙ reductionSite A T).Faithful := by
  constructor
  intro K L f g h
  ext
  exact (site_map_bijective A T K.obj L.obj L.property).1 h

/-- The counit transpose of the fixed compact-support coefficient comparison has
its canonical ordered Tate reassociation on every smooth coordinate chart.
Source: blueprint latest, sec-smooth-purity, sk-lem-sp-reduction-exceptional.proof.md,
Steps 5--12 (blueprint: lem-sp-reduction-exceptional-chart).

Proof: scalar preservation gives bounded-below ordinary scalar origins. Full
faithfulness of site comparison lifts their normalized site isomorphism to a
natural origin isomorphism. The characteristic hypotheses make every common
ell-power annihilator invertible on Y. For each chart and input, comparison full
faithfulness lifts the actual intrinsic coefficient component to its unique
ordinary arrow. The coefficient/site square and the two realization counit
identities descend the given intrinsic counit equation to that ordinary arrow.
The ordinary chart calculation uses sum/evaluation followed by ordered affine
integration and right-adjoint uniqueness to give its canonical Tate scalar formula.
Paste this formula with the normalized scalar/site/pullback cube. Naturality moves
the realization and chart isomorphisms through the two boundaries; their inverse
identities cancel the lifted comparison, giving exactly the displayed intrinsic
chart equation. The argument uses the same fixed compactification throughout,
includes the zero ring and identity affine tower, and introduces no orientation. -/
theorem reductionExceptional_chartEquation
    (ℓ pchar : ℕ) [Fact ℓ.Prime] (hp : 0 < pchar) (hℓ : pchar ≠ ℓ)
    (k : Type u) [Field k] [CharP k pchar]
    {X Z Y : Scheme.{u}}
    [X.Over (Spec (.of k))] [Z.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of k))] [QuasiCompact (Z ↘ Spec (.of k))]
    [IsSeparated (Z ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))] (d : ℕ) [SmoothOfRelativeDimension d f]
    (j : X ⟶ Z) [IsOpenImmersion j] [j.IsOver (Spec (.of k))]
    (p : Z ⟶ Y) [IsProper p] [p.IsOver (Spec (.of k))] (hf : j ≫ p = f)
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
  have _ := hp
  have _ := hf
  have _ := hA
  have _ := hB
  have : IsLocallyNoetherian Y :=
    LocallyOfFiniteType.isLocallyNoetherian (Y ↘ Spec (.of k))
  have : CompactSpace Y :=
    QuasiCompact.compactSpace_of_compactSpace (Y ↘ Spec (.of k))
  have : IsNoetherian Y := ⟨⟩
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
  have hunit : IsUnit ((ℓ ^ n : ℕ) : Γ(Y, ⊤)) := by
    have h : (ℓ : k) ≠ 0 := CharP.cast_ne_zero_of_ne_of_prime k
      (Fact.out : ℓ.Prime) hℓ
    have hu := (isUnit_iff_ne_zero.mpr (pow_ne_zero n h)).map
      (Scheme.ΓSpecIso (.of k)).inv.hom
    simpa only [map_pow, map_natCast, Nat.cast_pow] using
      hu.map (Y ↘ Spec (.of k)).appTop.hom
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

end AlgebraicGeometry.ProEtale
