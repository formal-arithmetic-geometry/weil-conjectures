/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Finite.Ring.FiniteRingBundleSectionOrientationData
import WeilConjectures.AlgebraicGeometry.Bundle.BundleSectionPurityUnitNormalization
import WeilConjectures.AlgebraicGeometry.Bundle.BundleSectionOrientationMapExt
import WeilConjectures.AlgebraicGeometry.Bundle.BundleSectionPurityUnitIsIso
import WeilConjectures.AlgebraicGeometry.VectorTraceGeometry.VectorTraceGeometry
import WeilConjectures.AlgebraicGeometry.Bundle.BundleSectionRankZeroAffineNormalization
import WeilConjectures.AlgebraicGeometry.Bundle.BundleSectionComparisonIsoPasting

/-! # Finite-ring orientations along bundle zero sections

The canonical integration mate constructs the orientation. Its affine normalization
and equality detection on affine frames give existence and uniqueness.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale

attribute [local irreducible] VectorBundleZeroSection.scheme VectorBundleZeroSection.π
  VectorBundleZeroSection.over VectorBundleZeroSection.antiEquivalence

private theorem proof_indexed_heq {α : Sort*} {P : α → Prop} {β : α → Sort*}
    (f : (a : α) → P a → β a) {a b : α} (h : a = b) (ha : P a) (hb : P b) :
    HEq (f a ha) (f b hb) := by
  subst b
  rfl

private theorem normalized_orientation_eq (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ)
    (M : S.Modules) [M.IsFiniteLocallyFreeOfRank d]
    (o o' : bundleSectionObject A S d M ≅ affineLinearBaseCoefficient A N hA S d)
    (ho : BundleSectionOrientationNormalization N hN A hA S hS d M o)
    (ho' : BundleSectionOrientationNormalization N hN A hA S hS d M o') : o = o' := by
  obtain ⟨t, D, _, _⟩ := exists_affineSpaceTopTrace N hN A hA
  have h : o.inv = o'.inv := by
    apply bundleSectionOrientation_map_ext N hN A hA S hS d M
    intro V hV e
    exact (ho t D V hV e).trans (ho' t D V hV e).symm
  have he : o.symm = o'.symm := Iso.ext h
  exact congrArg Iso.symm he

/-- The normalized local orientations glue uniquely, including all frame changes.
Source: orientation-charts Step 4 (blueprint: lem-trf-finite-ring-bundle-section-orientation).

Proof: (1) bundle projective completion and Noetherian open restriction supply all geometric
hypotheses. (2) Conjugate the affine coordinate-tower adjunction through the unbounded
compact-support compositor. Its counit identifies its comparison at the unit with alpha_p,
so alpha_p is invertible. (3) Compose open extension/restriction adjunctions with the ambient
adjunctions. The resulting Hom chain defines exactly bundleSectionComparison; mate pasting
proves its composition law. (4) Affine-trace base change identifies restricted adjuncts,
even on non-affine intersections. (5) Linear trace invariance makes the two frame adjuncts
agree, without any determinant factor. (6) Shift source and target by -2d into the heart.
Degree-zero derived-map gluing gives a unique map and glues the inverse maps; uniqueness
makes both composites identities. (7) Induced frames prove bundle-isomorphism naturality.
(8) The rank-zero tower is the identity adjunction. Empty covers and zero coefficients are
included. (9) At the coefficient unit the canonical projection formula is the identity
under unitors; both signed symmetries have sign one. (10) Integration restricts to the same
coordinate traces, so inverse bundle purity has these frame restrictions and uniqueness
identifies it with the orientation. Annihilator changes use the finite Tate power maps.
-/
theorem finiteRingBundleSectionOrientation (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ)
    (M : S.Modules) [M.IsFiniteLocallyFreeOfRank d] :
    ∃! o : bundleSectionObject A S d M ≅ affineLinearBaseCoefficient A N hA S d,
      BundleSectionOrientationNormalization N hN A hA S hS d M o := by
  obtain ⟨p, hp, hm⟩ := bundleSectionPurityUnit_exists_isIso N hN A hA S hS d M
  let q := (bundleSectionCoefficientIso A N hA S d M).inv ≫
    (ordinaryFinitePullback A (VectorBundleZeroSection.zero S d M)).map
      (bundleSectionPurityUnitMap N hN A hA S hS d M p)
  have : IsIso q := IsIso.comp_isIso' (Iso.isIso_inv _)
    (Functor.map_isIso _ _)
  let o := (asIso q).symm
  have ho : BundleSectionOrientationNormalization N hN A hA S hS d M o :=
    bundleSectionPurityUnit_normalization N hN A hA S hS d M p hp o rfl
  refine ⟨o, ho, ?_⟩
  intro o' ho'
  exact normalized_orientation_eq N hN A hA S hS d M o' o ho' ho

/-- Preservation under a linear bundle isomorphism. The last hypothesis expresses linearity
in frames: every linear frame of M is carried to a linear frame of P. The two preceding
equations are its structural-map and zero-section equations, not extra geometric conditions.
Source: orientation-charts Step 4 (blueprint: lem-trf-finite-ring-bundle-section-orientation).

Proof: compose a frame of the target with the bundle isomorphism. Counit-preserving
comparison and mate pasting identify the two local normalization equations. Uniqueness
in degree-zero gluing makes the two maps equal globally (node proof Step 7). -/
theorem finiteRingBundleSectionOrientation_naturality (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ)
    (M P : S.Modules) [M.IsFiniteLocallyFreeOfRank d] [P.IsFiniteLocallyFreeOfRank d]
    (o : bundleSectionObject A S d M ≅ affineLinearBaseCoefficient A N hA S d)
    (o' : bundleSectionObject A S d P ≅ affineLinearBaseCoefficient A N hA S d)
    (_ho : BundleSectionOrientationNormalization N hN A hA S hS d M o)
    (_ho' : BundleSectionOrientationNormalization N hN A hA S hS d P o')
    (h : VectorBundleZeroSection.scheme S d M ≅ VectorBundleZeroSection.scheme S d P)
    (hp : h.hom ≫ VectorBundleZeroSection.π S d P = VectorBundleZeroSection.π S d M)
    (hz : VectorBundleZeroSection.zero S d M ≫ h.hom = VectorBundleZeroSection.zero S d P)
    (_hlin : ∀ (V : S.Opens) (e : VectorBundleZeroSection.Trivialization S d M V),
      ∃ e' : VectorBundleZeroSection.Trivialization S d P V,
        vectorIntegrationChart S d M V e ≫ h.hom = vectorIntegrationChart S d P V e') :
    (leftDerivedUpperStarId (ModuleCat.{u + 1} A) S).inv.app
        (bundleSectionObject A S d P) ≫
      bundleSectionComparison A (VectorBundleZeroSection.π S d P)
        (VectorBundleZeroSection.π S d M) h.hom (𝟙 S)
        (IsPullback.of_horiz_isIso
          (CommSq.mk (hp.trans (Category.comp_id _).symm)))
        (VectorBundleZeroSection.zero S d P) (VectorBundleZeroSection.zero S d M)
        (hz.trans (Category.id_comp _).symm) ≫ o.hom = o'.hom := by
  let c : bundleSectionObject A S d P ⟶ bundleSectionObject A S d M :=
    (leftDerivedUpperStarId (ModuleCat.{u + 1} A) S).inv.app
      (bundleSectionObject A S d P) ≫
    bundleSectionComparison A (VectorBundleZeroSection.π S d P)
      (VectorBundleZeroSection.π S d M) h.hom (𝟙 S)
      (IsPullback.of_horiz_isIso
        (CommSq.mk (hp.trans (Category.comp_id _).symm)))
      (VectorBundleZeroSection.zero S d P) (VectorBundleZeroSection.zero S d M)
      (hz.trans (Category.id_comp _).symm)
  obtain ⟨t, D, _, _⟩ := exists_affineSpaceTopTrace N hN A hA
  have he : o'.inv ≫ c = o.inv := by
    apply bundleSectionOrientation_map_ext N hN A hA S hS d M
    intro V hV f
    obtain ⟨f', hf⟩ := _hlin V f
    have hM := vectorIntegrationChart_isPullback S d M V f
    have hP := vectorIntegrationChart_isPullback S d P V f'
    have hwM : bundleSectionChartZero S d M V f ≫ vectorIntegrationChart S d M V f =
        V.ι ≫ VectorBundleZeroSection.zero S d M := hM.lift_fst _ _ _
    have hwP : bundleSectionChartZero S d P V f' ≫ vectorIntegrationChart S d P V f' =
        V.ι ≫ VectorBundleZeroSection.zero S d P := hP.lift_fst _ _ _
    have hzero : bundleSectionChartZero S d M V f =
        bundleSectionChartZero S d P V f' := by
      apply hP.hom_ext
      · have hh : bundleSectionChartZero S d M V f ≫
            vectorIntegrationChart S d P V f' =
          V.ι ≫ VectorBundleZeroSection.zero S d P := by
          simpa only [Category.assoc, hf, hz] using
            congrArg (fun k ↦ k ≫ h.hom) hwM
        exact hh.trans hwP.symm
      · exact (hM.lift_snd _ _ _).trans (hP.lift_snd _ _ _).symm
    have hc := bundleSectionComparison_iso_pasting A
      (VectorBundleZeroSection.π S d P) (VectorBundleZeroSection.π S d M)
      (affineTraceProjection V.toScheme d) h hp V.ι
      (vectorIntegrationChart S d M V f) hM (hf.symm ▸ hP)
      (VectorBundleZeroSection.zero S d P) (VectorBundleZeroSection.zero S d M)
      (bundleSectionChartZero S d M V f) hz hwM
      (by rw [← Category.assoc, hwM, Category.assoc, hz])
    simp only [c, bundleSectionChartComparison, hf] at hc ⊢
    erw [Functor.map_comp, Category.assoc, hc]
    have hnormM := _ho t D V hV f
    have hnormP := _ho' t D V hV f'
    have hn := proof_indexed_heq
      (fun (b : V.toScheme ⟶ affineTraceTower V.toScheme d)
        (hb : b ≫ affineTraceProjection V.toScheme d = 𝟙 V.toScheme) ↦
        (vectorIntegrationBaseCoefficientPullback A N hA t V.ι hS d).hom ≫
          ((ordinaryFinitePullback A b).mapIso
              (affineLinearCoefficientDescent A N hA t V.toScheme
                (affineTracePullbackInvertible N V.ι hS) d) ≪≫
            (leftDerivedUpperStarCompSectionIso (ModuleCat.{u + 1} A) b
              (affineTraceProjection V.toScheme d) hb).app
                (affineLinearBaseCoefficient A N hA V.toScheme d)).inv ≫
          (ordinaryFinitePullback A b).map
            (bundleSectionAffineAdjunct N hN A hA t D V.toScheme
              (affineTracePullbackInvertible N V.ι hS) d))
      hzero.symm (hP.lift_snd _ _ _) (hM.lift_snd _ _ _)
    have hl := proof_indexed_heq
      (fun (b : V.toScheme ⟶ affineTraceTower V.toScheme d)
        (hb : b ≫ vectorIntegrationChart S d P V f' =
          V.ι ≫ VectorBundleZeroSection.zero S d P) ↦
        (ordinaryFinitePullback A V.ι).map o'.inv ≫
          bundleSectionComparison A (VectorBundleZeroSection.π S d P)
            (affineTraceProjection V.toScheme d) (vectorIntegrationChart S d P V f')
            V.ι hP (VectorBundleZeroSection.zero S d P) b hb)
      hzero (by rw [← hf, ← Category.assoc, hwM, Category.assoc, hz]) hwP
    exact eq_of_heq (hl.trans ((heq_of_eq hnormP).trans
      (hn.trans (heq_of_eq hnormM.symm))))
  have hfin : c ≫ o.hom = o'.hom := by
    apply (cancel_epi o'.inv).1
    calc
      o'.inv ≫ c ≫ o.hom = (o'.inv ≫ c) ≫ o.hom := (Category.assoc _ _ _).symm
      _ = o.inv ≫ o.hom := congrArg (fun k ↦ k ≫ o.hom) he
      _ = o'.inv ≫ o'.hom := o.inv_hom_id.trans o'.inv_hom_id.symm
  exact (Category.assoc _ _ _).symm.trans hfin

/-- Identity normalization in rank zero, with the canonical geometric identification.
Source: orientation-charts Step 4 (blueprint: lem-trf-finite-ring-bundle-section-orientation).

Proof: the rank-zero symmetric algebra is the structure algebra and augmentation is the
identity. Thus pi and z are inverse. The coordinate tower, counit and its adjunct are the
identity in dimension zero. The normalization on every frame and unique gluing identify
o with the displayed identity-adjunction comparison (node proof Step 8). -/
theorem finiteRingBundleSectionOrientation_rankZero (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤)))
    (M : S.Modules) [M.IsFiniteLocallyFreeOfRank 0]
    (o : bundleSectionObject A S 0 M ≅ affineLinearBaseCoefficient A N hA S 0)
    (_ho : BundleSectionOrientationNormalization N hN A hA S hS 0 M o) :
    ∃ (e : VectorBundleZeroSection.scheme S 0 M ≅ S)
      (_hp : e.hom = VectorBundleZeroSection.π S 0 M)
      (hz : e.inv = VectorBundleZeroSection.zero S 0 M),
      o.hom = bundleSectionRankZeroComparison A S M e hz := by
  have := VectorTraceGeometry.zero_isIso S M
  let e := asIso (VectorBundleZeroSection.π S 0 M)
  have hz : e.inv = VectorBundleZeroSection.zero S 0 M := by
    apply (cancel_mono (VectorBundleZeroSection.π S 0 M)).1
    exact e.inv_hom_id.trans (VectorBundleZeroSection.zero_spec S 0 M).1.symm
  have : IsIso (VectorBundleZeroSection.zero S 0 M) := hz ▸ e.isIso_inv
  have hb := isIso_rightDerivedUpperShriekBaseChangeMap_of_isOpenImmersion A
    (IsPullback.of_horiz_isIso
      (CommSq.mk ((VectorBundleZeroSection.zero_spec S 0 M).1.trans
        (Category.comp_id _).symm)))
  have : IsIso (bundleSectionRankZeroComparison A S M e hz) := by
    dsimp only [bundleSectionRankZeroComparison, bundleSectionComparison]
    infer_instance
  let c : bundleSectionObject A S 0 M ≅ affineLinearBaseCoefficient A N hA S 0 :=
    asIso (bundleSectionRankZeroComparison A S M e hz)
  have hc : BundleSectionOrientationNormalization N hN A hA S hS 0 M c := by
    intro t D V hV f
    exact bundleSectionRankZero_affineNormalization N hN A hA S hS M e rfl hz
      t D V hV f
  refine ⟨e, rfl, hz, ?_⟩
  exact congrArg Iso.hom (normalized_orientation_eq N hN A hA S hS 0 M o c _ho hc)

/-- For valuation quotients the orientation is the restriction of inverse bundle purity.
The existing coefficient type denotes O_F / varpi_F^(n+1), so n ranges over all positive
quotient levels without excluding the first level. The equation uses inverse orientations
and therefore refers directly to the specified gamma, without choosing another isomorphism.
Source: orientation-charts Step 4 (blueprint: lem-trf-finite-ring-bundle-section-orientation).

Proof: at the unit the proper projection map is the transpose of the counit and hence
identity under unitors. The open factor is likewise identity, and the two derived
symmetries have sign one. Thus gamma at the unit is the adjunct of t_pi. Its restriction
to every frame is alpha_p by the integration normalization and mate pasting. Inverting
and restricting by zero gives the prescribed frame orientation. Unique degree-zero gluing
identifies it with o. Any different annihilating power gives the same line by the canonical
roots-of-unity power comparisons (node proof Steps 9--10). -/
theorem finiteRingBundleSectionOrientation_valuation
    (ell : ℕ) [Fact ell.Prime] (F : Type u) [Field F] [Algebra (Padic ell) F]
    [FiniteDimensional (Padic ell) F] (n N : ℕ) (hN : 0 < N)
    (hA : (N : Scheme.finiteTateCoefficient ell F n) = 0)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤)))
    (_hEll : IsUnit (ell : Γ(S, ⊤))) (d : ℕ)
    (M : S.Modules) [M.IsFiniteLocallyFreeOfRank d]
    (o : bundleSectionObject (Scheme.finiteTateCoefficient ell F n) S d M ≅
      affineLinearBaseCoefficient (Scheme.finiteTateCoefficient ell F n) N hA S d)
    (_ho : BundleSectionOrientationNormalization N hN
      (Scheme.finiteTateCoefficient ell F n) hA S hS d M o) :
    BundleSectionPurityCompatibility N hN
      (Scheme.finiteTateCoefficient ell F n) hA S hS d M o := by
  obtain ⟨p, hp, hm⟩ := bundleSectionPurityUnit_exists_isIso N hN _ hA S hS d M
  let q := (bundleSectionCoefficientIso _ N hA S d M).inv ≫
    (ordinaryFinitePullback _ (VectorBundleZeroSection.zero S d M)).map
      (bundleSectionPurityUnitMap N hN _ hA S hS d M p)
  have : IsIso q := IsIso.comp_isIso' (Iso.isIso_inv _)
    (Functor.map_isIso _ _)
  let o' := (asIso q).symm
  have ho' : BundleSectionOrientationNormalization N hN _ hA S hS d M o' :=
    bundleSectionPurityUnit_normalization N hN _ hA S hS d M p hp o' rfl
  have he := normalized_orientation_eq N hN _ hA S hS d M o o' _ho ho'
  refine ⟨p, hp, ?_⟩
  exact congrArg Iso.inv he

end AlgebraicGeometry.Etale
