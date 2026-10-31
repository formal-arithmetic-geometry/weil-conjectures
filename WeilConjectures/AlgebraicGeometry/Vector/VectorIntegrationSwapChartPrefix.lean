/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.VectorTraceGeometry.VectorTraceGeometry
import all WeilConjectures.AlgebraicGeometry.VectorBundleZeroSection.VectorBundleMapFrameCoordinates
import all WeilConjectures.AlgebraicGeometry.Vector.VectorIntegrationBaseChangeCoordinates
import all WeilConjectures.AlgebraicGeometry.VectorTraceGeometry.VectorTraceGeometry
import all WeilConjectures.AlgebraicGeometry.Affine.Linear.AffineLinearTraceAction
import WeilConjectures.AlgebraicGeometry.Vector.VectorIntegrationCartesianPrefixBaseChange
import WeilConjectures.AlgebraicGeometry.Vector.VectorIntegrationBaseCoefficientComposition
import all WeilConjectures.AlgebraicGeometry.Affine.Linear.AffineLinearExchangeCoherence

/-! # Exchange of vector-bundle chart source comparisons

Source: blueprint latest, sec-smooth-purity/sk-prop-an/cor-pur-vector-bundle-purity.proof.md,
paragraph 2; local swap proof, Steps 1--2.
(blueprint: lem-pur-vector-integration-swap-chart-prefix).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Etale
open VectorBundleZeroSection
attribute [local irreducible] _root_.DerivedCategory.singleFunctors
attribute [local implicit_reducible] Scheme.Modules Scheme.Modules.Hom Matrix
  vectorIntegrationCoefficient vectorIntegrationSource
attribute [local irreducible] rightDerivedLowerShriek affineLinearCompactComparison
  affineLinearCoefficientDescent affineLinearBaseCoefficient
  leftDerivedUpperStarComp derivedSquareUpperStarIso upperStar Functor.leftDerivedFunctor
private theorem linear_coordinates
    {S T : Scheme.{u}} [IsNoetherian S] [IsNoetherian T]
    (f : T ⟶ S) (r : ℕ) (F : S.Modules) (G : T.Modules)
    [F.IsFiniteLocallyFreeOfRank r] [G.IsFiniteLocallyFreeOfRank r]
    (m : (Scheme.Modules.pullback f).obj F ≅ G)
    (v : scheme T r G ⟶ scheme S r F)
    (hv : VectorTraceGeometry.MapSpec f r r F G
      ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _ m.hom) v)
    (V : S.Opens) (eS : Trivialization S r F V)
    (U : T.Opens) (eT : Trivialization T r G U)
    (W : Scheme.{u}) (j : W ⟶ T) (a : W ⟶ U.toScheme) (g : W ⟶ V.toScheme)
    (ha : a ≫ U.ι = j) (hg : j ≫ f = g ≫ V.ι) :
    ∃ H : Matrix.GeneralLinearGroup (Fin r) Γ(W, ⊤),
      (affineTraceMap a r ≫ vectorIntegrationChart T r G U eT) ≫ v =
        affineTraceLinearMap W r H ≫
          (affineTraceMap g r ≫ vectorIntegrationChart S r F V eS) := by
  classical
  have h : (a ≫ U.ι) ≫ f = g ≫ V.ι := by rw [ha, hg]
  let φ : SheafOfModules.free (R := W.ringCatSheaf) (ULift.{u} (Fin r)) ≅
      SheafOfModules.free (R := W.ringCatSheaf) (ULift.{u} (Fin r)) :=
    (pulledFrame S r F V eS g).symm ≪≫
      (Scheme.Modules.pullbackCongr h.symm).app F ≪≫
      (Scheme.Modules.pullbackComp (a ≫ U.ι) f).symm.app F ≪≫
      (Scheme.Modules.pullback (a ≫ U.ι)).mapIso m ≪≫
      pulledFrame T r G U eT a
  let C : Matrix (Fin r) (Fin r) Γ(W, ⊤) :=
    fun i j ↦ Scheme.Modules.freeMatrix φ.hom (ULift.up i) (ULift.up j)
  let D : Matrix (Fin r) (Fin r) Γ(W, ⊤) :=
    fun i j ↦ Scheme.Modules.freeMatrix φ.inv (ULift.up i) (ULift.up j)
  have hCD : C * D = 1 := by
    have he := freeMatrix_comp φ.inv φ.hom
    rw [φ.inv_hom_id, freeMatrix_id] at he
    ext i j
    have he' := congrArg (fun z ↦ z (ULift.up i) (ULift.up j)) he
    simp only [Matrix.mul_apply] at he'
    change (∑ z : Fin r, C i z * D z j) = _
    rw [← Equiv.sum_comp (Equiv.ulift : ULift.{u} (Fin r) ≃ Fin r)
      (fun z ↦ C i z * D z j)]
    simpa [C, D, Matrix.one_apply] using he'.symm
  have hDC : D * C = 1 := by
    have he := freeMatrix_comp φ.hom φ.inv
    rw [φ.hom_inv_id, freeMatrix_id] at he
    ext i j
    have he' := congrArg (fun z ↦ z (ULift.up i) (ULift.up j)) he
    simp only [Matrix.mul_apply] at he'
    change (∑ z : Fin r, D i z * C z j) = _
    rw [← Equiv.sum_comp (Equiv.ulift : ULift.{u} (Fin r) ≃ Fin r)
      (fun z ↦ D i z * C z j)]
    simpa [C, D, Matrix.one_apply] using he'.symm
  let H : Matrix.GeneralLinearGroup (Fin r) Γ(W, ⊤) :=
    { val := C.transpose
      inv := D.transpose
      val_inv := by rw [← Matrix.transpose_mul, hDC, Matrix.transpose_one]
      inv_val := by rw [← Matrix.transpose_mul, hCD, Matrix.transpose_one] }
  refine ⟨H, ?_⟩
  let ℓ := (affineTraceMap a r ≫ vectorIntegrationChart T r G U eT) ≫
    v
  have hℓ : ℓ ≫ π S r F = (affineTraceProjection W r ≫ g) ≫ V.ι := by
    simp only [ℓ, Category.assoc]
    rw [hv.comm, reassoc_of% (vectorIntegrationChart_isPullback T r G U eT).w,
      reassoc_of% (affineTraceMap_isPullback a r).w]
    simpa only [Category.assoc] using congrArg (fun z ↦ affineTraceProjection W r ≫ z) h
  let sq := (isPullback_morphismRestrict (π S r F) V).flip
  let k := sq.lift ℓ (affineTraceProjection W r ≫ g) hℓ
  have hk : k ≫ ((π S r F) ⁻¹ᵁ V).ι = ℓ := sq.lift_fst _ _ _
  have hkp : k ≫ ((π S r F) ∣_ V) = affineTraceProjection W r ≫ g :=
    sq.lift_snd _ _ _
  have ht : IsIso (trivializationMap S r F V eS) :=
    (trivializationMap_spec S r F V eS).1
  have he : k ≫ trivializationMap S r F V eS =
      affineTraceLinearMap W r H ≫ affineTraceMap g r ≫
        (affineTraceAffineSpaceIso V.toScheme r).hom := by
    apply AffineSpace.hom_ext
    · simp only [Category.assoc, (trivializationMap_spec S r F V eS).2.1,
        affineTraceAffineSpaceIso, asIso_hom, affineTraceToAffineSpace,
        AffineSpace.homOfVector_over]
      rw [hkp, (affineTraceMap_isPullback g r).w, ← Category.assoc,
        affineTraceLinearMap_over]
    · rintro ⟨j⟩
      have hc := map_frame_coordinates f r r F G m.hom
        (v) hv V eS U eT W a g h k hk j
      rw [hc]
      simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
        affineTraceAffineSpaceIso, asIso_hom, affineTraceToAffineSpace,
        AffineSpace.homOfVector_appTop_coord, tower_map_coordinate,
        affineTraceLinearMap_coordinate]
      rfl
  change ℓ = _
  rw [← hk]
  unfold vectorIntegrationChart
  simp only [← Category.assoc]
  apply congrArg (fun z ↦ z ≫ ((π S r F) ⁻¹ᵁ V).ι)
  apply (cancel_mono (trivializationMap S r F V eS)).mp
  simpa only [Category.assoc, IsIso.inv_hom_id, Category.comp_id] using he

private lemma base_coefficient_id
    (A : Type (u + 1)) [CommRing A] (N : ℕ) (hA : (N : A) = 0)
    (t : OrdinaryFiniteTwistTransport A N hA)
    (S : Scheme.{u}) (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ) :
    vectorIntegrationBaseCoefficientPullback A N hA t (𝟙 S) hS d =
      (leftDerivedUpperStarId (ModuleCat.{u + 1} A) S).app
        (affineLinearBaseCoefficient A N hA S d) := by
  let L := affineLinearBaseCoefficient A N hA S d
  let B := vectorIntegrationBaseCoefficientPullback A N hA t (𝟙 S) hS d
  let I := leftDerivedUpperStarId (ModuleCat.{u + 1} A) S
  let C := leftDerivedUpperStarComp (ModuleCat.{u + 1} A) (𝟙 S) (𝟙 S) (𝟙 S)
    (Category.comp_id _).symm
  have h := vectorIntegrationBaseCoefficientPullback_comp A N hA t
    (𝟙 S) (𝟙 S) (𝟙 S) (Category.comp_id _).symm hS hS d
  change C.hom.app L ≫ (ordinaryFinitePullback A (𝟙 S)).map B.hom ≫ B.hom = B.hom at h
  have hu := leftDerivedUpperStarComp_id_right_hom_app (ModuleCat.{u + 1} A) (𝟙 S) L
  have hm : (ordinaryFinitePullback A (𝟙 S)).map B.hom =
      (ordinaryFinitePullback A (𝟙 S)).map (I.hom.app L) := by
    apply (cancel_epi (C.hom.app L)).mp
    apply (cancel_mono B.hom).mp
    simpa only [Category.assoc, Category.id_comp, ordinaryFinitePullback, C, I,
      reassoc_of% hu] using h
  let : (ordinaryFinitePullback A (𝟙 S)).Faithful := Functor.Faithful.of_iso I.symm
  apply Iso.ext
  exact (ordinaryFinitePullback A (𝟙 S)).map_injective hm

private lemma identity_square_coefficient
    (A : Type (u + 1)) [CommRing A] (N : ℕ) (hA : (N : A) = 0)
    (t : OrdinaryFiniteTwistTransport A N hA)
    {X X' S : Scheme.{u}} (p : X ⟶ S) (p' : X' ⟶ S) (v : X' ⟶ X)
    (sq : IsPullback v p' p (𝟙 S)) (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ) :
    (derivedSquareUpperStarIso (ModuleCat.{u + 1} A) sq.toCommSq).symm.app
        (affineLinearBaseCoefficient A N hA S d) ≪≫
      (ordinaryFinitePullback A p').mapIso
        (vectorIntegrationBaseCoefficientPullback A N hA t (𝟙 S) hS d) =
    (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) v p p'
      (sq.w.trans (Category.comp_id _)).symm).symm.app
        (affineLinearBaseCoefficient A N hA S d) := by
  have hp' : p' = v ≫ p := (sq.w.trans (Category.comp_id _)).symm
  subst p'
  rw [base_coefficient_id]
  apply Iso.ext
  simp only [derivedSquareUpperStarIso, Iso.symm_hom,
    Iso.trans_inv, Iso.symm_inv, NatTrans.comp_app, Iso.trans_hom,
    Iso.app_hom, Functor.mapIso_hom, Category.assoc]
  dsimp only [ordinaryFinitePullback]
  rw [leftDerivedUpperStarComp_id_right_hom_app]
  simp only [Category.comp_id]
private lemma named_compositor
    (A : Type (u + 1)) [CommRing A] {X Y Z : Scheme.{u}}
    (r : X ⟶ Y) (v : Y ⟶ Z) (k : X ⟶ Z) (e : k = r ≫ v) :
    eqToIso (congrArg (ordinaryFinitePullback A) e) ≪≫
        leftDerivedUpperStarComp (ModuleCat.{u + 1} A) r v =
      leftDerivedUpperStarComp (ModuleCat.{u + 1} A) r v k e := by
  subst k
  simp only [eqToIso_refl, Iso.refl_trans]

private lemma square_iso_calculation
    {C D : Type*} [Category C] [Category D] {F G H K : C ⥤ D}
    (a : F ≅ K) (b : G ≅ H) (c : F ≅ H) (e : F = G)
    (h : eqToIso e ≪≫ b = c) :
    a.symm ≪≫ eqToIso e ≪≫ b = (c.symm ≪≫ a).symm := by
  rw [h, Iso.trans_symm, Iso.symm_symm_eq]

private lemma inverse_square_comparison
    (A : Type (u + 1)) [CommRing A] {X X' Y Y' : Scheme.{u}}
    (q : X' ⟶ X) (r : X' ⟶ Y') (p : X ⟶ Y) (v : Y' ⟶ Y)
    (sq : CommSq q r p v) :
    (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) q p).symm ≪≫
      eqToIso (congrArg (ordinaryFinitePullback A) sq.w) ≪≫
      leftDerivedUpperStarComp (ModuleCat.{u + 1} A) r v =
    (derivedSquareUpperStarIso (ModuleCat.{u + 1} A) sq).symm := by
  delta derivedSquareUpperStarIso
  exact square_iso_calculation
    (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) q p)
    (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) r v)
    (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) r v (q ≫ p) sq.w)
    (congrArg (ordinaryFinitePullback A) sq.w)
    (named_compositor A r v (q ≫ p) sq.w)


private lemma tower_map_id (S : Scheme.{u}) (d : ℕ) :
    affineTraceMap (𝟙 S) d = 𝟙 _ := by
  induction d with
  | zero => rfl
  | succ d ih =>
    change AffineSpace.map PUnit.{u + 1} (affineTraceMap (𝟙 S) d) = 𝟙 _
    rw [ih, AffineSpace.map_id]

private theorem app_three_then
    {C D : Type*} [Category C] [Category D] {F G H I : C ⥤ D}
    (a : F ≅ G) (b : G ≅ H) (c : H ≅ I) (e : F ≅ I)
    (he : a ≪≫ b ≪≫ c = e) (X : C) {Y : D} (d : I.obj X ≅ Y) :
    a.app X ≪≫ b.app X ≪≫ c.app X ≪≫ d = e.app X ≪≫ d := by
  rw [← he]
  simp only [NatIso.trans_app, Iso.trans_assoc]

private theorem prefix_of_coefficient_eq
    {C D : Type*} [Category C] [Category D] (R : C ⥤ D)
    {L M : C} (c c' : L ≅ M) (h : c = c')
    {X Y : D} (a : X ⟶ R.obj L) (b : R.obj M ⟶ Y) :
    a ≫ R.map c.hom ≫ b = a ≫ R.map c'.hom ≫ b := by
  rw [h]

private lemma chart_prefix_cartesian (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (t : OrdinaryFiniteTwistTransport A N hA)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ)
    (F : S.Modules) [F.IsFiniteLocallyFreeOfRank d]
    [IsAffineHom (VectorBundleZeroSection.π S d F)]
    [LocallyOfFiniteType (VectorBundleZeroSection.π S d F)] (V : S.Opens)
    [IsNoetherian V.toScheme] (e : VectorBundleZeroSection.Trivialization S d F V) :
    vectorIntegrationCartesianPrefix N hN A hA t (VectorBundleZeroSection.π S d F)
      V.ι (affineTracePullbackInvertible N V.ι hS) d
      (vectorIntegrationChart S d F V e) (vectorIntegrationChart_isPullback S d F V e)
      (affineLinearBaseCoefficient A N hA S d)
      (vectorIntegrationBaseCoefficientPullback A N hA t V.ι hS d) =
    (rightDerivedLowerShriekBaseChangeMap A
      (vectorIntegrationChart_isPullback S d F V e)).app
        (vectorIntegrationCoefficient A N hA S d F) ≫
      (rightDerivedLowerShriek (ModuleCat.{u + 1} A)
        (affineTraceProjection V.toScheme d)).map
        (vectorIntegrationChartCoefficient A N hA t S hS d F V e).hom ≫
      (affineLinearCompactComparison N hN A hA V.toScheme
        (affineTracePullbackInvertible N V.ι hS) d).inv := by
  let := (vectorIntegration_geometry S d F).1
  let := (vectorIntegration_geometry S d F).2.1
  have hc : vectorIntegrationCartesianCoefficient A N hA t
      (VectorBundleZeroSection.π S d F) V.ι
      (affineTracePullbackInvertible N V.ι hS) d (vectorIntegrationChart S d F V e)
      (vectorIntegrationChart_isPullback S d F V e)
      (affineLinearBaseCoefficient A N hA S d)
      (vectorIntegrationBaseCoefficientPullback A N hA t V.ι hS d) =
      vectorIntegrationChartCoefficient A N hA t S hS d F V e := by
    exact (app_three_then
      (leftDerivedUpperStarComp (ModuleCat.{u + 1} A)
        (vectorIntegrationChart S d F V e) (VectorBundleZeroSection.π S d F)).symm
      (eqToIso (congrArg (ordinaryFinitePullback A)
        (vectorIntegrationChart_isPullback S d F V e).w))
      (leftDerivedUpperStarComp (ModuleCat.{u + 1} A)
        (affineTraceProjection V.toScheme d) V.ι)
      (derivedSquareUpperStarIso (ModuleCat.{u + 1} A)
        (vectorIntegrationChart_isPullback S d F V e).toCommSq).symm
      (inverse_square_comparison A (vectorIntegrationChart S d F V e)
        (affineTraceProjection V.toScheme d) (VectorBundleZeroSection.π S d F) V.ι
        (vectorIntegrationChart_isPullback S d F V e).toCommSq)
      (affineLinearBaseCoefficient A N hA S d)
      ((ordinaryFinitePullback A (affineTraceProjection V.toScheme d)).mapIso
          (vectorIntegrationBaseCoefficientPullback A N hA t V.ι hS d) ≪≫
        (affineLinearCoefficientDescent A N hA t V.toScheme
          (affineTracePullbackInvertible N V.ι hS) d).symm)).symm
  exact prefix_of_coefficient_eq
    (rightDerivedLowerShriek (ModuleCat.{u + 1} A) (affineTraceProjection V.toScheme d))
    _ _ hc _ _


private theorem frame_iso_prefix (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) (d d' : ℕ) (hd : d' = d)
    (H K : S.Modules) [H.IsFiniteLocallyFreeOfRank d] [K.IsFiniteLocallyFreeOfRank d']
    (m : (Scheme.Modules.pullback (𝟙 S)).obj K ≅ H)
    (v : VectorBundleZeroSection.scheme S d H ⟶ VectorBundleZeroSection.scheme S d' K)
    (sqv : IsPullback v (VectorBundleZeroSection.π S d H)
      (VectorBundleZeroSection.π S d' K) (𝟙 S))
    (hv : VectorTraceGeometry.MapSpec (𝟙 S) d' d K H
      ((Scheme.Modules.pullbackPushforwardAdjunction (𝟙 S)).homEquiv _ _ m.hom) v)
    (c : (ordinaryFinitePullback A v).obj
        (vectorIntegrationCoefficient A N hA S d' K) ≅
      vectorIntegrationCoefficient A N hA S d H)
    (hc : c =
      (leftDerivedUpperStarComp (ModuleCat.{u + 1} A)
        v
        (VectorBundleZeroSection.π S d' K)
        (VectorBundleZeroSection.π S d H)
        (by simpa only [Category.comp_id] using
          sqv.w.symm)).symm.app _ ≪≫
      (ordinaryFinitePullback A
        (VectorBundleZeroSection.π S d H)).mapIso
        (eqToIso (congrArg (affineLinearBaseCoefficient A N hA S) hd)))
    (b : (ordinaryFinitePullback A (𝟙 S)).obj
        (vectorIntegrationSource A N hA S d' K) ≅
      vectorIntegrationSource A N hA S d H)
    (hb : b.hom =
      (rightDerivedLowerShriekBaseChangeMap A
        sqv).app
        (vectorIntegrationCoefficient A N hA S d' K) ≫
      (rightDerivedLowerShriek (ModuleCat.{u + 1} A)
        (VectorBundleZeroSection.π S d H)).map c.hom)
    (t : OrdinaryFiniteTwistTransport A N hA)
    (V : S.Opens)
    (e : VectorBundleZeroSection.Trivialization S d H V)
    (e' : VectorBundleZeroSection.Trivialization S d' K V) :
    letI : TopologicalSpace.NoetherianSpace V.toScheme :=
      V.ι.isOpenEmbedding.isInducing.noetherianSpace
    letI : IsNoetherian V.toScheme :=
      { toIsLocallyNoetherian := inferInstance
        isCompact_univ := TopologicalSpace.NoetherianSpace.isCompact _ }
    let Q := fun d ↦ (affineTraceLeft A V.toScheme d).obj
      ((affineTraceRight A N hA V.toScheme d).obj (ordinaryFiniteUnit A V.toScheme))
    let B := fun (d : ℕ) (H : S.Modules) [H.IsFiniteLocallyFreeOfRank d]
      (f : VectorBundleZeroSection.Trivialization S d H V) ↦
        (rightDerivedLowerShriekBaseChangeMap A
          (vectorIntegrationChart_isPullback S d H V f)).app
            (vectorIntegrationCoefficient A N hA S d H) ≫
        (rightDerivedLowerShriek (ModuleCat.{u + 1} A)
          (affineTraceProjection V.toScheme d)).map
            (vectorIntegrationChartCoefficient A N hA t S hS d H V f).hom ≫
        (affineLinearCompactComparison N hN A hA V.toScheme
          (affineTracePullbackInvertible N V.ι hS) d).inv
    ∃ (g : Matrix.GeneralLinearGroup (Fin d') Γ(V.toScheme, ⊤))
      (sq : IsPullback (affineTraceLinearMap V.toScheme d' g)
        (affineTraceProjection V.toScheme d')
        (affineTraceProjection V.toScheme d') (𝟙 V.toScheme)),
      (ordinaryFinitePullback A V.ι).map
          (b.inv ≫ (affineLinearPullbackId A S).hom.app
            (vectorIntegrationSource A N hA S d' K)) ≫
        B d' K e' =
      B d H e ≫
        eqToHom (congrArg Q hd.symm) ≫
        affineLinearTraceAction N hN A hA t V.toScheme
          (affineTracePullbackInvertible N V.ι hS) d'
          (affineTraceLinearMap V.toScheme d' g) sq  := by
  subst d'
  let : TopologicalSpace.NoetherianSpace V.toScheme :=
    V.ι.isOpenEmbedding.isInducing.noetherianSpace
  let : IsNoetherian V.toScheme :=
    { toIsLocallyNoetherian := inferInstance
      isCompact_univ := TopologicalSpace.NoetherianSpace.isCompact _ }
  let := (vectorIntegration_geometry S d H).1
  let := (vectorIntegration_geometry S d H).2.1
  let := (vectorIntegration_geometry S d H).2.2
  let := (vectorIntegration_geometry S d K).1
  let := (vectorIntegration_geometry S d K).2.1
  let := (vectorIntegration_geometry S d K).2.2
  obtain ⟨g, hg⟩ := linear_coordinates (𝟙 S) d K H m v hv V e' V e V.toScheme V.ι
    (𝟙 V.toScheme) (𝟙 V.toScheme) (Category.id_comp _) (by simp)
  simp only [tower_map_id, Category.id_comp] at hg
  let p := VectorBundleZeroSection.π S d K
  let p' := VectorBundleZeroSection.π S d H
  let q := vectorIntegrationChart S d H V e
  let q' := vectorIntegrationChart S d K V e'
  let sq := vectorIntegrationChart_isPullback S d H V e
  let sq' := vectorIntegrationChart_isPullback S d K V e'
  let sqZ : IsPullback (q ≫ v) (affineTraceProjection V.toScheme d) p V.ι := by
    simpa only [Category.comp_id] using sq.paste_horiz sqv
  let L := affineLinearBaseCoefficient A N hA S d
  let beta := vectorIntegrationBaseCoefficientPullback A N hA t V.ι hS d
  let hV := affineTracePullbackInvertible N V.ι hS
  let BH := vectorIntegrationCartesianPrefix N hN A hA t p' V.ι hV d q sq L beta
  let BK := vectorIntegrationCartesianPrefix N hN A hA t p V.ι hV d q' sq' L beta
  let PZ := vectorIntegrationCartesianPrefix N hN A hA t p V.ι hV d (q ≫ v) sqZ L beta
  have hq : q' = affineTraceLinearMap V.toScheme d g⁻¹ ≫ (q ≫ v) := by
    rw [hg]
    rw [← Category.assoc, linear_comp, mul_inv_cancel, linear_one, Category.id_comp]
  let sa := affineTraceLinearMap_isPullback V.toScheme d g⁻¹
  have haction := vectorIntegrationCartesianPrefix_action N hN A hA t p V.ι hV d
    (q ≫ v) q' sqZ sq' (affineTraceLinearMap V.toScheme d g⁻¹) sa hq L beta
  change BK = PZ ≫ affineLinearTraceAction N hN A hA t V.toScheme hV d
    (affineTraceLinearMap V.toScheme d g⁻¹) sa at haction
  have hc0 : c = (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) v p p'
      (sqv.w.trans (Category.comp_id _)).symm).symm.app L := by
    rw [hc]
    simp only [eqToIso_refl, Functor.mapIso_refl]
    exact Iso.trans_refl _
  have hpaste := vectorIntegrationCartesianPrefix_baseChange N hN A hA t p p' (𝟙 S)
    v sqv hS d V.ι hV q sq V.ι (Category.comp_id _).symm (q ≫ v) rfl sqZ
  dsimp only at hpaste
  change b.hom = (rightDerivedLowerShriekBaseChangeMap A sqv).app
    ((ordinaryFinitePullback A p).obj L) ≫
      (rightDerivedLowerShriek (ModuleCat.{u + 1} A) p').map c.hom at hb
  rw [identity_square_coefficient A N hA t p p' v sqv hS d, ← hc0, ← hb] at hpaste
  rw [comp_id_right_inv] at hpaste
  change (ordinaryFinitePullback A V.ι).map b.hom ≫ BH =
    (ordinaryFinitePullback A V.ι).map
      ((leftDerivedUpperStarId (ModuleCat.{u + 1} A) S).hom.app
        (vectorIntegrationSource A N hA S d K)) ≫ PZ at hpaste
  let P := ordinaryFinitePullback A V.ι
  have hfinish : P.map (b.inv ≫
      (leftDerivedUpperStarId (ModuleCat.{u + 1} A) S).hom.app _) ≫ BK =
      BH ≫ affineLinearTraceAction N hN A hA t V.toScheme hV d
        (affineTraceLinearMap V.toScheme d g⁻¹) sa := by
    apply (cancel_epi (P.map b.hom)).mp
    rw [haction]
    simp only [Functor.map_comp, Category.assoc]
    rw [← Functor.map_comp_assoc, b.hom_inv_id, CategoryTheory.Functor.map_id, Category.id_comp]
    simpa only [P, Category.assoc] using congrArg (fun z ↦ z ≫
      affineLinearTraceAction N hN A hA t V.toScheme hV d
        (affineTraceLinearMap V.toScheme d g⁻¹) sa) hpaste.symm
  refine ⟨g⁻¹, sa, ?_⟩
  have hid : affineLinearPullbackId A S =
      leftDerivedUpperStarId (ModuleCat.{u + 1} A) S := by
    simp [affineLinearPullbackId, leftDerivedUpperStarId, Functor.leftDerivedFunctorNatIso,
      leftDerivedUpperStarIsoMapDerivedCategory]
  simpa only [P, BH, BK, p, p', q, q', sq, sq', L, beta,
    chart_prefix_cartesian, hid, eqToHom_refl, Category.id_comp] using hfinish

/-- The two chart source comparisons differ by an invertible linear action.
Source: blueprint latest, vector-bundle purity proof paragraph 2, simultaneous
trivializations; local swap proof Steps 1--2.
(blueprint: lem-pur-vector-integration-swap-chart-prefix).

Proof: restrict the generator map of biproduct braiding to V. In the supplied frames
it gives an invertible matrix, with inverse given by the reverse braiding. After the
rank identification this matrix induces exactly the comparison of the two inverse
coordinate charts: check on each degree-one generator and use the symmetric-algebra
universal property. Its square over the identity of V is Cartesian. Paste the chart
squares with the restricted swap square. Horizontal compact-support exchange pasting
and naturality give the displayed relation between their exchange factors. The
inverse-image compositor is associative and unital; the normalized Tate pullbacks
respect composition. Thus the coefficient factors agree with precisely c, without
an additional scalar, and the constant identity comparison is affineLinearPullbackId.
The bounded/unbounded tower comparisons conjugate the remaining exchange to the
specified affineLinearTraceAction. Cancel the invertible exchange b to obtain the
formula. There is no counit or projective-line datum in this assertion. Empty opens,
rank zero (empty matrices), and the zero coefficient ring need no separate choices.
-/
theorem vectorIntegration_swap_chart_prefix (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) (r s : ℕ)
    (F G : S.Modules) [F.IsFiniteLocallyFreeOfRank r] [G.IsFiniteLocallyFreeOfRank s]
    (c : (ordinaryFinitePullback A (VectorTraceGeometry.swap S r s F G)).obj
        (vectorIntegrationCoefficient A N hA S (s + r) (VectorTraceGeometry.sum S G F)) ≅
      vectorIntegrationCoefficient A N hA S (r + s) (VectorTraceGeometry.sum S F G))
    (hc : c =
      (leftDerivedUpperStarComp (ModuleCat.{u + 1} A)
        (VectorTraceGeometry.swap S r s F G)
        (VectorBundleZeroSection.π S (s + r) (VectorTraceGeometry.sum S G F))
        (VectorBundleZeroSection.π S (r + s) (VectorTraceGeometry.sum S F G))
        (by simpa only [Category.comp_id] using
          (VectorTraceGeometry.swap_isPullback S r s F G).w.symm)).symm.app _ ≪≫
      (ordinaryFinitePullback A
        (VectorBundleZeroSection.π S (r + s) (VectorTraceGeometry.sum S F G))).mapIso
        (eqToIso (congrArg (affineLinearBaseCoefficient A N hA S) (Nat.add_comm s r))))
    (b : (ordinaryFinitePullback A (𝟙 S)).obj
        (vectorIntegrationSource A N hA S (s + r) (VectorTraceGeometry.sum S G F)) ≅
      vectorIntegrationSource A N hA S (r + s) (VectorTraceGeometry.sum S F G))
    (hb : b.hom =
      (rightDerivedLowerShriekBaseChangeMap A
        (VectorTraceGeometry.swap_isPullback S r s F G)).app
        (vectorIntegrationCoefficient A N hA S (s + r) (VectorTraceGeometry.sum S G F)) ≫
      (rightDerivedLowerShriek (ModuleCat.{u + 1} A)
        (VectorBundleZeroSection.π S (r + s) (VectorTraceGeometry.sum S F G))).map c.hom)
    (t : OrdinaryFiniteTwistTransport A N hA)
    (V : S.Opens)
    (e : VectorBundleZeroSection.Trivialization S (r + s) (VectorTraceGeometry.sum S F G) V)
    (e' : VectorBundleZeroSection.Trivialization S (s + r) (VectorTraceGeometry.sum S G F) V) :
    letI : TopologicalSpace.NoetherianSpace V.toScheme :=
      V.ι.isOpenEmbedding.isInducing.noetherianSpace
    letI : IsNoetherian V.toScheme :=
      { toIsLocallyNoetherian := inferInstance
        isCompact_univ := TopologicalSpace.NoetherianSpace.isCompact _ }
    let Q := fun d ↦ (affineTraceLeft A V.toScheme d).obj
      ((affineTraceRight A N hA V.toScheme d).obj (ordinaryFiniteUnit A V.toScheme))
    let B := fun (d : ℕ) (H : S.Modules) [H.IsFiniteLocallyFreeOfRank d]
      (f : VectorBundleZeroSection.Trivialization S d H V) ↦
        (rightDerivedLowerShriekBaseChangeMap A
          (vectorIntegrationChart_isPullback S d H V f)).app
            (vectorIntegrationCoefficient A N hA S d H) ≫
        (rightDerivedLowerShriek (ModuleCat.{u + 1} A)
          (affineTraceProjection V.toScheme d)).map
            (vectorIntegrationChartCoefficient A N hA t S hS d H V f).hom ≫
        (affineLinearCompactComparison N hN A hA V.toScheme
          (affineTracePullbackInvertible N V.ι hS) d).inv
    ∃ (g : Matrix.GeneralLinearGroup (Fin (s + r)) Γ(V.toScheme, ⊤))
      (sq : IsPullback (affineTraceLinearMap V.toScheme (s + r) g)
        (affineTraceProjection V.toScheme (s + r))
        (affineTraceProjection V.toScheme (s + r)) (𝟙 V.toScheme)),
      (ordinaryFinitePullback A V.ι).map
          (b.inv ≫ (affineLinearPullbackId A S).hom.app
            (vectorIntegrationSource A N hA S (s + r) (VectorTraceGeometry.sum S G F))) ≫
        B (s + r) (VectorTraceGeometry.sum S G F) e' =
      B (r + s) (VectorTraceGeometry.sum S F G) e ≫
        eqToHom (congrArg Q (Nat.add_comm r s)) ≫
        affineLinearTraceAction N hN A hA t V.toScheme
          (affineTracePullbackInvertible N V.ι hS) (s + r)
          (affineTraceLinearMap V.toScheme (s + r) g) sq  := by
  let H := VectorTraceGeometry.sum S F G
  let K := VectorTraceGeometry.sum S G F
  let j : K ≅ H := biprod.braiding G F
  let m : (Scheme.Modules.pullback (𝟙 S)).obj K ≅ H :=
    (Scheme.Modules.pullbackId S).app K ≪≫ j
  have hm : ((Scheme.Modules.pullbackPushforwardAdjunction (𝟙 S)).homEquiv K H) m.hom =
      j.hom ≫ (Scheme.Modules.pushforwardId S).inv.app H := by
    change ((Scheme.Modules.pullbackPushforwardAdjunction (𝟙 S)).homEquiv K H)
      ((Scheme.Modules.pullbackId S).hom.app K ≫ j.hom) = _
    rw [mate_homEquiv (Adjunction.id : 𝟭 S.Modules ⊣ 𝟭 S.Modules)
      (Scheme.Modules.pullbackPushforwardAdjunction (𝟙 S))
      (Scheme.Modules.pullbackId S).hom j.hom,
      Scheme.Modules.conjugateEquiv_pullbackId_hom]
    change (𝟙 K ≫ j.hom) ≫ (Scheme.Modules.pushforwardId S).inv.app H = _
    rw [Category.id_comp]
  have hv : VectorTraceGeometry.MapSpec (𝟙 S) (s + r) (r + s) K H
      ((Scheme.Modules.pullbackPushforwardAdjunction (𝟙 S)).homEquiv _ _ m.hom)
      (VectorTraceGeometry.swap S r s F G) := by
    rw [hm]
    refine ⟨(VectorTraceGeometry.swap_isPullback S r s F G).w, ?_⟩
    intro U x
    exact VectorTraceGeometry.purityBundleMap_generators S (r + s) (s + r) H K
      j.hom U x
  exact frame_iso_prefix N hN A hA S hS (r + s) (s + r) (Nat.add_comm s r) H K m
    (VectorTraceGeometry.swap S r s F G) (VectorTraceGeometry.swap_isPullback S r s F G)
    hv c hc b hb t V e e'


end AlgebraicGeometry.Etale
