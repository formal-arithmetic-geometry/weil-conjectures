/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.VectorTraceGeometry.VectorTraceGeometry
import WeilConjectures.AlgebraicGeometry.Vector.VectorIntegrationPulledChartTransport
import WeilConjectures.AlgebraicGeometry.Vector.VectorIntegrationCartesianPrefixBaseChange
import WeilConjectures.AlgebraicGeometry.Vector.VectorIntegrationBaseChangeCoordinates
import WeilConjectures.AlgebraicGeometry.Vector.VectorIntegrationOverlapChartPrefix
import WeilConjectures.AlgebraicGeometry.Affine.Space.AffineSpaceLinearTraceInvariance
import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinaryFiniteP1DatumUniqueness
import WeilConjectures.AlgebraicGeometry.Affine.Trace.AffineTraceTowerCounitBaseChange

/-! # Geometric local trace exchange before arbitrary-arrow substitution -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Etale

attribute [local irreducible] rightDerivedLowerShriek affineLinearCompactComparison
  affineLinearCoefficientDescent affineLinearBaseCoefficient
  leftDerivedUpperStarComp derivedSquareUpperStarIso upperStar Functor.leftDerivedFunctor
attribute [local implicit_reducible] Scheme.Modules Scheme.Modules.Hom Scheme.Modules.instCategory
  vectorIntegrationCoefficient vectorIntegrationSource

private theorem app_trans_tail
    {C D : Type*} [Category C] [Category D] {F G H I : C ⥤ D}
    (a : F ≅ G) (b : G ≅ H) (c : H ≅ I) (e : F ≅ I)
    (he : a ≪≫ b ≪≫ c = e) (X : C) {Y : D} (d : I.obj X ≅ Y) :
    a.app X ≪≫ b.app X ≪≫ c.app X ≪≫ d = e.app X ≪≫ d := by
  rw [← he]
  simp only [NatIso.trans_app, Iso.trans_assoc]

private theorem paste_with_source
    {C D E : Type*} [Category C] [Category D] [Category E]
    (P : C ⥤ D) (R : E ⥤ C) {K : C} {M M' : E}
    (e : K ⟶ R.obj M) (c c' : M ≅ M') (hc : c = c')
    (b : K ⟶ R.obj M') (hb : b = e ≫ R.map c.hom)
    {Q : D} (pt : P.obj (R.obj M') ⟶ Q) (z : P.obj K ⟶ Q)
    (hp : P.map (e ≫ R.map c'.hom) ≫ pt = z) :
    P.map b ≫ pt = z := by
  rw [hb, hc]
  exact hp

private theorem map_trace
    {C D : Type*} [Category C] [Category D] (P : C ⥤ D)
    {X Y Z : C} {V W B : D} (l : V ⟶ W) (c : W ⟶ P.obj X)
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z) (u : P.obj Z ⟶ B)
    (hh : h = f ≫ g) :
    l ≫ c ≫ P.map h ≫ u = l ≫ c ≫ P.map f ≫ P.map g ≫ u := by
  rw [hh, P.map_comp]
  simp only [Category.assoc]

private theorem finish_prefixes
    {C : Type*} [Category C] {X Y Z U V R O Q B : C}
    (l : X ⟶ Y) (cT : Y ⟶ Z) (bT : Z ⟶ U) (eT : U ⟶ Q)
    (cS : V ⟶ R) (bS : R ⟶ O) (eS : O ⟶ Q)
    (c : X ⟶ V) (pt : Y ⟶ Q) (ps pz : V ⟶ Q)
    (rho : Q ⟶ Q) (eps : Q ⟶ B) (tauT : U ⟶ B) (tauS : O ⟶ B)
    (hT : cT ≫ bT ≫ eT = pt) (hS : cS ≫ bS ≫ eS = ps)
    (hpaste : l ≫ pt = c ≫ pz) (haction : pz = ps ≫ rho)
    (hi : rho ≫ eps = eps) (htT : eT ≫ eps = tauT) (htS : eS ≫ eps = tauS) :
    l ≫ cT ≫ bT ≫ tauT = c ≫ cS ≫ bS ≫ tauS := by
  rw [← htT, ← htS, reassoc_of% hT, reassoc_of% hS, reassoc_of% hpaste, haction]
  simp only [Category.assoc]
  rw [hi]

private theorem tower_unit_counit (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (t : OrdinaryFiniteTwistTransport A N hA)
    (D : ∀ (X : Scheme.{u}) [IsNoetherian X] (hX : IsUnit (N : Γ(X, ⊤))),
      OrdinaryFiniteP1Datum A N hA t X hX)
    (hD : OrdinaryFiniteP1BaseChange A N hA t D)
    {T U : Scheme.{u}} [IsNoetherian T] [IsNoetherian U]
    (p : T ⟶ U) (hU : IsUnit (N : Γ(U, ⊤))) (d : ℕ) :
    affineTraceUnitBaseChange A N hA t p hU d ≫
        affineTraceCounit A N hA t D T (affineTracePullbackInvertible N p hU) d =
      (ordinaryFinitePullback A p).map (affineTraceCounit A N hA t D U hU d) ≫
        (ordinaryFiniteUnitPullback A p).hom := by
  have hn := (affineTraceAdjunction A N hA t D T
    (affineTracePullbackInvertible N p hU) d).counit.naturality
      (ordinaryFiniteUnitPullback A p).hom
  simp only [Functor.comp_map, Functor.id_map] at hn
  unfold affineTraceUnitBaseChange affineTraceCounit
  simp only [Category.assoc]
  rw [hn]
  simpa only [Category.assoc] using congrArg
    (fun f ↦ f ≫ (ordinaryFiniteUnitPullback A p).hom)
    (affineTraceTowerCounit_baseChange A N hN hA t D hD p hU d (ordinaryFiniteUnit A U))

private theorem chart_trace_eq_prefix (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (t : OrdinaryFiniteTwistTransport A N hA)
    (D : ∀ (X : Scheme.{u}) [IsNoetherian X] (hX : IsUnit (N : Γ(X, ⊤))),
      OrdinaryFiniteP1Datum A N hA t X hX)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ)
    (F : SheafOfModules.{u} S.ringCatSheaf) [F.IsFiniteLocallyFreeOfRank d]
    (V : S.Opens) [IsNoetherian V.toScheme]
    (e : VectorBundleZeroSection.Trivialization S d F V) :
    vectorIntegrationLocalTrace N hN A hA t D S hS d F V e =
      vectorIntegrationChartPrefix N hN A hA t S hS d F V e ≫
        affineTraceCounit A N hA t D V.toScheme
          (affineTracePullbackInvertible N V.ι hS) d := by
  unfold vectorIntegrationLocalTrace vectorIntegrationChartPrefix
  simp only [Category.assoc]

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

/--
The geometric local trace exchange used by the degree-zero base-change wrapper.

Proof: paste the Cartesian exchange square for the source bundle with the coefficient
comparison `c`, then restrict both frame charts to `W`.  The affine counit base-change
identity over `W` identifies the two resulting prefixes.  Substitution of the two
frame equations and naturality of the constant-unit pullback gives the displayed
formula.  This is the geometric core; the wrapper separately handles arbitrary
arrows `kS` and `kT` by pullback composition.
(blueprint: lem-pur-vector-integration-base-local-trace). -/
theorem vectorIntegration_baseChange_local_trace
    (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (t : OrdinaryFiniteTwistTransport A N hA)
    {S T : Scheme.{u}} [IsNoetherian S] [IsNoetherian T]
    (f : T ⟶ S) (hS : IsUnit (N : Γ(S, ⊤))) (r : ℕ) (F : S.Modules)
    [F.IsFiniteLocallyFreeOfRank r]
    (c : (ordinaryFinitePullback A (VectorTraceGeometry.baseChange f r F)).obj
        (vectorIntegrationCoefficient A N hA S r F) ≅
      vectorIntegrationCoefficient A N hA T r ((Scheme.Modules.tensorPullback f).obj F))
    (hc : c =
      (leftDerivedUpperStarComp (ModuleCat.{u + 1} A)
        (VectorTraceGeometry.baseChange f r F) (VectorBundleZeroSection.π S r F)).symm.app _ ≪≫
      (eqToIso (congrArg (ordinaryFinitePullback A)
        (VectorTraceGeometry.baseChange_isPullback f r F).w)).app _ ≪≫
      (leftDerivedUpperStarComp (ModuleCat.{u + 1} A)
        (VectorBundleZeroSection.π T r ((Scheme.Modules.tensorPullback f).obj F)) f).app _ ≪≫
      (ordinaryFinitePullback A
        (VectorBundleZeroSection.π T r ((Scheme.Modules.tensorPullback f).obj F))).mapIso
        (vectorIntegrationBaseCoefficientPullback A N hA t f hS r))
    (b : (ordinaryFinitePullback A f).obj (vectorIntegrationSource A N hA S r F) ≅
      vectorIntegrationSource A N hA T r ((Scheme.Modules.tensorPullback f).obj F))
    (hb : b.hom =
      (rightDerivedLowerShriekBaseChangeMap A
        (VectorTraceGeometry.baseChange_isPullback f r F)).app
        (vectorIntegrationCoefficient A N hA S r F) ≫
      (rightDerivedLowerShriek (ModuleCat.{u + 1} A)
        (VectorBundleZeroSection.π T r ((Scheme.Modules.tensorPullback f).obj F))).map c.hom)
    (D : ∀ (X : Scheme.{u}) [IsNoetherian X] (hX : IsUnit (N : Γ(X, ⊤))),
      OrdinaryFiniteP1Datum A N hA t X hX)
    (V : S.Opens) (eS : VectorBundleZeroSection.Trivialization S r F V)
    (U : T.Opens)
    (eT : VectorBundleZeroSection.Trivialization T r
      ((Scheme.Modules.tensorPullback f).obj F) U)
    (W : Scheme.{u}) [IsNoetherian W]
    (j : W ⟶ T) (a : W ⟶ U.toScheme) (g : W ⟶ V.toScheme)
    (ha : a ≫ U.ι = j) (hg : j ≫ f = g ≫ V.ι) :
    (ordinaryFinitePullback A j).map b.hom ≫
      (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) a U.ι j ha.symm).hom.app _ ≫
        (ordinaryFinitePullback A a).map
          (vectorIntegrationLocalTrace N hN A hA t D T
            (affineTracePullbackInvertible N f hS) r
            ((Scheme.Modules.tensorPullback f).obj F) U eT) ≫
        (ordinaryFiniteUnitPullback A a).hom =
      (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) j f (g ≫ V.ι) hg.symm).inv.app _ ≫
        (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) g V.ι (g ≫ V.ι) rfl).hom.app _ ≫
        (ordinaryFinitePullback A g).map
        (vectorIntegrationLocalTrace N hN A hA t D S hS r F V eS) ≫
        (ordinaryFiniteUnitPullback A g).hom := by
  let : TopologicalSpace.NoetherianSpace V.toScheme :=
    V.ι.isOpenEmbedding.isInducing.noetherianSpace
  let : IsNoetherian V.toScheme :=
    { toIsLocallyNoetherian := inferInstance
      isCompact_univ := TopologicalSpace.NoetherianSpace.isCompact _ }
  let : TopologicalSpace.NoetherianSpace U.toScheme :=
    U.ι.isOpenEmbedding.isInducing.noetherianSpace
  let : IsNoetherian U.toScheme :=
    { toIsLocallyNoetherian := inferInstance
      isCompact_univ := TopologicalSpace.NoetherianSpace.isCompact _ }
  let := (vectorIntegration_geometry S r F).1
  let := (vectorIntegration_geometry S r F).2.1
  let := (vectorIntegration_geometry S r F).2.2
  let G := (Scheme.Modules.tensorPullback f).obj F
  let := (vectorIntegration_geometry T r G).1
  let := (vectorIntegration_geometry T r G).2.1
  let := (vectorIntegration_geometry T r G).2.2
  let hT := affineTracePullbackInvertible N f hS
  let hW := affineTracePullbackInvertible N (g ≫ V.ι) hS
  let qS := affineTraceMap g r ≫ vectorIntegrationChart S r F V eS
  let qT := affineTraceMap a r ≫ vectorIntegrationChart T r G U eT
  let sqS := vectorIntegrationPulledChart_isPullback S r F V eS W g (g ≫ V.ι) rfl
  let sqT := vectorIntegrationPulledChart_isPullback T r G U eT W a j ha.symm
  let sqZ : IsPullback (qT ≫ VectorTraceGeometry.baseChange f r F)
      (affineTraceProjection W r) (VectorBundleZeroSection.π S r F) (g ≫ V.ι) := by
    simpa only [hg] using sqT.paste_horiz (VectorTraceGeometry.baseChange_isPullback f r F)
  let BS := vectorIntegrationChartPrefix N hN A hA t S hS r F V eS
  let BT := vectorIntegrationChartPrefix N hN A hA t T hT r G U eT
  let PS := vectorIntegrationCartesianPrefix N hN A hA t (VectorBundleZeroSection.π S r F)
    (g ≫ V.ι) hW r qS sqS (affineLinearBaseCoefficient A N hA S r)
    (vectorIntegrationBaseCoefficientPullback A N hA t (g ≫ V.ι) hS r)
  let PT := vectorIntegrationCartesianPrefix N hN A hA t (VectorBundleZeroSection.π T r G)
    j hW r qT sqT (affineLinearBaseCoefficient A N hA T r)
    (vectorIntegrationBaseCoefficientPullback A N hA t j hT r)
  let PZ := vectorIntegrationCartesianPrefix N hN A hA t (VectorBundleZeroSection.π S r F)
    (g ≫ V.ι) hW r (qT ≫ VectorTraceGeometry.baseChange f r F) sqZ
    (affineLinearBaseCoefficient A N hA S r)
    (vectorIntegrationBaseCoefficientPullback A N hA t (g ≫ V.ι) hS r)
  have hc' : c =
      (derivedSquareUpperStarIso (ModuleCat.{u + 1} A)
        (VectorTraceGeometry.baseChange_isPullback f r F).toCommSq).symm.app
          (affineLinearBaseCoefficient A N hA S r) ≪≫
      (ordinaryFinitePullback A (VectorBundleZeroSection.π T r G)).mapIso
        (vectorIntegrationBaseCoefficientPullback A N hA t f hS r) :=
    hc.trans (app_trans_tail _ _ _ _
      (inverse_square_comparison A (VectorTraceGeometry.baseChange f r F)
        (VectorBundleZeroSection.π T r G) (VectorBundleZeroSection.π S r F) f
        (VectorTraceGeometry.baseChange_isPullback f r F).toCommSq) _ _)
  have hpaste := vectorIntegrationCartesianPrefix_baseChange N hN A hA t
    (VectorBundleZeroSection.π S r F) (VectorBundleZeroSection.π T r G)
    f (VectorTraceGeometry.baseChange f r F)
    (VectorTraceGeometry.baseChange_isPullback f r F) hS r j hW qT sqT
    (g ≫ V.ι) hg.symm (qT ≫ VectorTraceGeometry.baseChange f r F) rfl sqZ
  dsimp only at hpaste
  have hpaste' := paste_with_source (ordinaryFinitePullback A j)
    (rightDerivedLowerShriek (ModuleCat.{u + 1} A) (VectorBundleZeroSection.π T r G))
    ((rightDerivedLowerShriekBaseChangeMap A
      (VectorTraceGeometry.baseChange_isPullback f r F)).app
      (vectorIntegrationCoefficient A N hA S r F)) c _ hc' b.hom hb PT _ hpaste
  change (ordinaryFinitePullback A j).map b.hom ≫ PT =
    (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) j f (g ≫ V.ι) hg.symm).inv.app _ ≫
      PZ at hpaste'
  have hrestS := vectorIntegration_pulled_chart_transport N hN A hA t S hS r F V eS
    W g (g ≫ V.ι) rfl
  have hrestT := vectorIntegration_pulled_chart_transport N hN A hA t T hT r G U eT
    W a j ha.symm
  change (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) g V.ι).hom.app _ ≫
    (ordinaryFinitePullback A g).map BS ≫
      affineTraceUnitBaseChange A N hA t g (affineTracePullbackInvertible N V.ι hS) r =
    PS at hrestS
  change (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) a U.ι j ha.symm).hom.app _ ≫
    (ordinaryFinitePullback A a).map BT ≫
      affineTraceUnitBaseChange A N hA t a (affineTracePullbackInvertible N U.ι hT) r =
    PT at hrestT
  obtain ⟨H, hH⟩ := vectorIntegration_baseChange_coordinates f r F V eS U eT W j a g ha hg
  have haction := vectorIntegrationCartesianPrefix_action N hN A hA t
    (VectorBundleZeroSection.π S r F) (g ≫ V.ι) hW r qS
    (qT ≫ VectorTraceGeometry.baseChange f r F) sqS sqZ
    (affineTraceLinearMap W r H) (affineTraceLinearMap_isPullback W r H) hH
    (affineLinearBaseCoefficient A N hA S r)
    (vectorIntegrationBaseCoefficientPullback A N hA t (g ≫ V.ι) hS r)
  change PZ = PS ≫ affineLinearTraceAction N hN A hA t W hW r
    (affineTraceLinearMap W r H) (affineTraceLinearMap_isPullback W r H) at haction
  obtain ⟨sqH, hInv⟩ := affineSpaceLinearTraceInvariance N hN A hA t D W hW r H
  have hD : OrdinaryFiniteP1BaseChange A N hA t D :=
    ordinaryFiniteP1BaseChange_of_normalization N hN A hA t D
  have hunitS := tower_unit_counit N hN A hA t D hD g
    (affineTracePullbackInvertible N V.ι hS) r
  have hunitT := tower_unit_counit N hN A hA t D hD a
    (affineTracePullbackInvertible N U.ι hT) r
  have htS := chart_trace_eq_prefix N hN A hA t D S hS r F V eS
  have htT := chart_trace_eq_prefix N hN A hA t D T hT r G U eT
  calc
    _ = (ordinaryFinitePullback A j).map b.hom ≫
        (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) a U.ι j ha.symm).hom.app _ ≫
        (ordinaryFinitePullback A a).map BT ≫
        (ordinaryFinitePullback A a).map
          (affineTraceCounit A N hA t D U.toScheme
            (affineTracePullbackInvertible N U.ι hT) r) ≫
        (ordinaryFiniteUnitPullback A a).hom :=
      map_trace (ordinaryFinitePullback A a) _ _ _ _ _ _ htT
    _ = (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) j f (g ≫ V.ι) hg.symm).inv.app _ ≫
        (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) g V.ι).hom.app _ ≫
        (ordinaryFinitePullback A g).map BS ≫
        (ordinaryFinitePullback A g).map
          (affineTraceCounit A N hA t D V.toScheme
            (affineTracePullbackInvertible N V.ι hS) r) ≫
        (ordinaryFiniteUnitPullback A g).hom :=
      finish_prefixes _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
        hrestT hrestS hpaste' haction hInv hunitT hunitS
    _ = _ := (map_trace (ordinaryFinitePullback A g) _ _ _ _ _ _ htS).symm

end AlgebraicGeometry.Etale
