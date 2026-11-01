/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.VectorTraceScalar.VectorTraceScalarData
import WeilConjectures.AlgebraicGeometry.Scalar.ScalarPullbackComposition
import WeilConjectures.AlgebraicGeometry.Etale.Scalar.EtaleScalarPullbackTensorCoherence
import WeilConjectures.SixFunctors.Etale.Derived.SupportsBaseChange
import WeilConjectures.AlgebraicGeometry.VectorTraceScalar.FiniteTateScalarPullbackSquare
import WeilConjectures.AlgebraicGeometry.Etale.Scalar.EtaleScalarPullbackUnitCoherence
import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinaryChartUnitNormalization
import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinaryFiniteSingleUnitPullback
import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinaryChartCompactScalar

/-! Scalar compatibility of vector integration on a trivializing open.

The proof transports the ordered coefficient and compact-support squares, then
applies the affine trace equation over that open.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option maxRecDepth 4096
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open WeilConjectures.PurityFiniteSetting
namespace AlgebraicGeometry.Etale.VectorTraceScalar

variable {A B : Type (u + 1)} [CommRing A] [CommRing B]

attribute [local irreducible] Functor.leftAdjoint Functor.rightAdjoint
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor Functor.mapDerivedCategory
  upperStar lowerStar ProEtale.pbcFixedScalarExtension
  HasDerivedCategory.ofIsGrothendieckAbelian HasDerivedCategory.ofHasKInjectiveResolutions

attribute [local implicit_reducible] derivedTensorRight derivedTensorRightFunctor
  affineLinearBaseCoefficient ordinaryFiniteTwistedPullback Scheme.Modules affineTraceTower
  affineTraceProjection vectorIntegrationCoefficient vectorIntegrationSource rightDerivedLowerShriek

set_option linter.auxLemma false in
attribute [local instance 100000] DerivedCategoryModule._proof_1 DerivedCategoryModule._proof_2

-- Tensor and inverse-image maps with both coefficient arrows explicit.
@[reassoc]
private theorem tensorMap_pre (φ : A →+* B) (T : Scheme.{u})
    {K L M P : DerivedCategoryModule A T} {K' L' : DerivedCategoryModule B T}
    (e : K ⟶ M) (v : L ⟶ P)
    (b : (scalarExtension φ T).obj M ⟶ K')
    (l : (scalarExtension φ T).obj P ⟶ L') :
    (scalarExtension φ T).map (e ⊗ₘ v) ≫ tensorMap φ T b l =
      tensorMap φ T ((scalarExtension φ T).map e ≫ b)
        ((scalarExtension φ T).map v ≫ l) := by
  have hn := (ExceptionalCoefficients.tensorIso φ T).hom.naturality (Prod.mkHom e v)
  change (scalarExtension φ T).map (e ⊗ₘ v) ≫ _ =
    _ ≫ ((scalarExtension φ T).map e ⊗ₘ (scalarExtension φ T).map v) at hn
  simp only [tensorMap, ← tensorHom_comp_tensorHom, ← Category.assoc]
  rw [hn]

@[reassoc]
private theorem pullMap_pre (φ : A →+* B) {X Y : Scheme.{u}} (f : X ⟶ Y)
    {K M : DerivedCategoryModule A Y} {K' : DerivedCategoryModule B Y}
    (e : K ⟶ M) (b : (scalarExtension φ Y).obj M ⟶ K') :
    (scalarExtension φ X).map ((ordinaryFinitePullback A f).map e) ≫ pullMap φ f b =
      pullMap φ f ((scalarExtension φ Y).map e ≫ b) := by
  have hn := (scalarPullbackIso φ f).inv.naturality e
  change (scalarExtension φ X).map ((ordinaryFinitePullback A f).map e) ≫ _ =
    _ ≫ (ordinaryFinitePullback B f).map ((scalarExtension φ Y).map e) at hn
  simp only [pullMap, Functor.map_comp, ← Category.assoc]
  rw [hn]

variable [Finite A] [Finite B]

private theorem unit_pullback (φ : A →+* B) {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (scalarExtension φ X).map (ordinaryFiniteUnitPullback A f).hom ≫ unit φ X =
      pullMap φ f (unit φ Y) ≫ (ordinaryFiniteUnitPullback B f).hom := by
  apply (cancel_epi ((scalarPullbackIso φ f).hom.app (ordinaryFiniteUnit A Y))).1
  simp only [pullMap, Category.assoc, Iso.hom_inv_id_app_assoc]
  rw [ordinaryChartUnitMap_eq φ X, ordinaryChartUnitMap_eq φ Y]
  simp only [← Functor.map_comp_assoc]
  have hA := ordinaryFiniteSingleUnitPullback_hom A f
  have hB := ordinaryFiniteSingleUnitPullback_hom B f
  change (ordinaryFiniteUnitPullback A f).hom ≫
      (ordinaryFiniteSingleUnitIso A X).hom =
    (ordinaryFinitePullback A f).map (ordinaryFiniteSingleUnitIso A Y).hom ≫
      (leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} A) f).hom at hA
  change (ordinaryFiniteUnitPullback B f).hom ≫
      (ordinaryFiniteSingleUnitIso B X).hom =
    (ordinaryFinitePullback B f).map (ordinaryFiniteSingleUnitIso B Y).hom ≫
      (leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} B) f).hom at hB
  rw [hA]
  simp only [Functor.map_comp, Category.assoc]
  have hn := (scalarPullbackIso φ f).hom.naturality
    (ordinaryFiniteSingleUnitIso A Y).hom
  dsimp only [Functor.comp_map] at hn
  simp only [ordinaryFinitePullback] at hn hB ⊢
  rw [← reassoc_of% hn, reassoc_of% (etaleScalarPullback_unit φ f)]
  apply (cancel_mono (ordinaryFiniteSingleUnitIso B X).hom).1
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [hB]
  simp only [← Functor.map_comp_assoc, Iso.inv_hom_id, Category.comp_id]

private theorem base_pullback (φ : A →+* B) (N : ℕ) (hN : 0 < N)
    (hA : (N : A) = 0) (hB : (N : B) = 0)
    (tA : OrdinaryFiniteTwistTransport A N hA)
    (tB : OrdinaryFiniteTwistTransport B N hB)
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hX : IsUnit (N : Γ(X, ⊤))) (hY : IsUnit (N : Γ(Y, ⊤))) (d : ℕ) :
    (scalarExtension φ X).map
        (vectorIntegrationBaseCoefficientPullback A N hA tA f hY d).hom ≫
      base φ N hN hA hB X hX d =
    pullBase φ N hN hA hB f hY d ≫
      (vectorIntegrationBaseCoefficientPullback B N hB tB f hY d).hom := by
  induction d with
  | zero => exact unit_pullback φ f
  | succ d ih =>
    have hl := finite_tate_scalar_pullback_square φ N hN hA hB tA tB f hX hY
    change (scalarExtension φ X).map
        ((ordinaryFiniteTensorPullback A f _ _).hom ≫
          ((vectorIntegrationBaseCoefficientPullback A N hA tA f hY d).hom ⊗ₘ
            (ordinaryFiniteShiftedLinePullback A N hA tA f hY).hom)) ≫
      tensorMap φ X (base φ N hN hA hB X hX d) (line φ N hN hA hB X hX) =
      pullMap φ f (tensorMap φ Y (base φ N hN hA hB Y hY d)
        (line φ N hN hA hB Y hY)) ≫
        (ordinaryFiniteTensorPullback B f _ _).hom ≫
          ((vectorIntegrationBaseCoefficientPullback B N hB tB f hY d).hom ⊗ₘ
            (ordinaryFiniteShiftedLinePullback B N hB tB f hY).hom)
    change (scalarExtension φ X).map
        (vectorIntegrationBaseCoefficientPullback A N hA tA f hY d).hom ≫
      base φ N hN hA hB X hX d =
      pullMap φ f (base φ N hN hA hB Y hY d) ≫
        (vectorIntegrationBaseCoefficientPullback B N hB tB f hY d).hom at ih
    have hl' : (scalarExtension φ X).map
        (ordinaryFiniteShiftedLinePullback A N hA tA f hY).hom ≫
        line φ N hN hA hB X hX =
        pullMap φ f (line φ N hN hA hB Y hY) ≫
          (ordinaryFiniteShiftedLinePullback B N hB tB f hY).hom := by
      simpa only [pullMap, Category.assoc] using hl
    rw [Functor.map_comp, Category.assoc, tensorMap_pre]
    rw [ih, hl']
    rw [← tensorMap_post, ← Category.assoc, tensor_pull]
    simp only [Category.assoc]


omit [Finite A] [Finite B] in
private theorem pull_comp_hom (φ : A →+* B) {X Y Z : Scheme.{u}}
    (g : Y ⟶ Z) (f : X ⟶ Y) (k : X ⟶ Z) (hk : f ≫ g = k)
    {K : DerivedCategoryModule A Z} {K' : DerivedCategoryModule B Z}
    (b : (scalarExtension φ Z).obj K ⟶ K') :
    (scalarExtension φ X).map
        ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) f g k hk.symm).hom.app K) ≫
      pullMap φ f (pullMap φ g b) =
    pullMap φ k b ≫
      (leftDerivedUpperStarComp (ModuleCat.{u + 1} B) f g k hk.symm).hom.app K' := by
  apply (cancel_epi ((scalarExtension φ X).map
    ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) f g k hk.symm).inv.app K))).1
  simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_app,
    CategoryTheory.Functor.map_id, Category.id_comp]
  rw [reassoc_of% (pull_comp φ g f k hk b)]
  simp only [Iso.inv_hom_id_app]
  erw [Category.comp_id]

private theorem named_compositor
    (R : Type (u + 1)) [CommRing R] {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (k : X ⟶ Z) (e : k = f ≫ g) :
    eqToIso (congrArg (ordinaryFinitePullback R) e) ≪≫
        leftDerivedUpperStarComp (ModuleCat.{u + 1} R) f g =
      leftDerivedUpperStarComp (ModuleCat.{u + 1} R) f g k e := by
  subst k
  simp only [eqToIso_refl, Iso.refl_trans]

-- The frame diagram is proved with abstract coefficient objects.  In particular,
-- its kernel check never unfolds the construction of a vector-bundle scheme.
private def frameCoefficientIso (R : Type (u + 1)) [CommRing R]
    {X X' Y Y' : Scheme.{u}} (p : X ⟶ Y) (q : X' ⟶ Y')
    (c : X' ⟶ X) (v : Y' ⟶ Y) (w : c ≫ p = q ≫ v)
    (K : DerivedCategoryModule R Y) {L : DerivedCategoryModule R Y'}
    (e : (ordinaryFinitePullback R v).obj K ≅ L)
    {M : DerivedCategoryModule R X'} (a : M ≅ (ordinaryFinitePullback R q).obj L) :
    (ordinaryFinitePullback R c).obj ((ordinaryFinitePullback R p).obj K) ≅ M :=
  (leftDerivedUpperStarComp (ModuleCat.{u + 1} R) c p).symm.app K ≪≫
    (eqToIso (congrArg (ordinaryFinitePullback R) w)).app K ≪≫
    (leftDerivedUpperStarComp (ModuleCat.{u + 1} R) q v).app K ≪≫
    (ordinaryFinitePullback R q).mapIso e ≪≫ a.symm

private theorem paste_frame_square
    {C D : Type*} [Category C] [Category D] (Q : C ⥤ D)
    {E F G H M : C} {E' F' G' H' M' : D}
    (i : E ⟶ F) (j : F ⟶ G) (e : G ⟶ H) (a : M ≅ H)
    (i' : E' ⟶ F') (j' : F' ⟶ G') (e' : G' ⟶ H') (a' : M' ≅ H')
    (b₀ : Q.obj E ⟶ E') (b₁ : Q.obj F ⟶ F')
    (b₂ : Q.obj G ⟶ G') (b₃ : Q.obj H ⟶ H')
    (hi : Q.map i ≫ b₁ = b₀ ≫ i')
    (hj : Q.map j ≫ b₂ = b₁ ≫ j')
    (he : Q.map e ≫ b₃ = b₂ ≫ e') :
    Q.map (i ≫ j ≫ e ≫ a.inv) ≫ Q.map a.hom ≫ b₃ ≫ a'.inv =
      b₀ ≫ i' ≫ j' ≫ e' ≫ a'.inv := by
  simp only [Functor.map_comp, Category.assoc]
  rw [Iso.map_inv_hom_id_assoc]
  rw [reassoc_of% he, reassoc_of% hj, reassoc_of% hi]

private theorem app_comp_congr
    {C D : Type*} [Category C] [Category D] {F G H : C ⥤ D}
    (i : F ≅ G) (j : G ≅ H) (k : F ≅ H) (h : i ≪≫ j = k) (X : C) :
    i.app X ≪≫ j.app X = k.app X := by
  subst k
  rfl

private theorem paste_iso_hom
    {C : Type*} [Category C] {U V W X Y Z : C}
    (i : U ≅ V) (j : V ≅ W) (k : W ≅ X) (l : X ≅ Y) (m : Y ≅ Z)
    (n : V ≅ X) (h : j ≪≫ k = n) :
    (i ≪≫ j ≪≫ k ≪≫ l ≪≫ m).hom = i.hom ≫ n.hom ≫ l.hom ≫ m.hom := by
  subst n
  simp only [Iso.trans_hom, Category.assoc]

private theorem frameCoefficientIso_hom (R : Type (u + 1)) [CommRing R]
    {X X' Y Y' : Scheme.{u}} (p : X ⟶ Y) (q : X' ⟶ Y')
    (c : X' ⟶ X) (v : Y' ⟶ Y) (w : c ≫ p = q ≫ v)
    (K : DerivedCategoryModule R Y) {L : DerivedCategoryModule R Y'}
    (e : (ordinaryFinitePullback R v).obj K ≅ L)
    {M : DerivedCategoryModule R X'} (a : M ≅ (ordinaryFinitePullback R q).obj L) :
    (frameCoefficientIso R p q c v w K e a).hom =
      (leftDerivedUpperStarComp (ModuleCat.{u + 1} R) c p).inv.app K ≫
      (leftDerivedUpperStarComp (ModuleCat.{u + 1} R) q v (c ≫ p) w).hom.app K ≫
      (ordinaryFinitePullback R q).map e.hom ≫ a.inv := by
  have hn := app_comp_congr
    (eqToIso (congrArg (ordinaryFinitePullback R) w))
    (leftDerivedUpperStarComp (ModuleCat.{u + 1} R) q v)
    (leftDerivedUpperStarComp (ModuleCat.{u + 1} R) q v (c ≫ p) w)
    (named_compositor R q v (c ≫ p) w) K
  exact paste_iso_hom
    ((leftDerivedUpperStarComp (ModuleCat.{u + 1} R) c p).symm.app K)
    ((eqToIso (congrArg (ordinaryFinitePullback R) w)).app K)
    ((leftDerivedUpperStarComp (ModuleCat.{u + 1} R) q v).app K)
    ((ordinaryFinitePullback R q).mapIso e) a.symm
    ((leftDerivedUpperStarComp (ModuleCat.{u + 1} R) q v (c ≫ p) w).app K) hn

omit [Finite A] [Finite B] in
private theorem frameCoefficientIso_scalar (φ : A →+* B)
    {X X' Y Y' : Scheme.{u}} (p : X ⟶ Y) (q : X' ⟶ Y')
    (c : X' ⟶ X) (v : Y' ⟶ Y) (w : c ≫ p = q ≫ v)
    {KA : DerivedCategoryModule A Y} {KB : DerivedCategoryModule B Y}
    {LA : DerivedCategoryModule A Y'} {LB : DerivedCategoryModule B Y'}
    {MA : DerivedCategoryModule A X'} {MB : DerivedCategoryModule B X'}
    (b : (scalarExtension φ Y).obj KA ⟶ KB)
    (l : (scalarExtension φ Y').obj LA ⟶ LB)
    (eA : (ordinaryFinitePullback A v).obj KA ≅ LA)
    (eB : (ordinaryFinitePullback B v).obj KB ≅ LB)
    (aA : MA ≅ (ordinaryFinitePullback A q).obj LA)
    (aB : MB ≅ (ordinaryFinitePullback B q).obj LB)
    (he : (scalarExtension φ Y').map eA.hom ≫ l = pullMap φ v b ≫ eB.hom) :
    (scalarExtension φ X').map (frameCoefficientIso A p q c v w KA eA aA).hom ≫
        (scalarExtension φ X').map aA.hom ≫ pullMap φ q l ≫ aB.inv =
      pullMap φ c (pullMap φ p b) ≫
        (frameCoefficientIso B p q c v w KB eB aB).hom := by
  have he' : (scalarExtension φ X').map ((ordinaryFinitePullback A q).map eA.hom) ≫
      pullMap φ q l =
      pullMap φ q (pullMap φ v b) ≫ (ordinaryFinitePullback B q).map eB.hom := by
    rw [pullMap_pre, he, ← pullMap_post]
  have h := paste_frame_square (scalarExtension φ X')
    ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) c p).inv.app KA)
    ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) q v (c ≫ p) w).hom.app KA)
    ((ordinaryFinitePullback A q).map eA.hom) aA
    ((leftDerivedUpperStarComp (ModuleCat.{u + 1} B) c p).inv.app KB)
    ((leftDerivedUpperStarComp (ModuleCat.{u + 1} B) q v (c ≫ p) w).hom.app KB)
    ((ordinaryFinitePullback B q).map eB.hom) aB
    (pullMap φ c (pullMap φ p b)) (pullMap φ (c ≫ p) b)
    (pullMap φ q (pullMap φ v b)) (pullMap φ q l)
    (pull_comp φ p c (c ≫ p) rfl b) (pull_comp_hom φ v q (c ≫ p) w.symm b) he'
  simpa only [frameCoefficientIso_hom] using h

private theorem chart_coefficient_scalar (φ : A →+* B) (N : ℕ) (hN : 0 < N)
    (hA : (N : A) = 0) (hB : (N : B) = 0)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ)
    (F : SheafOfModules.{u} S.ringCatSheaf) [F.IsFiniteLocallyFreeOfRank d]
    (V : S.Opens) (e : VectorBundleZeroSection.Trivialization S d F V) :
    (scalarExtension φ (affineTraceTower V.toScheme d)).map
        (vectorIntegrationChartCoefficient A N hA
          (projectiveLineTraceTransport N hN A hA) S hS d F V e).hom ≫
      affineCoefficient φ N hN hA hB V.toScheme
        (affineTracePullbackInvertible N V.ι hS) d =
    pullMap φ (vectorIntegrationChart S d F V e)
        (pullBase φ N hN hA hB (VectorBundleZeroSection.π S d F) hS d) ≫
      (vectorIntegrationChartCoefficient B N hB
        (projectiveLineTraceTransport N hN B hB) S hS d F V e).hom := by
  have hb := base_pullback φ N hN hA hB
    (projectiveLineTraceTransport N hN A hA) (projectiveLineTraceTransport N hN B hB)
    V.ι (affineTracePullbackInvertible N V.ι hS) hS d
  have h := frameCoefficientIso_scalar φ (VectorBundleZeroSection.π S d F)
    (affineTraceProjection V.toScheme d) (vectorIntegrationChart S d F V e) V.ι
    (vectorIntegrationChart_isPullback S d F V e).w
    (base φ N hN hA hB S hS d)
    (base φ N hN hA hB V.toScheme (affineTracePullbackInvertible N V.ι hS) d)
    (vectorIntegrationBaseCoefficientPullback A N hA
      (projectiveLineTraceTransport N hN A hA) V.ι hS d)
    (vectorIntegrationBaseCoefficientPullback B N hB
      (projectiveLineTraceTransport N hN B hB) V.ι hS d)
    (affineLinearCoefficientDescent A N hA (projectiveLineTraceTransport N hN A hA)
      V.toScheme (affineTracePullbackInvertible N V.ι hS) d)
    (affineLinearCoefficientDescent B N hB (projectiveLineTraceTransport N hN B hB)
      V.toScheme (affineTracePullbackInvertible N V.ι hS) d) hb
  exact h

private theorem compact_restriction_derived (φ : A →+* B)
    {X X' Y Y' : Scheme.{u}}
    [IsNoetherian X] [IsNoetherian X'] [IsNoetherian Y] [IsNoetherian Y']
    {f : X ⟶ Y} [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    {f' : X' ⟶ Y'} {v : Y' ⟶ Y} {h : X' ⟶ X} [IsOpenImmersion v]
    (sq : IsPullback h f' f v) (c : Compactification f)
    (M : DerivedCategoryModule A X) :
    (ordinaryFinitePullback B v).map ((compactScalarMap φ c).app M) ≫
      (rightDerivedLowerShriekOfCompactificationBaseChangeMap
        (ModuleCat.{u + 1} B) sq c).app ((scalarExtension φ X).obj M) ≫
      (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} B)
        (c.ofIsPullback sq)).map ((scalarPullbackIso φ h).hom.app M) =
    (scalarPullbackIso φ v).hom.app
        ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).obj M) ≫
      (scalarExtension φ Y').map
        ((rightDerivedLowerShriekOfCompactificationBaseChangeMap
          (ModuleCat.{u + 1} A) sq c).app M) ≫
      (compactScalarMap φ (c.ofIsPullback sq)).app
        ((ordinaryFinitePullback A h).obj M) := by
  let eA := fun {U T : Scheme.{u}} (g : U ⟶ T) ↦
    leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) g
  let eB := fun {U T : Scheme.{u}} (g : U ⟶ T) ↦
    leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} B) g
  let RA := rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c
  let RB' := rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} B)
    (c.ofIsPullback sq)
  have ht := etaleCompactScalarOpenRestriction φ sq c M
  simp only [unboundedEtaleCompactSupportExchange, properOpenCoefficientPullbackIso,
    Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.map_comp, Category.assoc] at ht
  have hh := congrArg (fun z ↦ (eB v).hom.app ((scalarExtension φ Y).obj (RA.obj M)) ≫
    z ≫ RB'.map ((scalarExtension φ X').map ((eA h).inv.app M))) ht
  have hn := (eB v).hom.naturality ((compactScalarMap φ c).app M)
  have hm := (compactScalarMap φ (c.ofIsPullback sq)).naturality ((eA h).hom.app M)
  dsimp only [Functor.comp_obj] at hn
  simp only [Category.assoc] at hh
  erw [← reassoc_of% hn] at hh
  dsimp only [eA, eB, RA, RB', rightDerivedLowerShriekOfCompactification,
    Functor.comp_obj, Functor.comp_map] at hh
  simp only [Iso.hom_inv_id_app_assoc] at hh
  erw [reassoc_of% hm] at hh
  simpa only [eA, eB, RA, RB', rightDerivedLowerShriekOfCompactification,
    ordinaryFinitePullback, Functor.comp_obj, Functor.comp_map, Category.assoc,
    ← Functor.map_comp_assoc, ← Functor.map_comp, Iso.hom_inv_id_app_assoc,
    Iso.hom_inv_id_app, CategoryTheory.Functor.map_id, Category.id_comp,
    Category.comp_id] using hh

private theorem compact_restriction_chosen (φ : A →+* B)
    {X X' Y Y' : Scheme.{u}}
    [IsNoetherian X] [IsNoetherian X'] [IsNoetherian Y] [IsNoetherian Y']
    {f : X ⟶ Y} [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    {f' : X' ⟶ Y'} [QuasiCompact f'] [HasCompactification f] [HasCompactification f']
    {v : Y' ⟶ Y} {h : X' ⟶ X} [IsOpenImmersion v]
    (sq : IsPullback h f' f v) (M : DerivedCategoryModule A X) :
    (ordinaryFinitePullback B v).map ((compactScalarChosenMap φ f).app M) ≫
      (rightDerivedLowerShriekBaseChangeMap B sq).app ((scalarExtension φ X).obj M) ≫
      (rightDerivedLowerShriek (ModuleCat.{u + 1} B) f').map
        ((scalarPullbackIso φ h).hom.app M) =
    (scalarPullbackIso φ v).hom.app
        ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).obj M) ≫
      (scalarExtension φ Y').map ((rightDerivedLowerShriekBaseChangeMap A sq).app M) ≫
      (compactScalarChosenMap φ f').app ((ordinaryFinitePullback A h).obj M) := by
  let c := HasCompactification.compactification f
  let d := c.ofIsPullback sq
  have ht := compact_restriction_derived φ sq c M
  have hh := congrArg (fun z ↦ z ≫ (rightDerivedLowerShriekIso B d).hom.app
    ((scalarExtension φ X').obj ((ordinaryFinitePullback A h).obj M))) ht
  have hn := (rightDerivedLowerShriekIso B d).hom.naturality
    ((scalarPullbackIso φ h).hom.app M)
  have hc := ordinaryChartCompactificationScalar φ d
    (HasCompactification.compactification f') ((ordinaryFinitePullback A h).obj M)
  change (scalarExtension φ Y').map
      ((rightDerivedLowerShriekIso A d).hom.app ((ordinaryFinitePullback A h).obj M)) ≫
    (compactScalarChosenMap φ f').app ((ordinaryFinitePullback A h).obj M) =
    (compactScalarMap φ d).app ((ordinaryFinitePullback A h).obj M) ≫
      (rightDerivedLowerShriekIso B d).hom.app
        ((scalarExtension φ X').obj ((ordinaryFinitePullback A h).obj M)) at hc
  dsimp only [Functor.comp_obj] at hn
  simp only [Category.assoc] at hh
  erw [hn, ← hc] at hh
  simpa only [rightDerivedLowerShriekBaseChangeMap, compactScalarChosenMap,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.map_comp, Category.assoc,
    c, d, ordinaryFinitePullback, rightDerivedLowerShriek, Functor.comp_obj] using hh

/-- Compact/open exchange after inserting the ordered affine component.
Source: blueprint/latest, sec-smooth-purity/sk-prop-an, cor-pur-vector-bundle-purity,
proof paragraph 2 ("on a trivializing open the integration is the ordered affine-space
counit"; the affine compatibility descends to the bundle).  This is the compact-support
subargument of the frame comparison.

Proof. (1) Coefficient square on the chart. The finite Tate scalar pullback square
(lem-pur-finite-tate-scalar-pullback-square) gives the square for the shifted line; the unit
square follows from scalar/pullback unit coherence (lem-pur-etale-scalar-pullback-unit-coherence)
through the ordinary single/unit identifications (lem-pur-ordinary-chart-unit-map,
lem-pur-ordinary-finite-single-unit-pullback).  Induction on the number of ordered tensor
factors, with scalar/pullback tensor coherence (lem-pur-etale-scalar-pullback-tensor-coherence),
gives the square for `vectorIntegrationBaseCoefficientPullback`.  Scalar/pullback composition
coherence (lem-sf-scalar-pullback-composition) on the two factorizations of the inverse-frame
Cartesian square, pasted with this square, gives the scalar square for
`vectorIntegrationChartCoefficient`.  (2) Compact exchange.  The open-restriction square of
compact scalar coherence (lem-pur-etale-compact-scalar-coherence), conjugated by the
exact/left-derived inverse-image comparisons and moved to the chosen compactification
(lem-pur-ordinary-chart-compactification-scalar), commutes with
`rightDerivedLowerShriekBaseChangeMap` for the inverse-frame square over the Noetherian open
`V`.  (3) Expand both local traces; naturality of compact exchange and of the affine compact
scalar map and (1) leave exactly `ha` over `V` in dimension `r`.  The local traces do not depend
on the data `(tA, DA)`, `(tB, DB)`: each equals the restriction of the glued integration map by
its normalization (`existsUnique_vectorIntegrationGluing`), so the canonical projective-line
data may be used.  The binder `hAffine` (the equation over `S`) is not needed.
(blueprint: new-lem-pur-vector-scalar-frame-compact-component).
-/
theorem frame_scalar_restriction_compact (N : ℕ) (hN : 0 < N) (φ : A →+* B)
    (hA : (N : A) = 0) (hB : (N : B) = 0)
    (ha : ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (N : Γ(T, ⊤)))
      (d : ℕ), affine φ N hN hA hB T hT d ≫ affineTrace N hN B hB T hT d =
        (scalarExtension φ T).map (affineTrace N hN A hA T hT d) ≫ unit φ T)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤)))
    (r : ℕ) (F : SheafOfModules.{u} S.ringCatSheaf)
    [F.IsFiniteLocallyFreeOfRank r] (V : S.Opens)
    (e : VectorBundleZeroSection.Trivialization S r F V)
    (hAffine : affine φ N hN hA hB S hS r ≫
      affineTrace N hN B hB S hS r =
        (scalarExtension φ S).map
          (affineTrace N hN A hA S hS r) ≫ unit φ S)
    (tA : OrdinaryFiniteTwistTransport A N hA)
    (DA : ∀ (T : Scheme.{u}) [IsNoetherian T]
      (hT : IsUnit (N : Γ(T, ⊤))), OrdinaryFiniteP1Datum A N hA tA T hT)
    (tB : OrdinaryFiniteTwistTransport B N hB)
    (DB : ∀ (T : Scheme.{u}) [IsNoetherian T]
      (hT : IsUnit (N : Γ(T, ⊤))), OrdinaryFiniteP1Datum B N hB tB T hT) :
    (ordinaryFinitePullback B V.ι).map (vector φ N hN hA hB S hS r F) ≫
        vectorIntegrationLocalTrace N hN B hB tB DB S hS r F V e =
      (scalarPullbackIso φ V.ι).hom.app
          (vectorIntegrationSource A N hA S r F) ≫
        (scalarExtension φ V.toScheme).map
          (vectorIntegrationLocalTrace N hN A hA tA DA S hS r F V e) ≫
        unit φ V.toScheme := by
  let tA₀ := projectiveLineTraceTransport N hN A hA
  let tB₀ := projectiveLineTraceTransport N hN B hB
  let DA₀ := projectiveLineTraceDatum N hN A hA
  let DB₀ := projectiveLineTraceDatum N hN B hB
  have hlocalA : vectorIntegrationLocalTrace N hN A hA tA DA S hS r F V e =
      vectorIntegrationLocalTrace N hN A hA tA₀ DA₀ S hS r F V e := by
    have h := (existsUnique_vectorIntegrationGluing N hN A hA S hS r F).2.exists.choose_spec.2
    exact (h tA DA V e).symm.trans (h tA₀ DA₀ V e)
  have hlocalB : vectorIntegrationLocalTrace N hN B hB tB DB S hS r F V e =
      vectorIntegrationLocalTrace N hN B hB tB₀ DB₀ S hS r F V e := by
    have h := (existsUnique_vectorIntegrationGluing N hN B hB S hS r F).2.exists.choose_spec.2
    exact (h tB DB V e).symm.trans (h tB₀ DB₀ V e)
  rw [hlocalA, hlocalB]
  let : IsAffineHom (VectorBundleZeroSection.π S r F) :=
    (vectorIntegration_geometry S r F).1
  let : LocallyOfFiniteType (VectorBundleZeroSection.π S r F) :=
    (vectorIntegration_geometry S r F).2.1
  let : IsNoetherian (VectorBundleZeroSection.scheme S r F) :=
    (vectorIntegration_geometry S r F).2.2
  let : TopologicalSpace.NoetherianSpace V.toScheme :=
    V.ι.isOpenEmbedding.isInducing.noetherianSpace
  let : IsNoetherian V.toScheme :=
    { toIsLocallyNoetherian := inferInstance
      isCompact_univ := TopologicalSpace.NoetherianSpace.isCompact _ }
  let := affineTraceNoetherian V.toScheme r
  let p := VectorBundleZeroSection.π S r F
  let q := affineTraceProjection V.toScheme r
  let c := vectorIntegrationChart S r F V e
  let sq := vectorIntegrationChart_isPullback S r F V e
  let hV := affineTracePullbackInvertible N V.ι hS
  let MA := vectorIntegrationCoefficient A N hA S r F
  let b := pullBase φ N hN hA hB p hS r
  let aA := (vectorIntegrationChartCoefficient A N hA tA₀ S hS r F V e).hom
  let aB := (vectorIntegrationChartCoefficient B N hB tB₀ S hS r F V e).hom
  let RA := rightDerivedLowerShriek (ModuleCat.{u + 1} A) q
  let RB := rightDerivedLowerShriek (ModuleCat.{u + 1} B) q
  have hc := chart_coefficient_scalar φ N hN hA hB S hS r F V e
  have hc' := congrArg (fun z ↦ (scalarPullbackIso φ c).hom.app MA ≫ z) hc
  dsimp only [c, MA, vectorIntegrationCoefficient] at hc'
  simp only [pullMap, Category.assoc, Iso.hom_inv_id_app_assoc] at hc'
  change (scalarPullbackIso φ c).hom.app MA ≫
      (scalarExtension φ (affineTraceTower V.toScheme r)).map aA ≫
      affineCoefficient φ N hN hA hB V.toScheme hV r =
    (ordinaryFinitePullback B c).map b ≫ aB at hc'
  have hn := (rightDerivedLowerShriekBaseChangeMap B sq).naturality b
  dsimp only [Functor.comp_map] at hn
  have ht := compact_restriction_chosen φ sq MA
  have hn' := (compactScalarChosenMap φ q).naturality aA
  dsimp only [Functor.comp_map] at hn'
  change (ordinaryFinitePullback B V.ι).map
      ((compactScalarChosenMap φ p).app MA ≫
        (rightDerivedLowerShriek (ModuleCat.{u + 1} B) p).map b) ≫
    (rightDerivedLowerShriekBaseChangeMap B sq).app _ ≫ RB.map aB ≫
      affineTrace N hN B hB V.toScheme hV r =
    (scalarPullbackIso φ V.ι).hom.app (vectorIntegrationSource A N hA S r F) ≫
      (scalarExtension φ V.toScheme).map
        ((rightDerivedLowerShriekBaseChangeMap A sq).app MA ≫ RA.map aA ≫
          affineTrace N hN A hA V.toScheme hV r) ≫ unit φ V.toScheme
  simp only [Functor.map_comp, Category.assoc]
  erw [reassoc_of% hn]
  rw [← RB.map_comp_assoc]
  erw [← hc']
  simp only [Functor.map_comp, Category.assoc]
  erw [reassoc_of% ht, ← reassoc_of% hn']
  have haV := ha V.toScheme hV r
  unfold affine at haV
  simp only [Category.assoc] at haV
  rw [haV]
  rfl

end AlgebraicGeometry.Etale.VectorTraceScalar
