/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.VectorTraceScalar.VectorTraceScalarData
import WeilConjectures.AlgebraicGeometry.VectorTraceScalar.VectorTraceScalarAffineSourceCompatibility
import WeilConjectures.AlgebraicGeometry.VectorTraceScalar.VectorTraceScalarAffineCompactCompatibility
import WeilConjectures.AlgebraicGeometry.Etale.EtaleDirectScalarProjection
import WeilConjectures.AlgebraicGeometry.ExceptionalCoefficients.ExceptionalCoefficientUnitCoherence
import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinaryChartSingleUnitor
import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinaryChartUnitNormalization
import all WeilConjectures.AlgebraicGeometry.Ordinary.OrdinaryChartIdentityScalar
import WeilConjectures.CategoryTheory.Exact.ExactDegreeZeroSupplement

/-! # Ordered affine scalar induction from projective traces

Source: blueprint/latest, sec-smooth-purity/sk-prop-an,
cor-pur-vector-bundle-purity.proof.md, paragraph 2.
(blueprint: lem-pur-vector-scalar-affine-induction).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option maxRecDepth 2048
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open WeilConjectures.PurityFiniteSetting
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale.VectorTraceScalar
set_option linter.auxLemma false in
attribute [local instance 100000] DerivedCategoryModule._proof_1 DerivedCategoryModule._proof_2
attribute [local instance 10000] SheafExactDegreeZero.scalarWeakSheafify
attribute [local irreducible] Functor.leftAdjoint Functor.rightAdjoint
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor Functor.mapDerivedCategory
  ProEtale.pbcFixedScalarExtension derivedTensor upperStar lowerStar
  projectiveLineTraceDatum projectiveLineTraceTransport
  purityScalarSingleMap purityScalarUnitMap
  ExceptionalCoefficients.tensorIso ExceptionalCoefficients.unitIso
  singleFunctorObjUnitIso derivedTensorRightUnitor
  HasDerivedCategory.ofIsGrothendieckAbelian HasDerivedCategory.ofHasKInjectiveResolutions
  _root_.DerivedCategory.singleFunctors

attribute [local implicit_reducible] affineTraceTower affineTraceProjection

variable {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem tensor_trace_counit_square
    {C D : Type*} [Category C] [Category D]
    (T : C ⥤ D) (TA : C ⥤ C ⥤ C) (TB : D ⥤ D ⥤ D)
    (m : Functor.uncurry.obj TA ⋙ T ⟶
      (T.prod T) ⋙ Functor.uncurry.obj TB)
    (K H I : C) (H' I' : D) (E : C) (E' : D)
    (π : (TA.obj K).obj H ⟶ E) [Epi (T.map π)]
    (π' : (TB.obj (T.obj K)).obj H' ⟶ E')
    (c : T.obj E ⟶ E') (ε : E ⟶ K) (ε' : E' ⟶ T.obj K)
    (t : H ⟶ I) (t' : H' ⟶ I') (b : T.obj H ⟶ H') (e : T.obj I ⟶ I')
    (ρ : (TA.obj K).obj I ⟶ K)
    (ρ' : (TB.obj (T.obj K)).obj I' ⟶ T.obj K)
    (hπ : T.map π ≫ c = m.app (K, H) ≫ (TB.obj (T.obj K)).map b ≫ π')
    (hε : π ≫ ε = (TA.obj K).map t ≫ ρ)
    (hε' : π' ≫ ε' = (TB.obj (T.obj K)).map t' ≫ ρ')
    (ht : b ≫ t' = T.map t ≫ e)
    (hρ : m.app (K, I) ≫ (TB.obj (T.obj K)).map e ≫ ρ' = T.map ρ) :
    c ≫ ε' = T.map ε := by
  apply (cancel_epi (T.map π)).1
  rw [← Category.assoc, hπ]
  simp only [Category.assoc]
  rw [hε', ← Functor.map_comp_assoc, ht, Functor.map_comp, Category.assoc]
  have hn := m.naturality (show (K, H) ⟶ (K, I) from (𝟙 K, t))
  dsimp only [Functor.comp_map, Functor.prod_map, Functor.uncurry_obj_map] at hn
  simp only [CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp,
    Functor.comp_obj, Functor.prod_obj, Functor.uncurry_obj_obj] at hn
  rw [← reassoc_of% hn, hρ, ← T.map_comp, ← hε, T.map_comp]

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem transported_right_unit
    {C D : Type*} [Category C] [Category D]
    (T : C ⥤ D) (TA : C ⥤ C ⥤ C) (TB : D ⥤ D ⥤ D)
    (m : Functor.uncurry.obj TA ⋙ T ⟶ T.prod T ⋙ Functor.uncurry.obj TB)
    (K I U : C) (I' U' : D) (e : I ≅ U) (f : I' ≅ U') (mu : T.obj U ⟶ U')
    (ρ : (TA.obj K).obj U ⟶ K) (ρ' : (TB.obj (T.obj K)).obj U' ⟶ T.obj K)
    (hu : m.app (K, U) ≫ (TB.obj (T.obj K)).map mu ≫ ρ' = T.map ρ) :
    m.app (K, I) ≫ (TB.obj (T.obj K)).map (T.map e.hom ≫ mu ≫ f.inv) ≫
      ((TB.obj (T.obj K)).map f.hom ≫ ρ') =
    T.map ((TA.obj K).map e.hom ≫ ρ) := by
  have hn := m.naturality (show (K, I) ⟶ (K, U) from (𝟙 K, e.hom))
  dsimp only [Functor.comp_map, Functor.prod_map, Functor.uncurry_obj_map] at hn
  simp only [CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp,
    Functor.comp_obj, Functor.prod_obj, Functor.uncurry_obj_obj] at hn
  simp only [Functor.map_comp, Category.assoc]
  rw [← Functor.map_comp_assoc _ f.inv f.hom, f.inv_hom_id,
    CategoryTheory.Functor.map_id, Category.id_comp, ← reassoc_of% hn, hu, ← T.map_comp]

private theorem transported_right_unit_named
    {C D : Type*} [Category C] [Category D]
    (T : C ⥤ D) (TA : C ⥤ C ⥤ C) (TB : D ⥤ D ⥤ D)
    (m : Functor.uncurry.obj TA ⋙ T ⟶ T.prod T ⋙ Functor.uncurry.obj TB)
    (K I U : C) (I' U' : D) (e : I ≅ U) (f : I' ≅ U') (mu : T.obj U ⟶ U')
    (ρ : (TA.obj K).obj U ⟶ K) (ρ' : (TB.obj (T.obj K)).obj U' ⟶ T.obj K)
    (v : T.obj I ⟶ I') (r : (TA.obj K).obj I ⟶ K)
    (r' : (TB.obj (T.obj K)).obj I' ⟶ T.obj K)
    (hv : v = T.map e.hom ≫ mu ≫ f.inv)
    (hr : r = (TA.obj K).map e.hom ≫ ρ)
    (hr' : r' = (TB.obj (T.obj K)).map f.hom ≫ ρ')
    (hu : m.app (K, U) ≫ (TB.obj (T.obj K)).map mu ≫ ρ' = T.map ρ) :
    m.app (K, I) ≫ (TB.obj (T.obj K)).map v ≫ r' = T.map r := by
  rw [hv, hr, hr']
  exact transported_right_unit T TA TB m K I U I' U' e f mu ρ ρ' hu

private theorem single_unit_square
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    (T : Scheme.{u}) (K : DerivedCategoryModule A T) :
    (ExceptionalCoefficients.tensorIso φ T).hom.app (K, ordinaryFiniteUnit A T) ≫
      ((ordinaryFiniteTensor B T).obj ((scalarExtension φ T).obj K)).map
        (VectorTraceScalar.unit φ T) ≫
      (derivedTensorSingleUnitIso ((scalarExtension φ T).obj K)).hom =
      (scalarExtension φ T).map (derivedTensorSingleUnitIso K).hom := by
  exact transported_right_unit_named (scalarExtension φ T)
    (ordinaryFiniteTensor A T) (ordinaryFiniteTensor B T)
    (ExceptionalCoefficients.tensorIso φ T).hom K
    (ordinaryFiniteUnit A T) (𝟙_ _) (ordinaryFiniteUnit B T) (𝟙_ _)
    (ordinaryFiniteSingleUnitIso A T) (ordinaryFiniteSingleUnitIso B T)
    (ExceptionalCoefficients.unitIso φ T).hom
    (derivedTensorRightUnitor (ModuleCat.{u + 1} A) T K).hom
    (derivedTensorRightUnitor (ModuleCat.{u + 1} B) T
      ((scalarExtension φ T).obj K)).hom
    (VectorTraceScalar.unit φ T) (derivedTensorSingleUnitIso K).hom
    (derivedTensorSingleUnitIso ((scalarExtension φ T).obj K)).hom
    (ordinaryChartUnitMap_eq φ T)
    (ordinaryChartSingleUnitor_eq T K)
    (ordinaryChartSingleUnitor_eq T ((scalarExtension φ T).obj K))
    (ExceptionalCoefficients.tensorIso_right_unit φ T K)

private theorem balanced_projection_scalar
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {X Y : Scheme.{u}} (f : X ⟶ Y) (K : DerivedCategoryModule A Y)
    (L : DerivedCategoryModule A X) (L' : DerivedCategoryModule B X)
    (l : (scalarExtension φ X).obj L ⟶ L') :
    (scalarExtension φ Y).map (ordinaryFiniteProjection A f L K) ≫
      (scalarMate φ f).app
        (((ordinaryFiniteTensor A X).obj ((ordinaryFinitePullback A f).obj K)).obj L) ≫
      (ordinaryFinitePushforward B f).map
        ((ExceptionalCoefficients.tensorIso φ X).hom.app
            ((ordinaryFinitePullback A f).obj K, L) ≫
          ((ordinaryFiniteTensor B X).map ((scalarPullbackIso φ f).inv.app K)).app
            ((scalarExtension φ X).obj L) ≫
          ((ordinaryFiniteTensor B X).obj
            ((ordinaryFinitePullback B f).obj ((scalarExtension φ Y).obj K))).map l) =
    (ExceptionalCoefficients.tensorIso φ Y).hom.app
        (K, (ordinaryFinitePushforward A f).obj L) ≫
      ((ordinaryFiniteTensor B Y).obj ((scalarExtension φ Y).obj K)).map
        ((scalarMate φ f).app L ≫ (ordinaryFinitePushforward B f).map l) ≫
      ordinaryFiniteProjection B f L' ((scalarExtension φ Y).obj K) := by
  have h := etaleDirectScalarProjection φ f K L
  have hn := (orderedDirectProjectionNat B f ((scalarExtension φ Y).obj K)).naturality l
  have hn' : ((ordinaryFiniteTensor B Y).obj ((scalarExtension φ Y).obj K)).map
      ((ordinaryFinitePushforward B f).map l) ≫
      orderedDirectProjection B f ((scalarExtension φ Y).obj K) L' =
    orderedDirectProjection B f ((scalarExtension φ Y).obj K)
      ((scalarExtension φ X).obj L) ≫
      (ordinaryFinitePushforward B f).map
        (((ordinaryFiniteTensor B X).obj
          ((ordinaryFinitePullback B f).obj ((scalarExtension φ Y).obj K))).map l) := by
    simpa only [Functor.comp_map, orderedDirectProjection, ordinaryFiniteTensor,
      ordinaryFinitePullback, ordinaryFinitePushforward, rightDerivedLowerStar] using hn
  have hh := congrArg (fun z ↦ z ≫ (ordinaryFinitePushforward B f).map
    (((ordinaryFiniteTensor B X).obj
      ((ordinaryFinitePullback B f).obj ((scalarExtension φ Y).obj K))).map l)) h
  simp only [Category.assoc, ordinaryFinitePushforward, ordinaryFiniteTensor,
    ordinaryFinitePullback] at hn' hh
  rw [← hn'] at hh
  simpa only [orderedDirectProjection_eq, ordinaryFiniteProjection,
    ordinaryFinitePushforward, ordinaryFiniteTensor, ordinaryFinitePullback,
    rightDerivedLowerStar, Functor.map_comp, Category.assoc] using hh

private theorem compose_counit_scalar
    {C D E C' D' E' : Type*}
    [Category C] [Category D] [Category E] [Category C'] [Category D'] [Category E']
    {L : C ⥤ D} {R : D ⥤ C} {M : D ⥤ E} {Q : E ⥤ D}
    {L' : C' ⥤ D'} {R' : D' ⥤ C'} {M' : D' ⥤ E'} {Q' : E' ⥤ D'}
    (a : L ⊣ R) (b : M ⊣ Q) (a' : L' ⊣ R') (b' : M' ⊣ Q')
    (S : C ⥤ C') (T : D ⥤ D') (U : E ⥤ E')
    (β : L ⋙ T ⟶ S ⋙ L') (γ : M ⋙ U ⟶ T ⋙ M')
    (K : E) (r : S.obj (R.obj (Q.obj K)) ⟶ R'.obj (T.obj (Q.obj K)))
    (q : T.obj (Q.obj K) ⟶ Q'.obj (U.obj K))
    (hr : β.app (R.obj (Q.obj K)) ≫ L'.map r ≫ a'.counit.app (T.obj (Q.obj K)) =
      T.map (a.counit.app (Q.obj K)))
    (hq : γ.app (Q.obj K) ≫ M'.map q ≫ b'.counit.app (U.obj K) =
      U.map (b.counit.app K)) :
    γ.app (L.obj (R.obj (Q.obj K))) ≫ M'.map (β.app (R.obj (Q.obj K))) ≫
      M'.map (L'.map (r ≫ R'.map q)) ≫ (a'.comp b').counit.app (U.obj K) =
      U.map ((a.comp b).counit.app K) := by
  simp only [Adjunction.comp_counit_app, Functor.map_comp, Category.assoc]
  have hn := a'.counit.naturality q
  simp only [Functor.comp_map, Functor.id_map] at hn
  have hn' := congrArg (fun z ↦ M'.map z) hn
  simp only [Functor.map_comp] at hn'
  rw [reassoc_of% hn']
  have hr' := congrArg (fun z ↦ M'.map z) hr
  simp only [Functor.map_comp] at hr'
  rw [reassoc_of% hr']
  have hm := γ.naturality (a.counit.app (Q.obj K))
  simp only [Functor.comp_map] at hm
  rw [← reassoc_of% hm, hq, ← U.map_comp]

private theorem p1_counit_from_trace
    (φ : A →+* B) (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0) (hB : (N : B) = 0)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤)))
    (ht : projective φ N hN hA hB S hS ≫ projectiveLineTrace N hN B hB S hS =
      (scalarExtension φ S).map (projectiveLineTrace N hN A hA S hS) ≫ unit φ S)
    (K : DerivedCategoryModule A S) :
    (scalarMate φ (ProjectiveLine S ↘ S)).app
        ((ordinaryFiniteP1Right A N hA S).obj K) ≫
      (ordinaryFinitePushforward B (ProjectiveLine S ↘ S)).map
        (projectiveSource φ N hN hA hB S hS K) ≫
      (projectiveLineTraceDatum N hN B hB S hS).adjunction.counit.app
        ((scalarExtension φ S).obj K) =
    (scalarExtension φ S).map
      ((projectiveLineTraceDatum N hN A hA S hS).adjunction.counit.app K) := by
  let q := ProjectiveLine S ↘ S
  let LA := (ordinaryFiniteLine A N hA (ProjectiveLine S))⟦(2 : ℤ)⟧
  let LB := (ordinaryFiniteLine B N hB (ProjectiveLine S))⟦(2 : ℤ)⟧
  let l := line φ N hN hA hB (ProjectiveLine S) (ordinaryFiniteP1_isUnit N S hS)
  let KB := (scalarExtension φ S).obj K
  have : IsLocallyNoetherian (ProjectiveLine S) :=
    LocallyOfFiniteType.isLocallyNoetherian q
  have : CompactSpace (ProjectiveLine S) := QuasiCompact.compactSpace_of_compactSpace q
  have : IsNoetherian (ProjectiveLine S) := ⟨⟩
  have : IsIso (ordinaryFiniteProjection A q LA K) :=
    isIso_proper_projection_formula_reordered A q LA K
  have hπ := balanced_projection_scalar φ q K LA LB l
  simp only [← Category.assoc]
  apply tensor_trace_counit_square (scalarExtension φ S)
    (ordinaryFiniteTensor A S) (ordinaryFiniteTensor B S)
    (ExceptionalCoefficients.tensorIso φ S).hom K
    ((ordinaryFinitePushforward A q).obj LA) (ordinaryFiniteUnit A S)
    ((ordinaryFinitePushforward B q).obj LB) (ordinaryFiniteUnit B S)
    ((ordinaryFinitePushforward A q).obj ((ordinaryFiniteP1Right A N hA S).obj K))
    ((ordinaryFinitePushforward B q).obj ((ordinaryFiniteP1Right B N hB S).obj KB))
    (ordinaryFiniteProjection A q LA K) (ordinaryFiniteProjection B q LB KB)
    ((scalarMate φ q).app ((ordinaryFiniteP1Right A N hA S).obj K) ≫
      (ordinaryFinitePushforward B q).map (projectiveSource φ N hN hA hB S hS K))
    ((projectiveLineTraceDatum N hN A hA S hS).adjunction.counit.app K)
    ((projectiveLineTraceDatum N hN B hB S hS).adjunction.counit.app KB)
    (projectiveLineTrace N hN A hA S hS) (projectiveLineTrace N hN B hB S hS)
    (projective φ N hN hA hB S hS) (unit φ S)
    (derivedTensorSingleUnitIso K).hom (derivedTensorSingleUnitIso KB).hom
  · simpa only [projectiveSource, projective, ordinaryFiniteP1Right, ordinaryFiniteTwistedPullback,
      derivedTensorRight, ordinaryFiniteTensor, ordinaryFinitePullback,
      Functor.comp_obj, Functor.flip_obj_obj, Functor.map_comp, Category.assoc,
      q, LA, LB, l, KB] using hπ
  · exact (projectiveLineTraceDatum N hN A hA S hS).counit_normalization K
  · exact (projectiveLineTraceDatum N hN B hB S hS).counit_normalization KB
  · exact ht
  · exact single_unit_square φ S K

private theorem line_counit_from_trace
    (φ : A →+* B) (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0) (hB : (N : B) = 0)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤)))
    (ht : projective φ N hN hA hB S hS ≫ projectiveLineTrace N hN B hB S hS =
      (scalarExtension φ S).map (projectiveLineTrace N hN A hA S hS) ≫ unit φ S)
    (K : DerivedCategoryModule A S) :
    (compactScalarMap φ (affineTraceLineCompactification S)).app
        ((affineTraceLineRight A N hA S).obj K) ≫
      (affineTraceLineLeft B S).map (lineSource φ N hN hA hB S hS K) ≫
      (affineTraceLineAdjunction B N hB (projectiveLineTraceTransport N hN B hB)
        S hS (projectiveLineTraceDatum N hN B hB S hS)).counit.app
          ((scalarExtension φ S).obj K) =
    (scalarExtension φ S).map
      ((affineTraceLineAdjunction A N hA (projectiveLineTraceTransport N hN A hA)
        S hS (projectiveLineTraceDatum N hN A hA S hS)).counit.app K) := by
  have h := compose_counit_scalar
    (affineTraceOpenAdjunction A S) (projectiveLineTraceDatum N hN A hA S hS).adjunction
    (affineTraceOpenAdjunction B S) (projectiveLineTraceDatum N hN B hB S hS).adjunction
    (scalarExtension φ (AffineSpace PUnit.{u + 1} S))
    (scalarExtension φ (ProjectiveLine S)) (scalarExtension φ S)
    (ExceptionalCoefficients.openIso φ (ProjectiveLine.affineChart S)).hom
    (scalarMate φ (ProjectiveLine S ↘ S)) K
    ((scalarPullbackIso φ (ProjectiveLine.affineChart S)).inv.app
      ((ordinaryFiniteP1Right A N hA S).obj K))
    (projectiveSource φ N hN hA hB S hS K)
    (by simpa only [affineTraceOpenAdjunction, affineTraceOpenLeft] using
      (open_scalar_counit φ (ProjectiveLine.affineChart S)
        ((ordinaryFiniteP1Right A N hA S).obj K)))
    (p1_counit_from_trace φ N hN hA hB S hS ht K)
  simpa only [compactScalarMap, ExceptionalCoefficients.compactSupportMap,
    affineTraceLineCompactification, Compactification.copy, Functor.comp_map,
    lineSource, affineTraceLineAdjunction, affineTraceComposeAdjunction_eq,
    affineTraceOpenLeft, affineTraceLineRight, affineTraceLineLeft,
    rightDerivedLowerShriekOfCompactification, ordinaryFinitePushforward,
    rightDerivedLowerStar, Functor.comp_obj, Category.assoc] using h

private theorem tower_counit_from_trace
    (φ : A →+* B) (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0) (hB : (N : B) = 0)
    (hp : ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (N : Γ(T, ⊤))),
      projective φ N hN hA hB T hT ≫ projectiveLineTrace N hN B hB T hT =
        (scalarExtension φ T).map (projectiveLineTrace N hN A hA T hT) ≫ unit φ T)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤)))
    (d : ℕ) (K : DerivedCategoryModule A S) :
    (towerLeft φ S d).app ((affineTraceRight A N hA S d).obj K) ≫
      (affineTraceLeft B S d).map (towerSource φ N hN hA hB S hS d K) ≫
      (affineTraceAdjunction B N hB (projectiveLineTraceTransport N hN B hB)
        (projectiveLineTraceDatum N hN B hB) S hS d).counit.app
          ((scalarExtension φ S).obj K) =
    (scalarExtension φ S).map
      ((affineTraceAdjunction A N hA (projectiveLineTraceTransport N hN A hA)
        (projectiveLineTraceDatum N hN A hA) S hS d).counit.app K) := by
  unfold affineTraceAdjunction
  let a := fun r ↦ affineTraceLineAdjunction A N hA
    (projectiveLineTraceTransport N hN A hA) (affineTraceTower S r)
    (affineTraceInvertible N S hS r)
    (@projectiveLineTraceDatum N hN A _ _ hA (affineTraceTower S r)
      (affineTraceNoetherian S r) (affineTraceInvertible N S hS r))
  let b := fun r ↦ affineTraceLineAdjunction B N hB
    (projectiveLineTraceTransport N hN B hB) (affineTraceTower S r)
    (affineTraceInvertible N S hS r)
    (@projectiveLineTraceDatum N hN B _ _ hB (affineTraceTower S r)
      (affineTraceNoetherian S r) (affineTraceInvertible N S hS r))
  change _ ≫ _ ≫ (affineTraceAdjunctionTower
    (C := fun r ↦ DerivedCategoryModule B (affineTraceTower S r)) b d).counit.app
      ((scalarExtension φ S).obj K) =
    (scalarExtension φ S).map ((affineTraceAdjunctionTower
      (C := fun r ↦ DerivedCategoryModule A (affineTraceTower S r)) a d).counit.app K)
  induction d with
  | zero =>
    simp only [towerLeft, affineTraceExchangeTower_zero, towerSource]
    change 𝟙 _ ≫ 𝟙 _ ≫ 𝟙 _ = (scalarExtension φ S).map (𝟙 K)
    simp
  | succ d ih =>
    let := affineTraceNoetherian S d
    let M := (affineTraceRight A N hA S d).obj K
    let q := towerSource φ N hN hA hB S hS d K
    have hn := (b d).counit.naturality q
    change (affineTraceLineLeft B (affineTraceTower S d)).map
        ((affineTraceLineRight B N hB (affineTraceTower S d)).map q) ≫
        (b d).counit.app _ = (b d).counit.app _ ≫ q at hn
    have h := line_counit_from_trace φ N hN hA hB (affineTraceTower S d)
      (affineTraceInvertible N S hS d) (hp _ _) M
    have hi : (compactScalarMap φ (affineTraceLineCompactification
        (affineTraceTower S d))).app ((affineTraceLineRight A N hA
          (affineTraceTower S d)).obj M) ≫
        (affineTraceLineLeft B (affineTraceTower S d)).map
          (lineSource φ N hN hA hB (affineTraceTower S d)
            (affineTraceInvertible N S hS d) M ≫
            (affineTraceLineRight B N hB (affineTraceTower S d)).map q) ≫
        (b d).counit.app ((affineTraceRight B N hB S d).obj
          ((scalarExtension φ S).obj K)) =
        (scalarExtension φ (affineTraceTower S d)).map ((a d).counit.app M) ≫ q := by
      rw [Functor.map_comp, Category.assoc, hn]
      simpa only [Category.assoc, a, b] using congrArg (fun z ↦ z ≫ q) h
    rw [affineTraceAdjunctionTower_counit_succ,
      affineTraceAdjunctionTower_counit_succ]
    simp only [towerLeft, affineTraceExchangeTower_succ, towerSource]
    change (_ ≫ (affineTraceLeft B S d).map
        ((compactScalarMap φ (affineTraceLineCompactification
          (affineTraceTower S d))).app ((affineTraceLineRight A N hA
            (affineTraceTower S d)).obj M))) ≫
      (affineTraceLeft B S d).map
        ((affineTraceLineLeft B (affineTraceTower S d)).map
          (lineSource φ N hN hA hB (affineTraceTower S d)
            (affineTraceInvertible N S hS d) M ≫
            (affineTraceLineRight B N hB (affineTraceTower S d)).map q)) ≫
      (affineTraceLeft B S d).map
        ((b d).counit.app ((affineTraceRight B N hB S d).obj
          ((scalarExtension φ S).obj K))) ≫
      (affineTraceAdjunctionTower
        (C := fun r ↦ DerivedCategoryModule B (affineTraceTower S r)) b d).counit.app _ = _
    have hi' := congrArg (fun z ↦ (affineTraceLeft B S d).map z) hi
    simp only [Functor.map_comp, Category.assoc] at hi'
    simp only [Functor.map_comp, Category.assoc]
    erw [reassoc_of% hi']
    have he := (towerLeft φ S d).naturality ((a d).counit.app M)
    simp only [Functor.comp_map] at he
    change _ ≫ (towerLeft φ S d).app M =
      (towerLeft φ S d).app
        ((affineTraceLineLeft A (affineTraceTower S d)).obj
          ((affineTraceRight A N hA S (d + 1)).obj K)) ≫ _ at he
    erw [← Category.assoc, ← Category.assoc, ← he]
    simp only [Category.assoc]
    rw [ih, ← Functor.map_comp]

private theorem compactComparison_eq (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ) :
    affineLinearCompactComparison N hN A hA S hS d =
      (affineTraceUnboundedCompactComparison A S d).app
        ((affineTraceRight A N hA S d).obj (ordinaryFiniteUnit A S)) := by
  let K : _root_.DerivedCategory.Plus
      (Sheaf (affineTraceTower S d).smallEtaleTopology (ModuleCat.{u + 1} A)) :=
    ⟨_, Exists.elim (exists_affineSpaceTopTrace N hN A hA) (fun _ ht ↦
      Exists.elim ht (fun _ hD ↦ (hD.2 S hS d).2.1))⟩
  apply Iso.ext
  change (affineTracePlusCompatibility A S d).inv.app K ≫
    _root_.DerivedCategory.Plus.ι.map
      ((affineTraceCompactSupportComparison A S d).hom.app K) ≫
      (rightDerivedLowerShriekPlusCompatibility (ModuleCat.{u + 1} A)
        (affineTraceProjection S d)).hom.app K =
    (affineTraceUnboundedCompactComparison A S d).hom.app
      (_root_.DerivedCategory.Plus.ι.obj K)
  apply (cancel_epi ((affineTracePlusCompatibility A S d).hom.app K)).mp
  simp only [Iso.hom_inv_id_app_assoc]
  exact (affineTraceUnboundedCompactComparison_restriction A S d K).symm

/-- The scalar square for every ordered affine tower follows from the projective
second-projection trace square over every Noetherian base.
Source: vector-bundle-purity proof paragraph 2; scalar-descent proof Steps 5--8.
Proof: the proper projection formula, scalar tensorator naturality, the normalized
single-unit equation and the supplied projective trace equation give the projective
counit square at arbitrary input. Compose with the open scalar counit square to obtain
the affine-line counit square. Induct on the coordinate count. At zero all arrows are
identities. At a successor, expand the composite counit; naturality moves the preceding
source arrow through the line counit, and the affine-line square replaces the inner
composite. Naturality of the preceding left exchange and the induction hypothesis finish
the tower square. Source compatibility writes affineCoefficient as the recursive source followed by
the appropriate right-functor unit. Counit naturality
therefore gives the counit equation for affineCoefficient. The bounded restriction theorem
identifies affineLinearCompactComparison with the unbounded comparison component.
Precompose the desired equation with scalar extension of its A-component, use compact
compatibility and naturality of the B-component, and cancel both comparison isomorphisms.
All intermediate bases are Noetherian; no tensor factor is permuted. Zero rings, N=1
and empty schemes are included.
(blueprint: lem-pur-vector-scalar-affine-induction). -/
theorem affine_of_projective (N : ℕ) (hN : 0 < N) (φ : A →+* B)
    (hA : (N : A) = 0) (hB : (N : B) = 0)
    (hp : ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (N : Γ(T, ⊤))),
      projective φ N hN hA hB T hT ≫ projectiveLineTrace N hN B hB T hT =
        (scalarExtension φ T).map (projectiveLineTrace N hN A hA T hT) ≫ unit φ T)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) :
    ∀ d : ℕ, affine φ N hN hA hB S hS d ≫ affineTrace N hN B hB S hS d =
        (scalarExtension φ S).map (affineTrace N hN A hA S hS d) ≫ unit φ S := by
  intro d
  let WA := (affineTraceRight A N hA S d).obj (ordinaryFiniteUnit A S)
  let WB := (affineTraceRight B N hB S d).obj (ordinaryFiniteUnit B S)
  let eA := affineTraceUnboundedCompactComparison A S d
  let eB := affineTraceUnboundedCompactComparison B S d
  have ht := tower_counit_from_trace φ N hN hA hB hp S hS d
    (ordinaryFiniteUnit A S)
  have hn := (affineTraceAdjunction B N hB (projectiveLineTraceTransport N hN B hB)
    (projectiveLineTraceDatum N hN B hB) S hS d).counit.naturality (unit φ S)
  simp only [Functor.comp_map, Functor.id_map] at hn
  have hc : (towerLeft φ S d).app WA ≫
      (affineTraceLeft B S d).map (affineCoefficient φ N hN hA hB S hS d) ≫
      affineTraceCounit B N hB (projectiveLineTraceTransport N hN B hB)
        (projectiveLineTraceDatum N hN B hB) S hS d =
    (scalarExtension φ S).map
      (affineTraceCounit A N hA (projectiveLineTraceTransport N hN A hA)
        (projectiveLineTraceDatum N hN A hA) S hS d) ≫ unit φ S := by
    simp only [affineTraceCounit]
    rw [affine_source_compatibility, Functor.map_comp, Category.assoc, hn]
    simpa only [affineTraceCounit, Category.assoc] using
      congrArg (fun z ↦ z ≫ unit φ S) ht
  rw [affineTrace, affineTrace, compactComparison_eq N hN A hA S hS d,
    compactComparison_eq N hN B hB S hS d]
  unfold affine
  apply (cancel_epi ((scalarExtension φ S).map (eA.hom.app WA))).1
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% (affine_compact_compatibility φ S d WA)]
  have he := eB.hom.naturality (affineCoefficient φ N hN hA hB S hS d)
  rw [← reassoc_of% he]
  simp only [Iso.app_inv, ← Functor.map_comp_assoc, eA, eB, WA,
    Iso.hom_inv_id_app_assoc]
  exact hc

end AlgebraicGeometry.Etale.VectorTraceScalar
