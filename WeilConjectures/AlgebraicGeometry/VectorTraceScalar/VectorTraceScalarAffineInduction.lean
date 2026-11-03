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

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option maxRecDepth 2048
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open WeilConjectures.PurityFiniteSetting
open scoped CategoryTheory.Functor
open AlgebraicGeometry.Etale (purityScalarSingleMap purityScalarUnitMap)
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

end AlgebraicGeometry.Etale.VectorTraceScalar
