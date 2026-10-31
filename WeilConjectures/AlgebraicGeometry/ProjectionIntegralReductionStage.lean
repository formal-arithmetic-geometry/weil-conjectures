/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectionIntegralReductionCoordinates
public import WeilConjectures.AlgebraicGeometry.ProjectionCoherenceComparisons
import all WeilConjectures.AlgebraicGeometry.FiniteProjectionActionLaws
import WeilConjectures.AlgebraicGeometry.CompletedPullbackTensorCoherentConstruction
import WeilConjectures.SixFunctors.IntegralSystemTensorComposition
import WeilConjectures.SixFunctors.IntegralCompactificationSystemRealization
import WeilConjectures.AlgebraicGeometry.IntegralProjectionReductionNormalization
import all WeilConjectures.AlgebraicGeometry.IntegralProperTensorPullbackReduction
import all WeilConjectures.AlgebraicGeometry.IntegralProjectionSupportFactorCoordinates
import WeilConjectures.AlgebraicGeometry.IntegralProjectionSupportEvaluation
import WeilConjectures.AlgebraicGeometry.IntegralProjectionTensorEvaluation
import WeilConjectures.AlgebraicGeometry.IntegralSupportReductionNormalization
import all WeilConjectures.AlgebraicGeometry.DerivedPullbackTensorFiniteConstraints
import WeilConjectures.AlgebraicGeometry.IntegralReductionJointFaithfulness
import all WeilConjectures.AlgebraicGeometry.SystemProjectionFormulaCoherence

/-! Finite-level reduction of the integral projection action. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option Elab.async false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u v w
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale
namespace WeilConjectures
open IntegralProjectionReduction

open CategoryTheory.MonoidalCategory
open IntegralSystemRealization

attribute [local irreducible] pullbackTensorCalculus
  integralCompletedTensor integralDerivedPullback
  HasDerivedCategory.standard
  Scheme.residueField CategoryTheory.constantSheaf
  pullbackTensorSequenceDerived CategoryTheory.Functor.mapDerivedCategory
  IntegralSystemRealization.supportEvaluation
  IntegralSystemRealization.properProjection IntegralSystemRealization.compactificationProjection

attribute [local implicit_reducible] CoefficientClosedStructure.tensor
  Functor.curryObjProdComp openTensorLeft openTensorRight pullbackTensorReferenceTensor
  constructibleIntegralTensor
  FixProjectionCompactification.identitySquare compactSupportProjectionSquare
  sixFunctorIntegralReduction coefficientFiniteDerivedExtension sixFunctorFiniteSupport
  sfIntrinsicCompactSupport sfAmbientCompactSupportCandidate
  scalarReductionSourceDerived scalarReductionTargetDerived
  integralCoefficientSheaf integralCoefficientCommRingSheaf
  integralOperationsCommHasDerivedCategory integralCompletedRingHasDerivedCategory
  integralTowerHasDerivedCategory coefficientFiniteHasDerived reductionModulesHasDerivedCategory
  SemilinearSections.moduleAbelian sixFunctorFactorCompactification
  SixFunctorCompactifiedSquare.compactification
attribute [local irreducible] CompactSupportFiniteProjection.tensor
  evaluatedSource evaluatedTarget evaluatedInput
  evaluatedSupport evaluatedPull liftedTensorEvaluation
  CompactSupportFiniteProjection.component
  compactSupportProperProjection
attribute [local implicit_reducible] CompactSupportFiniteProjection.partialTensor torReduction
  compactSupportProjectionComponent

private theorem tensor_naturality_left
    {A B : Type*} [Category A] [Category B] [MonoidalCategory B]
    (T : A ⥤ A ⥤ A) (R : A ⥤ B)
    (t : Functor.uncurry.obj T ⋙ R ≅
      (R.prod R) ⋙ MonoidalCategory.tensor B)
    {P Q : A} (x : P ⟶ Q) (N : A) :
    R.map ((T.map x).app N) ≫ t.hom.app (Q, N) =
      t.hom.app (P, N) ≫ R.map x ▷ R.obj N := by
  simpa [Functor.uncurry] using t.hom.naturality (Prod.mkHom x (𝟙 N))

private def action_input
    {A B A' B' : Type*} [Category A] [Category B] [Category A'] [Category B']
    [MonoidalCategory A']
    (TX : A ⥤ A ⥤ A) (RX : A ⥤ A') (RY : B ⥤ B') (U : B ⥤ A) (U' : B' ⥤ A')
    (t : Functor.uncurry.obj TX ⋙ RX ≅
      (RX.prod RX) ⋙ MonoidalCategory.tensor A')
    (u : U ⋙ RX ≅ RY ⋙ U') (K : A) (L : B) :
    RX.obj ((TX.obj K).obj (U.obj L)) ≅ RX.obj K ⊗ U'.obj (RY.obj L) :=
  t.app (K, U.obj L) ≪≫ tensorIso (Iso.refl _) (u.app L)

private theorem action_input_assoc
    {A B A' B' : Type*} [Category A] [Category B] [Category A'] [Category B']
    [MonoidalCategory A'] [MonoidalCategory B']
    (TX : A ⥤ A ⥤ A) (TY : B ⥤ B ⥤ B)
    (RX : A ⥤ A') (RY : B ⥤ B') (U : B ⥤ A) (U' : B' ⥤ A')
    (tX : Functor.uncurry.obj TX ⋙ RX ≅
      (RX.prod RX) ⋙ MonoidalCategory.tensor A')
    (tY : Functor.uncurry.obj TY ⋙ RY ≅
      (RY.prod RY) ⋙ MonoidalCategory.tensor B')
    (u : U ⋙ RX ≅ RY ⋙ U')
    (aX : ∀ K M N, (TX.obj ((TX.obj K).obj M)).obj N ≅
      (TX.obj K).obj ((TX.obj M).obj N))
    (μ : ∀ L N, U.obj ((TY.obj L).obj N) ⟶ (TX.obj (U.obj L)).obj (U.obj N))
    (μ' : ∀ L N, U'.obj (L ⊗ N) ⟶ U'.obj L ⊗ U'.obj N)
    (haX : ∀ K M N, RX.map (aX K M N).hom ≫
      tX.hom.app (K, (TX.obj M).obj N) ≫ RX.obj K ◁ tX.hom.app (M, N) =
        tX.hom.app ((TX.obj K).obj M, N) ≫ tX.hom.app (K, M) ▷ RX.obj N ≫
          (α_ (RX.obj K) (RX.obj M) (RX.obj N)).hom)
    (hμ : ∀ L N, RX.map (μ L N) ≫ tX.hom.app (U.obj L, U.obj N) ≫
      (u.hom.app L ⊗ₘ u.hom.app N) =
        u.hom.app ((TY.obj L).obj N) ≫ U'.map (tY.hom.app (L, N)) ≫
          μ' (RY.obj L) (RY.obj N)) (K : A) (L N : B) :
    let b := action_input TX RX RY U U' tX u
    RX.map ((TX.obj K).map (μ L N) ≫ (aX K (U.obj L) (U.obj N)).inv) ≫
      (b ((TX.obj K).obj (U.obj L)) N).hom ≫
        (b K L).hom ▷ U'.obj (RY.obj N) =
      (b K ((TY.obj L).obj N)).hom ≫
        RX.obj K ◁ U'.map (tY.hom.app (L, N)) ≫
        RX.obj K ◁ μ' (RY.obj L) (RY.obj N) ≫
          (α_ (RX.obj K) (U'.obj (RY.obj L)) (U'.obj (RY.obj N))).inv := by
  have ha (M P : A) :
      RX.map (aX K M P).inv ≫ tX.hom.app ((TX.obj K).obj M, P) ≫
        tX.hom.app (K, M) ▷ RX.obj P =
      tX.hom.app (K, (TX.obj M).obj P) ≫ RX.obj K ◁ tX.hom.app (M, P) ≫
        (α_ (RX.obj K) (RX.obj M) (RX.obj P)).inv := by
    apply (cancel_epi (RX.map (aX K M P).hom)).mp
    simp only [← RX.map_comp_assoc, Iso.hom_inv_id, RX.map_id, Category.id_comp]
    erw [reassoc_of% (haX K M P), Iso.hom_inv_id, Category.comp_id]
  dsimp only [action_input]
  simp only [Iso.trans_hom, Iso.app_hom, tensorIso_hom, Iso.refl_hom,
    MonoidalCategory.tensorHom_def, id_whiskerRight, Category.id_comp, Functor.map_comp,
    comp_whiskerRight, Category.assoc]
  erw [whisker_exchange_assoc, reassoc_of% (ha (U.obj L) (U.obj N))]
  erw [← associator_inv_naturality_right_assoc,
    ← associator_inv_naturality_middle]
  have ht := tX.hom.naturality (Prod.mkHom (𝟙 K) (μ L N))
  have ht' : RX.map ((TX.obj K).map (μ L N)) ≫
      tX.hom.app (K, (TX.obj (U.obj L)).obj (U.obj N)) =
    tX.hom.app (K, U.obj ((TY.obj L).obj N)) ≫ RX.obj K ◁ RX.map (μ L N) := by
    simpa [Functor.uncurry] using ht
  erw [reassoc_of% ht']
  have hw := congrArg (fun k ↦ RX.obj K ◁ k) (hμ L N)
  simp only [whiskerLeft_comp, tensorHom_def'] at hw
  erw [reassoc_of% hw]

/-- Transport a right action through specified natural tensor and functor comparisons. -/
private theorem transport_action
    {A B A' B' : Type*} [Category A] [Category B] [Category A'] [Category B']
    [MonoidalCategory A'] [MonoidalCategory B']
    (TX : A ⥤ A ⥤ A) (TY : B ⥤ B ⥤ B)
    (RX : A ⥤ A') (RY : B ⥤ B') (F : A ⥤ B) (U : B ⥤ A)
    (F' : A' ⥤ B') (U' : B' ⥤ A')
    (t : Functor.uncurry.obj TY ⋙ RY ≅
      (RY.prod RY) ⋙ MonoidalCategory.tensor B')
    (q : F ⋙ RY ≅ RX ⋙ F')
    (b : ∀ K L, RX.obj ((TX.obj K).obj (U.obj L)) ≅
      RX.obj K ⊗ U'.obj (RY.obj L))
    (aX : ∀ K M N, (TX.obj ((TX.obj K).obj M)).obj N ≅
      (TX.obj K).obj ((TX.obj M).obj N))
    (aY : ∀ K M N, (TY.obj ((TY.obj K).obj M)).obj N ≅
      (TY.obj K).obj ((TY.obj M).obj N))
    (μ : ∀ L N, U.obj ((TY.obj L).obj N) ⟶ (TX.obj (U.obj L)).obj (U.obj N))
    (μ' : ∀ L N, U'.obj (L ⊗ N) ⟶ U'.obj L ⊗ U'.obj N)
    (π : ∀ K L, (TY.obj (F.obj K)).obj L ⟶ F.obj ((TX.obj K).obj (U.obj L)))
    (π' : ∀ K L, F'.obj K ⊗ L ⟶ F'.obj (K ⊗ U'.obj L))
    (hπ : ∀ K L, RY.map (π K L) ≫ q.hom.app ((TX.obj K).obj (U.obj L)) ≫
      F'.map (b K L).hom =
        t.hom.app (F.obj K, L) ≫ q.hom.app K ▷ RY.obj L ≫ π' (RX.obj K) (RY.obj L))
    (hπl : ∀ {K K' : A'} (x : K ⟶ K') (L : B'),
      F'.map x ▷ L ≫ π' K' L = π' K L ≫ F'.map (x ▷ U'.obj L))
    (hπr : ∀ K {L L' : B'} (y : L ⟶ L'),
      F'.obj K ◁ y ≫ π' K L' = π' K L ≫ F'.map (K ◁ U'.map y))
    (haY : ∀ K L N, RY.map (aY K L N).hom ≫
      t.hom.app (K, (TY.obj L).obj N) ≫ RY.obj K ◁ t.hom.app (L, N) =
        t.hom.app ((TY.obj K).obj L, N) ≫ t.hom.app (K, L) ▷ RY.obj N ≫
          (α_ (RY.obj K) (RY.obj L) (RY.obj N)).hom)
    (hb : ∀ K L N,
      RX.map ((TX.obj K).map (μ L N) ≫ (aX K (U.obj L) (U.obj N)).inv) ≫
        (b ((TX.obj K).obj (U.obj L)) N).hom ≫
          (b K L).hom ▷ U'.obj (RY.obj N) =
      (b K ((TY.obj L).obj N)).hom ≫
        RX.obj K ◁ U'.map (t.hom.app (L, N)) ≫
        RX.obj K ◁ μ' (RY.obj L) (RY.obj N) ≫
          (α_ (RX.obj K) (U'.obj (RY.obj L)) (U'.obj (RY.obj N))).inv)
    (hact : ∀ K L N, π' K L ▷ N ≫ π' (K ⊗ U'.obj L) N =
      (α_ (F'.obj K) L N).hom ≫ π' K (L ⊗ N) ≫
        F'.map (K ◁ μ' L N ≫ (α_ K (U'.obj L) (U'.obj N)).inv))
    (K : A) (L N : B) :
    RY.map ((TY.map (π K L)).app N ≫ π ((TX.obj K).obj (U.obj L)) N) =
      RY.map ((aY (F.obj K) L N).hom ≫ π K ((TY.obj L).obj N) ≫
        F.map ((TX.obj K).map (μ L N)) ≫ F.map (aX K (U.obj L) (U.obj N)).inv) := by
  let v := (TX.obj K).map (μ L N) ≫ (aX K (U.obj L) (U.obj N)).inv
  let s := t.hom.app ((TY.obj (F.obj K)).obj L, N) ≫
    t.hom.app (F.obj K, L) ▷ RY.obj N ≫
      (q.hom.app K ▷ RY.obj L) ▷ RY.obj N
  let r := q.hom.app ((TX.obj ((TX.obj K).obj (U.obj L))).obj (U.obj N)) ≫
    F'.map (b ((TX.obj K).obj (U.obj L)) N).hom ≫
      F'.map ((b K L).hom ▷ U'.obj (RY.obj N))
  apply (cancel_mono r).mp
  have hleft :
      RY.map ((TY.map (π K L)).app N ≫ π ((TX.obj K).obj (U.obj L)) N) ≫ r =
        s ≫ π' (RX.obj K) (RY.obj L) ▷ RY.obj N ≫
          π' (RX.obj K ⊗ U'.obj (RY.obj L)) (RY.obj N) := by
    dsimp only [r, s]
    simp only [Functor.map_comp, Category.assoc]
    erw [reassoc_of% (hπ ((TX.obj K).obj (U.obj L)) N),
      ← hπl (b K L).hom (RY.obj N),
      reassoc_of% (tensor_naturality_left TY RY t (π K L) N)]
    have hw := congrArg (fun k ↦ k ▷ RY.obj N) (hπ K L)
    simp only [comp_whiskerRight] at hw
    erw [reassoc_of% hw]
  have hright :
      RY.map ((aY (F.obj K) L N).hom ≫ π K ((TY.obj L).obj N) ≫
        F.map ((TX.obj K).map (μ L N)) ≫ F.map (aX K (U.obj L) (U.obj N)).inv) ≫ r =
      s ≫ (α_ (F'.obj (RX.obj K)) (RY.obj L) (RY.obj N)).hom ≫
        π' (RX.obj K) (RY.obj L ⊗ RY.obj N) ≫
          F'.map (RX.obj K ◁ μ' (RY.obj L) (RY.obj N) ≫
            (α_ (RX.obj K) (U'.obj (RY.obj L)) (U'.obj (RY.obj N))).inv) := by
    dsimp only [r, s]
    erw [← F.map_comp]
    simp only [RY.map_comp, Category.assoc]
    erw [reassoc_of% (q.hom.naturality v)]
    simp only [← F'.map_comp]
    erw [hb]
    simp only [Functor.map_comp]
    erw [reassoc_of% (hπ K ((TY.obj L).obj N)),
      ← reassoc_of% (hπr (RX.obj K) (t.hom.app (L, N))),
      ← whisker_exchange_assoc, reassoc_of% (haY (F.obj K) L N),
      ← associator_naturality_left_assoc]
    rfl
  erw [hleft, hright, hact, Category.assoc]

private theorem curried_action_natural_left
    {A B : Type*} [Category A] [Category B] [MonoidalCategory A] [MonoidalCategory B]
    (G : A ⥤ B) (P : B ⥤ A)
    (p : G ⋙ Functor.curryObj (MonoidalCategory.tensor B) ⟶
      (Functor.postcompose₂.obj G).obj
        ((((Functor.whiskeringLeft₂ A).obj (𝟭 A)).obj P).obj
          (Functor.curryObj (MonoidalCategory.tensor A))))
    {K K' : A} (x : K ⟶ K') (L : B) :
    G.map x ▷ L ≫ (p.app K').app L =
      (p.app K).app L ≫ G.map (x ▷ P.obj L) := by
  have h := congr_app (p.naturality x) L
  change (G.map x ⊗ₘ 𝟙 L) ≫ (p.app K').app L =
    (p.app K).app L ≫ G.map (x ⊗ₘ 𝟙 (P.obj L)) at h
  erw [tensorHom_id x (P.obj L), tensorHom_id (G.map x) L] at h
  exact h

private def monoidal_comparison
    {A B : Type*} [Category A] [Category B] [MonoidalCategory A] [MonoidalCategory B]
    (S : A ⥤ B)
    (d : MonoidalCategory.tensor A ⋙ S ≅ (S.prod S) ⋙ MonoidalCategory.tensor B) :
    (Functor.postcompose₂.obj S).obj (curriedTensor A) ≅
      (((Functor.whiskeringLeft₂ B).obj S).obj S).obj (curriedTensor B) :=
  NatIso.ofComponents (fun M ↦ NatIso.ofComponents (fun N ↦ d.app (M, N)) (by
    intro N N' y
    change S.map (M ◁ y) ≫ d.hom.app (M, N') =
      d.hom.app (M, N) ≫ S.obj M ◁ S.map y
    have h := d.hom.naturality (Prod.mkHom (𝟙 M) y)
    change S.map (𝟙 M ⊗ₘ y) ≫ d.hom.app (M, N') =
      d.hom.app (M, N) ≫ (S.map (𝟙 M) ⊗ₘ S.map y) at h
    simp only [S.map_id] at h
    rw [id_tensorHom M y, id_tensorHom (S.obj M) (S.map y)] at h
    exact h)) (by
    intro M M' x
    ext N
    change S.map (x ▷ N) ≫ d.hom.app (M', N) =
      d.hom.app (M, N) ≫ S.map x ▷ S.obj N
    have h := d.hom.naturality (Prod.mkHom x (𝟙 N))
    change S.map (x ⊗ₘ 𝟙 N) ≫ d.hom.app (M', N) =
      d.hom.app (M, N) ≫ (S.map x ⊗ₘ S.map (𝟙 N)) at h
    simp only [S.map_id] at h
    rw [tensorHom_id x N, tensorHom_id (S.map x) (S.obj N)] at h
    exact h)

attribute [local implicit_reducible] monoidal_comparison

private theorem proper_comparison_component
    {A B : Type*} [Category A] [Category B] [MonoidalCategory A] [MonoidalCategory B]
    {F : B ⥤ A} {G : A ⥤ B} (adj : F ⊣ G)
    (d : MonoidalCategory.tensor B ⋙ F ≅ (F.prod F) ⋙ MonoidalCategory.tensor A)
    (M : A) (N : B) :
    (((adj.rightAdjointProjectionMap
      (T_C := Functor.curry.obj (MonoidalCategory.tensor A))
      (T_D := Functor.curry.obj (MonoidalCategory.tensor B))
      (Functor.curry.mapIso d ≪≫
        Functor.curryObjProdComp F F (MonoidalCategory.tensor A)).hom).app M).app N) =
      (((adj.rightAdjointProjectionMap (T_C := curriedTensor A) (T_D := curriedTensor B)
        (monoidal_comparison F d).hom).app M).app N) := by
  simp only [Adjunction.rightAdjointProjectionMap_app_app,
    Functor.curryObjProdComp, Functor.curry, Functor.curryObj, Functor.mapIso,
    Iso.trans, NatIso.ofComponents, NatTrans.comp_app, monoidal_comparison,
    MonoidalCategory.tensor, Category.comp_id, tensorHom_id, Iso.refl_hom, Iso.app_hom,
    Functor.id_obj, curriedTensor_obj_obj, curriedTensor_map_app,
    Functor.comp_obj, Functor.prod_obj]

private theorem system_proper_component
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (o : Operations l E)
    {X Y : Scheme.{u}} (f : X ⟶ Y) (M : System l E X) (N : System l E Y) :
    let := (calculus l E X).systemClosed.monoidal
    let := (calculus l E Y).systemClosed.monoidal
    ((properProjection l E o f).app M).app N =
      (((o.direct f).adj.rightAdjointProjectionMap
        (monoidal_comparison (pull l E f) (pullbackTensorSystemComparison l E f)).hom).app M
          ).app N := by
  let := (calculus l E X).systemClosed.monoidal
  let := (calculus l E Y).systemClosed.monoidal
  unfold properProjection
  exact proper_comparison_component (o.direct f).adj (pullbackTensorSystemComparison l E f) M N

private theorem system_tensor_assoc
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] {X Y : Scheme.{u}} (f : X ⟶ Y)
    (A B C : System l E Y) :
    let := (calculus l E X).systemClosed.monoidal
    let := (calculus l E Y).systemClosed.monoidal
    let S := pull l E f
    let d := pullbackTensorSystemComparison l E f
    d.hom.app (A ⊗ B, C) ≫ d.hom.app (A, B) ▷ S.obj C ≫ (α_ _ _ _).hom =
      S.map (α_ A B C).hom ≫ d.hom.app (A, B ⊗ C) ≫
        S.obj A ◁ d.hom.app (B, C) := by
  simpa only [CoefficientClosedStructure.tensor, MonoidalCategory.tensor,
    Functor.prod_obj, id_tensorHom, tensorHom_id] using
    (pullbackTensorSystemComparison_associativity l E f A B C).symm

private theorem system_tensor_cast
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] {X Y : Scheme.{u}} (f g : X ⟶ Y) (h : f = g)
    (A B : System l E Y) :
    let := (calculus l E X).systemClosed.monoidal
    let := (calculus l E Y).systemClosed.monoidal
    eqToHom (congrArg (fun k ↦ (pull l E k).obj (A ⊗ B)) h) ≫
      (pullbackTensorSystemComparison l E g).hom.app (A, B) =
    (pullbackTensorSystemComparison l E f).hom.app (A, B) ≫
      (eqToHom (congrArg (fun k ↦ (pull l E k).obj A) h) ⊗ₘ
        eqToHom (congrArg (fun k ↦ (pull l E k).obj B) h)) := by
  subst g
  simp only [eqToHom_refl, id_tensorHom_id, Category.id_comp,
    Functor.prod_obj]
  erw [Category.comp_id]

private theorem open_natural_left
    {A B : Type*} [Category A] [Category B] [MonoidalCategory A] [MonoidalCategory B]
    (J : A ⥤ B) (U : B ⥤ A)
    (p : (J.prod (𝟭 B)) ⋙ MonoidalCategory.tensor B ≅
      ((𝟭 A).prod U) ⋙ MonoidalCategory.tensor A ⋙ J)
    {K K' : A} (x : K ⟶ K') (L : B) :
    J.map x ▷ L ≫ p.hom.app (K', L) =
      p.hom.app (K, L) ≫ J.map (x ▷ U.obj L) := by
  have h := p.hom.naturality (Prod.mkHom x (𝟙 L))
  change (J.map x ⊗ₘ 𝟙 L) ≫ p.hom.app (K', L) =
    p.hom.app (K, L) ≫ J.map (x ⊗ₘ U.map (𝟙 L)) at h
  erw [U.map_id, tensorHom_id x (U.obj L), tensorHom_id (J.map x) L] at h
  exact h

private theorem open_natural_right
    {A B : Type*} [Category A] [Category B] [MonoidalCategory A] [MonoidalCategory B]
    (J : A ⥤ B) (U : B ⥤ A)
    (p : (J.prod (𝟭 B)) ⋙ MonoidalCategory.tensor B ≅
      ((𝟭 A).prod U) ⋙ MonoidalCategory.tensor A ⋙ J)
    (K : A) {L L' : B} (y : L ⟶ L') :
    J.obj K ◁ y ≫ p.hom.app (K, L') =
      p.hom.app (K, L) ≫ J.map (K ◁ U.map y) := by
  have h := p.hom.naturality (Prod.mkHom (𝟙 K) y)
  change (J.map (𝟙 K) ⊗ₘ y) ≫ p.hom.app (K, L') =
    p.hom.app (K, L) ≫ J.map (𝟙 K ⊗ₘ U.map y) at h
  erw [J.map_id, id_tensorHom K (U.map y), id_tensorHom (J.obj K) y] at h
  exact h

private theorem system_open_action
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (o : Operations l E) (c : Compositors l E o)
    (a : OpenComparisons l E o c) {X Y : Scheme.{u}} (j : X ⟶ Y)
    [IsOpenImmersion j] (K : System l E X) (L N : System l E Y) :
    let := (calculus l E X).systemClosed.monoidal
    let := (calculus l E Y).systemClosed.monoidal
    (a.projection j).hom.app (K, L) ▷ N ≫
        (a.projection j).hom.app (K ⊗ (pull l E j).obj L, N) =
      (α_ ((Operations.shriek l E o j).obj K) L N).hom ≫
        (a.projection j).hom.app (K, L ⊗ N) ≫
        (Operations.shriek l E o j).map
          (K ◁ (pullbackTensorSystemComparison l E j).hom.app (L, N) ≫
            (α_ K ((pull l E j).obj L) ((pull l E j).obj N)).inv) := by
  let := (calculus l E X).systemClosed.monoidal
  let := (calculus l E Y).systemClosed.monoidal
  let S := pull l E j
  let J := Operations.shriek l E o j
  let d := pullbackTensorSystemComparison l E j
  let δ := (monoidal_comparison S d).inv
  have hd := system_tensor_assoc l E j
  have hp (M : System l E X) (B : System l E Y) :
      (a.projection j).inv.app (M, B) =
        (((o.extension j).adj.projectionMap S
          (curriedTensor (System l E X)) (curriedTensor (System l E Y)) δ).app M).app B := by
    apply ((o.extension j).adj.homEquiv _ _).injective
    rw [a.projection_transpose]
    erw [Adjunction.projectionMap_app_app, Equiv.apply_symm_apply]
    change (_ ⊗ₘ 𝟙 _) ≫ _ = _ ▷ _ ≫ _
    rw [tensorHom_id]
    rfl
  have hδ (A B C : System l E Y) :
      (α_ (S.obj A) (S.obj B) (S.obj C)).hom ≫
        S.obj A ◁ d.inv.app (B, C) ≫ (δ.app A).app (B ⊗ C) ≫
        S.map (α_ A B C).inv =
      (δ.app A).app B ▷ S.obj C ≫ (δ.app (A ⊗ B)).app C := by
    have h := inverse_comparison_assoc S (fun A B ↦ d.app (A, B)) hd A B C
    change (α_ _ _ _).hom ≫ S.obj A ◁ (d.app (B, C)).inv ≫
      (d.app (A, B ⊗ C)).inv ≫ S.map (α_ A B C).inv =
        (d.app (A, B)).inv ▷ S.obj C ≫ (d.app (A ⊗ B, C)).inv
    erw [h, Iso.hom_inv_id_assoc]
  let hi (B C : System l E Y) : IsIso (d.hom.app (B, C)) :=
    (d.app (B, C)).isIso_hom
  have hinv (B C : System l E Y) : inv (d.hom.app (B, C)) = d.inv.app (B, C) :=
    IsIso.inv_eq_of_hom_inv_id (d.hom_inv_id_app (B, C))
  have h := projection_map_assoc_data (o.extension j).adj S
    (fun B C ↦ d.inv.app (B, C)) δ hδ K L N
  simp only [← hp] at h
  simpa only [Iso.symm_inv, Iso.app_inv, Iso.app_hom, IsIso.inv_hom_id,
    Iso.inv_hom_id] using
    inverse_action_assoc J S (fun B C ↦ d.hom.app (B, C))
      (fun M B ↦ (a.projection j).symm.app (M, B)) K L N (by
        simpa only [Iso.symm_hom, Iso.app_hom, Iso.app_inv, Iso.inv_hom_id, hinv] using h)

private theorem system_compactification_component
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (o : Operations l E) (c : Compositors l E o)
    (a : OpenComparisons l E o c) {X Y : Scheme.{u}} {f : X ⟶ Y}
    (d : Compactification f) (K : System l E X) (L : System l E Y) :
    let := (calculus l E X).systemClosed.monoidal
    let := (calculus l E Y).systemClosed.monoidal
    let := (calculus l E d.Z).systemClosed.monoidal
    compactificationProjection l E o c a d K L =
      composite_projection_components
        (Operations.push l E o d.g) (Operations.shriek l E o d.i) (pull l E d.g)
        (fun M B ↦ ((properProjection l E o d.g).app M).app B)
        (fun M B ↦ (a.projection d.i).hom.app (M, B))
        (fun B ↦ (c.pullComp d.i d.g).inv.app B ≫
          eqToHom (congrArg (fun g : X ⟶ Y ↦ (pull l E g).obj B) d.comm.symm)) K L := by
  let := (calculus l E X).systemClosed.monoidal
  let := (calculus l E Y).systemClosed.monoidal
  let := (calculus l E d.Z).systemClosed.monoidal
  unfold IntegralSystemRealization.compactificationProjection
  dsimp only [composite_projection_components]
  simp only [CoefficientClosedStructure.tensor, MonoidalCategory.tensor,
    Functor.map_comp]
  erw [id_tensorHom K ((c.pullComp d.i d.g).inv.app L ≫
    eqToHom (congrArg (fun g : X ⟶ Y ↦ (pull l E g).obj L) d.comm.symm))]

private theorem system_compositor_tensor
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (o : Operations l E) (c : Compositors l E o)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (d : Compactification f)
    (B B' : System l E Y) :
    let := (calculus l E X).systemClosed.monoidal
    let := (calculus l E Y).systemClosed.monoidal
    let := (calculus l E d.Z).systemClosed.monoidal
    let P := pull l E d.g
    let Q := pull l E d.i
    let U := pull l E f
    let e (B : System l E Y) : Q.obj (P.obj B) ⟶ U.obj B :=
      (c.pullComp d.i d.g).inv.app B ≫
        eqToHom (congrArg (fun g : X ⟶ Y ↦ (pull l E g).obj B) d.comm.symm)
    e (B ⊗ B') ≫ (pullbackTensorSystemComparison l E f).hom.app (B, B') =
      Q.map ((pullbackTensorSystemComparison l E d.g).hom.app (B, B')) ≫
        (pullbackTensorSystemComparison l E d.i).hom.app (P.obj B, P.obj B') ≫
          (e B ⊗ₘ e B') := by
  let := (calculus l E X).systemClosed.monoidal
  let := (calculus l E Y).systemClosed.monoidal
  let := (calculus l E d.Z).systemClosed.monoidal
  let P := pull l E d.g
  let Q := pull l E d.i
  let U := pull l E f
  let e (B : System l E Y) : Q.obj (P.obj B) ⟶ U.obj B :=
    (c.pullComp d.i d.g).inv.app B ≫
      eqToHom (congrArg (fun g : X ⟶ Y ↦ (pull l E g).obj B) d.comm.symm)
  have h := integralSystemTensorComposition l E o c d.i d.g B B'
  apply (cancel_epi ((c.pullComp d.i d.g).hom.app (B ⊗ B'))).mp
  dsimp only [e]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
  change (c.pullComp d.i d.g).hom.app (B ⊗ B') ≫
    Q.map ((pullbackTensorSystemComparison l E d.g).hom.app (B, B')) ≫
    (pullbackTensorSystemComparison l E d.i).hom.app (P.obj B, P.obj B') =
    (pullbackTensorSystemComparison l E (d.i ≫ d.g)).hom.app (B, B') ≫
      ((c.pullComp d.i d.g).hom.app B ⊗ₘ (c.pullComp d.i d.g).hom.app B') at h
  erw [reassoc_of% h]
  erw [tensorHom_comp_tensorHom]
  simp only [Iso.hom_inv_id_app_assoc]
  exact system_tensor_cast l E (d.i ≫ d.g) f d.comm.symm B B'

private theorem system_proper_action
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (o : Operations l E)
    {X Y : Scheme.{u}} (f : X ⟶ Y) (M : System l E X) (B B' : System l E Y) :
    let := (calculus l E X).systemClosed.monoidal
    let := (calculus l E Y).systemClosed.monoidal
    let P := pull l E f
    let G := Operations.push l E o f
    ((properProjection l E o f).app M).app B ▷ B' ≫
      ((properProjection l E o f).app (M ⊗ P.obj B)).app B' ≫
        G.map (α_ M (P.obj B) (P.obj B')).hom =
    (α_ (G.obj M) B B').hom ≫ ((properProjection l E o f).app M).app (B ⊗ B') ≫
      G.map (M ◁ (pullbackTensorSystemComparison l E f).hom.app (B, B')) := by
  let := (calculus l E X).systemClosed.monoidal
  let := (calculus l E Y).systemClosed.monoidal
  let P := pull l E f
  let G := Operations.push l E o f
  simp only [system_proper_component l E o f]
  exact (o.direct f).adj.rightAdjointProjectionMap_associativity
    (monoidal_comparison P (pullbackTensorSystemComparison l E f)).hom
    (system_tensor_assoc l E f) M B B'

set_option maxHeartbeats 2000000 in
-- Instantiate the composite action on the large derived coefficient-system categories.
private theorem system_compactification_action
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (o : Operations l E) (c : Compositors l E o)
    (a : OpenComparisons l E o c) {X Y : Scheme.{u}} {f : X ⟶ Y}
    (d : Compactification f) (K : System l E X) (L N : System l E Y) :
    let := (calculus l E X).systemClosed.monoidal
    let := (calculus l E Y).systemClosed.monoidal
    let F := Operations.shriek l E o d.i ⋙ Operations.push l E o d.g
    compactificationProjection l E o c a d K L ▷ N ≫
        compactificationProjection l E o c a d (K ⊗ (pull l E f).obj L) N =
      (α_ (F.obj K) L N).hom ≫
        compactificationProjection l E o c a d K (L ⊗ N) ≫
        F.map (K ◁ (pullbackTensorSystemComparison l E f).hom.app (L, N) ≫
          (α_ K ((pull l E f).obj L) ((pull l E f).obj N)).inv) := by
  dsimp only
  let := (calculus l E X).systemClosed.monoidal
  let := (calculus l E Y).systemClosed.monoidal
  let := (calculus l E d.Z).systemClosed.monoidal
  let G := Operations.push l E o d.g
  let J := Operations.shriek l E o d.i
  let P := pull l E d.g
  let Q := pull l E d.i
  let U := pull l E f
  let e (B : System l E Y) : Q.obj (P.obj B) ⟶ U.obj B :=
    (c.pullComp d.i d.g).inv.app B ≫
      eqToHom (congrArg (fun g : X ⟶ Y ↦ (pull l E g).obj B) d.comm.symm)
  have he (B B' : System l E Y) :
      e (B ⊗ B') ≫ (pullbackTensorSystemComparison l E f).hom.app (B, B') =
        Q.map ((pullbackTensorSystemComparison l E d.g).hom.app (B, B')) ≫
          (pullbackTensorSystemComparison l E d.i).hom.app (P.obj B, P.obj B') ≫
            (e B ⊗ₘ e B') :=
    system_compositor_tensor l E o c d B B'
  have hπ (M : System l E d.Z) (B B' : System l E Y) :
      ((properProjection l E o d.g).app M).app B ▷ B' ≫
        ((properProjection l E o d.g).app (M ⊗ P.obj B)).app B' ≫
          G.map (α_ M (P.obj B) (P.obj B')).hom =
      (α_ (G.obj M) B B').hom ≫ ((properProjection l E o d.g).app M).app (B ⊗ B') ≫
        G.map (M ◁ (pullbackTensorSystemComparison l E d.g).hom.app (B, B')) :=
    system_proper_action l E o d.g M B B'
  have h := composite_projection_components_action G J P
    (F' := Q) (F'' := U)
    (fun M B ↦ ((properProjection l E o d.g).app M).app B)
    (fun M B ↦ (a.projection d.i).hom.app (M, B)) e
    (fun B B' ↦ (pullbackTensorSystemComparison l E d.g).hom.app (B, B'))
    (fun B B' ↦ (pullbackTensorSystemComparison l E d.i).hom.app (B, B'))
    (fun B B' ↦ (pullbackTensorSystemComparison l E f).hom.app (B, B'))
    (fun x B ↦ curried_action_natural_left _ _ (properProjection l E o d.g) x B)
    (fun M B B' ↦ action_of_assoc G P
      (fun B B' ↦ (pullbackTensorSystemComparison l E d.g).hom.app (B, B'))
      (fun M B ↦ ((properProjection l E o d.g).app M).app B) M B B' (hπ M B B'))
    (fun x B ↦ open_natural_left _ _ (a.projection d.i) x B)
    (fun M _ _ y ↦ open_natural_right _ _ (a.projection d.i) M y)
    (system_open_action l E o c a d.i) he K L N
  rw [system_compactification_component l E o c a d K L,
    system_compactification_component l E o c a d (K ⊗ (pull l E f).obj L) N,
    system_compactification_component l E o c a d K (L ⊗ N)]
  exact h.symm

private theorem system_compactification_natural_left
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (o : Operations l E) (c : Compositors l E o)
    (a : OpenComparisons l E o c) {X Y : Scheme.{u}} {f : X ⟶ Y}
    (d : Compactification f) {K K' : System l E X} (x : K ⟶ K')
    (L : System l E Y) :
    let := (calculus l E X).systemClosed.monoidal
    let := (calculus l E Y).systemClosed.monoidal
    let F := Operations.shriek l E o d.i ⋙ Operations.push l E o d.g
    F.map x ▷ L ≫ compactificationProjection l E o c a d K' L =
      compactificationProjection l E o c a d K L ≫ F.map (x ▷ (pull l E f).obj L) := by
  let := (calculus l E X).systemClosed.monoidal
  let := (calculus l E Y).systemClosed.monoidal
  have h := SystemProjectionFormula.projection_natural_aux l E o c a d x (𝟙 L)
  simpa only [SystemProjectionFormula.support, SystemProjectionFormula.projection,
    CoefficientClosedStructure.tensor, MonoidalCategory.tensor,
    (pull l E f).map_id L, tensorHom_id] using h

set_option maxHeartbeats 2000000 in
-- The derived functor and inverse compositor conversions need a larger kernel allowance.
private theorem system_compactification_natural_right
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (o : Operations l E) (c : Compositors l E o)
    (a : OpenComparisons l E o c) {X Y : Scheme.{u}} {f : X ⟶ Y}
    (d : Compactification f) (K : System l E X) {L L' : System l E Y} (y : L ⟶ L') :
    let := (calculus l E X).systemClosed.monoidal
    let := (calculus l E Y).systemClosed.monoidal
    let F := Operations.shriek l E o d.i ⋙ Operations.push l E o d.g
    F.obj K ◁ y ≫ compactificationProjection l E o c a d K L' =
      compactificationProjection l E o c a d K L ≫ F.map (K ◁ (pull l E f).map y) := by
  let := (calculus l E X).systemClosed.monoidal
  let := (calculus l E Y).systemClosed.monoidal
  have h := SystemProjectionFormula.projection_natural_aux l E o c a d (𝟙 K) y
  simpa only [SystemProjectionFormula.support, SystemProjectionFormula.projection,
    CoefficientClosedStructure.tensor, MonoidalCategory.tensor,
    (Operations.shriek l E o d.i ⋙ Operations.push l E o d.g).map_id K,
    id_tensorHom] using h

private theorem conjugated_hom
    {A : Type*} [Category A] {X Y X' Y' : A}
    (hX : X = X') (hY : Y' = Y) (e : X' ≅ Y') :
    HEq (eqToIso hX ≪≫ e ≪≫ eqToIso hY).hom e.hom := by
  subst X' Y'
  simp

private theorem normalized_tensor_canonical
    (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
    (E : Type u) [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E]
    (W : Scheme.{u}) [∀ x : W, Invertible (C.l : W.residueField x)]
    (K L : sfIntegralConstructibleCategory C.l E W) :
    (IntegralProjectionReduction.normalizedTensor D C E W
      (Functor.currying.inverse.obj (constructibleIntegralTensor C.l E W)) rfl
      ).hom.app (K, L) = (pullbackTensorIntegralReductionTensor C.l E W K L).hom := by
  dsimp only [IntegralProjectionReduction.normalizedTensor,
    FixProjectionCompactification.Coordinates.tensorReductionIso,
    pullbackTensorIntegralReductionTensor, Functor.currying, Iso.trans,
    eqToIso, Functor.isoWhiskerRight, Functor.isoWhiskerLeft,
    Functor.whiskerRight, Functor.whiskerLeft, NatIso.ofComponents,
    Functor.mapIso, Iso.refl, asIso, Functor.prod_obj, Functor.comp_obj,
    Functor.curry, Functor.curryObj, Functor.whiskeringLeft, Functor.whiskeringRight]
  simp only [NatTrans.comp_app, Iso.app_hom, eqToHom_refl,
    Category.id_comp, ObjectProperty.ι_obj,
    ((sfIntegralConstructible C.l E W).ι ⋙ (calculus C.l E W).reduction).map_id]
  exact Category.id_comp _

private theorem normalized_associator
    (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
    (E : Type u) [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E]
    (W : Scheme.{u}) [∀ x : W, Invertible (C.l : W.residueField x)]
    (T : sfIntegralConstructibleCategory C.l E W ⥤
      sfIntegralConstructibleCategory C.l E W ⥤ sfIntegralConstructibleCategory C.l E W)
    (hT : T = Functor.currying.inverse.obj (constructibleIntegralTensor C.l E W))
    (K L N : sfIntegralConstructibleCategory C.l E W) :
    let := (calculus C.l E W).systemClosed.monoidal
    let R := (sfIntegralConstructible C.l E W).ι ⋙ (calculus C.l E W).reduction
    let t := IntegralProjectionReduction.normalizedTensor D C E W T hT
    let a := sixFunctorProjectionTensorAssociator T _ hT
      (pullbackTensorIntegralAssociator C.l E W)
    R.map (a K L N).hom ≫ t.hom.app (K, (T.obj L).obj N) ≫
        R.obj K ◁ t.hom.app (L, N) =
      t.hom.app ((T.obj K).obj L, N) ≫ t.hom.app (K, L) ▷ R.obj N ≫
        (α_ (R.obj K) (R.obj L) (R.obj N)).hom := by
  subst T
  have h := (pullbackTensorIntegralAssociator_existsUnique C.l E W K L N).exists.choose_spec
  dsimp only
  simp only [sixFunctorProjectionTensorAssociator, eqToIso_refl,
    Iso.trans_hom, Iso.refl_hom, Iso.symm_hom, Iso.refl_inv,
    Category.id_comp, Category.comp_id, normalized_tensor_canonical]
  simpa only [CoefficientClosedStructure.tensor, MonoidalCategory.tensor,
    id_tensorHom, tensorHom_id, Functor.comp_map, ObjectProperty.ι_map,
    Functor.comp_obj, Functor.prod_obj, Functor.currying, Functor.curry_obj_obj_obj,
    ObjectProperty.ι_obj, pullbackTensorIntegralAssociator] using h

variable {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
  {E : Type u} [Field E] [Algebra (Padic C.l) E]
  [FiniteDimensional (Padic C.l) E] {n : ℕ} {hn : 1 ≤ n}


set_option maxHeartbeats 2000000 in
-- Naturality expands three whiskered comparison isomorphisms on derived categories.
attribute [-instance] WeilConjectures.IntegralHom.derivedCategory in
private theorem evaluated_support_natural
    (S : SixFunctorOperationDatum D C E n hn) (m : ℕ) (o : Operations C.l E)
    {X Y : SixFunctorSpace D} (f : X ⟶ Y) [IsSeparated f.hom.left]
    [LocallyOfFiniteType f.hom.left] [QuasiCompact f.hom.left]
    (c : Compactification f.hom.left)
    {K K' : sfIntegralConstructibleCategory C.l E X.obj.left} (v : K ⟶ K') :
    let RX := (sfIntegralConstructible C.l E X.obj.left).ι ⋙
      (calculus C.l E X.obj.left).reduction
    let G := Operations.shriek C.l E o c.i ⋙ Operations.push C.l E o c.g
    let ev : coefficientSequenceDerived C.l E Y.obj.left ⥤
        normalizedDVRDerived C.l E Y.obj.left m :=
      evaluation (C := C) (E := E) m Y
    let I : ObjectProperty.FullSubcategory.{u + 2, u + 2}
          (intrinsicFiniteTorsionConstructible C.l E (m + 1)
            (Nat.le_add_left 1 m) Y.obj.left) ⥤
        proEtaleDerivedCategory Y.obj.left
          (Padic.coefficientExtensionRing C.l E (m + 1)) :=
      finiteInclusion (C := C) (E := E) m Y
    ev.map (G.map (RX.map v)) ≫ (evaluatedSupport S m o f c K').hom =
      (evaluatedSupport S m o f c K).hom ≫
        I.map ((SixFunctorPushStage.support.{u, u + 2, u + 2}
          (stage S m).finite f c).map ((reduction S m X).map v)) := by
  let RX := (sfIntegralConstructible C.l E X.obj.left).ι ⋙
    (calculus C.l E X.obj.left).reduction
  let G := Operations.shriek C.l E o c.i ⋙ Operations.push C.l E o c.g
  let ev := evaluation (C := C) (E := E) m Y
  let I := finiteInclusion (C := C) (E := E) m Y
  let H : sixFunctorFiniteCategory D C E (m + 1) (Nat.le_add_left 1 m) X ⥤
      sixFunctorFiniteCategory D C E (m + 1) (Nat.le_add_left 1 m) Y :=
    SixFunctorPushStage.support.{u, u + 2, u + 2} (stage S m).finite f c
  let q : RX ⋙ G ⋙ ev ≅ reduction S m X ⋙ H ⋙ I :=
    Functor.isoWhiskerLeft RX (supportEvaluation C.l E o c m) ≪≫
    Functor.isoWhiskerRight (reductionSystemEvaluation S m X)
      (sixFunctorFiniteSupport D C E (m + 1) (Nat.le_add_left 1 m) f c) ≪≫
    Functor.isoWhiskerLeft (reduction S m X) ((stage S m).finiteSupport f c).symm
  have h := q.hom.naturality v
  dsimp only [q, reductionSystemEvaluation, evaluatedSupport, reductionEvaluation,
    Functor.isoWhiskerLeft, Functor.isoWhiskerRight,
    Functor.whiskerLeft, Functor.whiskerRight, NatIso.ofComponents,
    Iso.trans, Functor.mapIso, Functor.comp_map, Functor.comp_obj,
    Functor.whiskeringLeft, Functor.whiskeringRight] at h ⊢
  simpa only [RX, G, H, ev, I, evaluatedSupport, reductionEvaluation,
    Iso.trans_hom, Functor.mapIso_hom,
    IntegralProjectionReduction.evaluation, finiteInclusion,
    Functor.comp_map, Functor.comp_obj, ObjectProperty.ι_map, ObjectProperty.ι_obj,
    Iso.app_hom, NatTrans.comp_app, Category.assoc] using h

attribute [-instance] WeilConjectures.IntegralHom.derivedCategory in
private theorem support_reduction_natural
    (S : SixFunctorOperationDatum D C E n hn) (hl : IsUnit (C.l : D.k))
    (o : Operations C.l E) (z : Realizations C.l E D o)
    {X Y : SixFunctorSpace D} (f : X ⟶ Y) [IsSeparated f.hom.left]
    [LocallyOfFiniteType f.hom.left] [QuasiCompact f.hom.left]
    (c : Compactification f.hom.left)
    {K K' : sfIntegralConstructibleCategory C.l E X.obj.left} (v : K ⟶ K') :
    let RX := (sfIntegralConstructible C.l E X.obj.left).ι ⋙
      (calculus C.l E X.obj.left).reduction
    let RY := (sfIntegralConstructible C.l E Y.obj.left).ι ⋙
      (calculus C.l E Y.obj.left).reduction
    RY.map ((S.higher.integral.support f c).map v) ≫
        FixProjectionCompactification.Coordinates.supportReduction D C E S.higher hl o z f c K' =
      FixProjectionCompactification.Coordinates.supportReduction D C E S.higher hl o z f c K ≫
        (Operations.shriek C.l E o c.i ⋙ Operations.push C.l E o c.g).map (RX.map v) := by
  let F := S.higher.integral.support f c
  let R := (calculus C.l E Y.obj.left).reduction
  let RX := (sfIntegralConstructible C.l E X.obj.left).ι ⋙
    (calculus C.l E X.obj.left).reduction
  let G := Operations.shriek C.l E o c.i ⋙ Operations.push C.l E o c.g
  let q (M : sfIntegralConstructibleCategory C.l E X.obj.left) :=
    FixProjectionCompactification.Coordinates.supportReduction D C E S.higher hl o z f c M
  let V := FixProjectionCompactification.Coordinates.supportValue D C E S.higher hl o z f c K'
  let s := q K ≫ G.map (RX.map v)
  let a : F.obj K ⟶ F.obj K' := ObjectProperty.homMk
    (((calculus C.l E Y.obj.left).adjunction.homEquiv _ _) s ≫ V.hom)
  have ha : R.map a.hom ≫ q K' = s :=
    FixProjectionCompactification.adjunct_factor
      (calculus C.l E Y.obj.left).adjunction V s
  have hav : a = F.map v := by
    apply integral_reductions_jointly_faithful S Y
    intro m
    let ev : coefficientSequenceDerived C.l E Y.obj.left ⥤
        normalizedDVRDerived C.l E Y.obj.left m :=
      evaluation (C := C) (E := E) m Y
    let I : ObjectProperty.FullSubcategory.{u + 2, u + 2}
          (intrinsicFiniteTorsionConstructible C.l E (m + 1)
            (Nat.le_add_left 1 m) Y.obj.left) ⥤
        proEtaleDerivedCategory Y.obj.left
          (Padic.coefficientExtensionRing C.l E (m + 1)) :=
      finiteInclusion (C := C) (E := E) m Y
    let red := coefficientFiniteDerivedExtension C.l E Y.obj.left m
    let rho := (calculus C.l E Y.obj.left).reductionEvaluation m
    let H : sixFunctorFiniteCategory D C E (m + 1) (Nat.le_add_left 1 m) X ⥤
        sixFunctorFiniteCategory D C E (m + 1) (Nat.le_add_left 1 m) Y :=
      SixFunctorPushStage.support.{u, u + 2, u + 2} (stage S m).finite f c
    let beta : F ⋙ reduction S m Y ≅ reduction S m X ⋙ H :=
      (SixFunctorCoefficientComparison.supportAdjunction.{u, u + 2, u + 2, u + 2, u + 2}
        (S.integralNormalization.reduction m) f c).left
    apply I.map_injective
    change red.map a.hom = red.map (F.map v).hom
    apply FixProjectionCompactification.finite_reflection R ev red rho s (q K')
      a.hom (F.map v).hom (evaluatedSupport S m o f c K')
      (I.mapIso (beta.app K')) ha
    · exact integralProjectionSupportEvaluation S m hl o z f c K'
    · dsimp only [s]
      simp only [ev.map_comp, Category.assoc]
      rw [evaluated_support_natural S m o f c v]
      rw [← Category.assoc, integralProjectionSupportEvaluation S m hl o z f c K]
      simp only [Category.assoc]
      have hb := congrArg (fun w ↦ I.map w) (beta.hom.naturality v)
      simpa only [I, beta, H, rho, red, F, reductionEvaluation, stage,
        IntegralProjectionReduction.reduction, sixFunctorIntegralReduction,
        ObjectProperty.ι_map, ObjectProperty.FullSubcategory.comp_hom,
        ObjectProperty.lift_map, ObjectProperty.homMk_hom, coefficientFiniteDerivedExtension,
        Functor.map_comp, Functor.comp_map, Iso.app_hom,
        Functor.mapIso_hom, Category.assoc] using congrArg
          (fun w ↦ rho.hom.app ((F.obj K).obj) ≫ w) hb.symm
  change R.map (F.map v).hom ≫ q K' = s
  rw [← hav]
  exact ha

/-- The equality obtained after applying one finite reduction to both paths of
an integral projection action. This is the finite evaluation step before joint
faithfulness of the reductions is applied. -/
def projectionIntegralReductionStageEquation
    (S : SixFunctorDatum D C E n hn)
    {X Y : SixFunctorSpace D} (f : X ⟶ Y) [IsSeparated f.hom.left]
    (c : Compactification f.hom.left)
    (K : sfIntegralConstructibleCategory C.l E X.obj.left)
    (L N : sfIntegralConstructibleCategory C.l E Y.obj.left) (m : ℕ) : Prop :=
  letI : ∀ x : X.obj.left, Invertible (C.l : X.obj.left.residueField x) :=
    fun x ↦ (map_natCast (X.obj.hom.residueFieldAlgebraMap x) C.l) ▸
      ((PurCompactSupport.coefficientPrimeUnit C.l D C.different).map
        (X.obj.hom.residueFieldAlgebraMap x)).invertible
  letI : ∀ y : Y.obj.left, Invertible (C.l : Y.obj.left.residueField y) :=
    fun y ↦ (map_natCast (Y.obj.hom.residueFieldAlgebraMap y) C.l) ▸
      ((PurCompactSupport.coefficientPrimeUnit C.l D C.different).map
        (Y.obj.hom.residueFieldAlgebraMap y)).invertible
  let TX := S.higher.integralTensor X
  let TY := S.higher.integralTensor Y
  let F := S.higher.integral.support f c
  let U := S.higher.integral.pull f
  let aX :=
    sixFunctorProjectionTensorAssociator TX _
      (S.higher.integralTensorNormalization X)
      (pullbackTensorIntegralAssociator C.l E X.obj.left)
  let aY :=
    sixFunctorProjectionTensorAssociator TY _
      (S.higher.integralTensorNormalization Y)
      (pullbackTensorIntegralAssociator C.l E Y.obj.left)
  let R := IntegralProjectionReduction.reduction S.toSixFunctorOperationDatum m Y
  R.map ((TY.flip.obj N).map
      (compactSupportProjectionComponent S.higher.integralExchange f c K L) ≫
      compactSupportProjectionComponent S.higher.integralExchange f c
        ((TX.obj K).obj (U.obj L)) N) =
    R.map ((aY (F.obj K) L N).hom ≫
      compactSupportProjectionComponent S.higher.integralExchange f c K ((TY.obj L).obj N) ≫
      F.map ((TX.obj K).map (sixFunctorProjectionIntegralMu S f L N).hom) ≫
      F.map (aX K (U.obj L) (U.obj N)).inv)

/-- Finite-stage action follows from the proper/open action on coherent systems,
transported through the prescribed integral reduction comparisons.
Source: current blueprint prop-sf-pf-coherence, final finite-reduction clause
(blueprint: lem-sf-projection-reduction-integral-stage-action).
Proof: combine the proper counit action and open unit action using the coherent
pullback compositor. Naturality of the specified support reduction follows from
its finite evaluations and joint faithfulness. Transport the system action through
this support comparison, the canonical tensor comparison and the pullback comparison;
their defining equations identify the associators and pullback tensor map. Faithful
coherent reduction gives the integral equality, and the requested finite reduction
preserves it. Integral residue Tor supplies the normalization hypotheses for arbitrary
integral constructible L and N. -/
theorem projectionIntegralReduction_stage_of_coordinates
    (S : SixFunctorDatum D C E n hn)
    {X Y : SixFunctorSpace D} (f : X ⟶ Y) [IsSeparated f.hom.left]
    (c : Compactification f.hom.left)
    (K : sfIntegralConstructibleCategory C.l E X.obj.left)
    (L N : sfIntegralConstructibleCategory C.l E Y.obj.left) (m : ℕ)
    (hcoord : projectionIntegralReductionCoordinates S.toSixFunctorOperationDatum) :
    projectionIntegralReductionStageEquation S f c K L N m := by
  /- Use the canonical coherent reduction coordinates. Their defining equations give
  the associator coherence needed to transport the proper/open tensor action. First
  reconstruct naturality of the actual support comparison from all finite evaluations;
  then cancel the common target comparison and use faithful coherent reduction. -/
  have _ := hcoord
  clear hcoord
  have hgeo : LocallyOfFiniteType f.hom.left ∧ QuasiCompact f.hom.left := by
    let : IsOpenImmersion c.i := c.isOpenImmersion
    let : IsProper c.g := c.isProper
    have hf : LocallyOfFiniteType f.hom.left := by
      rw [c.comm]
      exact locallyOfFiniteType_comp c.i c.g
    let : LocallyOfFiniteType X.obj.hom := X.property.1
    let : QuasiCompact X.obj.hom := X.property.2
    let : IsNoetherian X.obj.left := isNoetherian_of_locallyOfFiniteType X.obj.hom
    exact ⟨hf, quasiCompact_of_noetherianSpace_source _⟩
  let : LocallyOfFiniteType f.hom.left := hgeo.1
  let : QuasiCompact f.hom.left := hgeo.2
  let hl := PurCompactSupport.coefficientPrimeUnit C.l D C.different
  let : ∀ x : X.obj.left, Invertible (C.l : X.obj.left.residueField x) :=
    fun x ↦ (map_natCast (X.obj.hom.residueFieldAlgebraMap x) C.l) ▸
      ((PurCompactSupport.coefficientPrimeUnit C.l D C.different).map
        (X.obj.hom.residueFieldAlgebraMap x)).invertible
  let : ∀ y : Y.obj.left, Invertible (C.l : Y.obj.left.residueField y) :=
    fun y ↦ (map_natCast (Y.obj.hom.residueFieldAlgebraMap y) C.l) ▸
      ((PurCompactSupport.coefficientPrimeUnit C.l D C.different).map
        (Y.obj.hom.residueFieldAlgebraMap y)).invertible
  obtain ⟨o, ⟨z⟩⟩ := integralCompactificationSystemRealization C.l E D C.different
  let := (calculus C.l E X.obj.left).systemClosed.monoidal
  let := (calculus C.l E Y.obj.left).systemClosed.monoidal
  let TX := S.higher.integralTensor X
  let TY := S.higher.integralTensor Y
  let F := S.higher.integral.support f c
  let U := S.higher.integral.pull f
  let RX := (sfIntegralConstructible C.l E X.obj.left).ι ⋙
    (calculus C.l E X.obj.left).reduction
  let RY := (sfIntegralConstructible C.l E Y.obj.left).ι ⋙
    (calculus C.l E Y.obj.left).reduction
  let F' := Operations.shriek C.l E o c.i ⋙ Operations.push C.l E o c.g
  let U' := pull C.l E f.hom.left
  let tX := FixProjectionCompactification.Coordinates.datumTensorReductionIso
    D C E S.higher hl X
  let tY := FixProjectionCompactification.Coordinates.datumTensorReductionIso
    D C E S.higher hl Y
  let u := ProperCoordinates.pullComparison S.higher hl o z f
  let b := action_input TX RX RY U U' tX u
  let hq (M : sfIntegralConstructibleCategory C.l E X.obj.left) :=
    (FixProjectionCompactification.integralSupportReductionNormalization
      D C E n hn S.toSixFunctorOperationDatum hl o z f).1 c M
  let q : F ⋙ RY ≅ RX ⋙ F' := NatIso.ofComponents
    (fun M ↦ asIso (FixProjectionCompactification.Coordinates.supportReduction
      D C E S.higher hl o z f c M))
    (fun v ↦ support_reduction_natural S.toSixFunctorOperationDatum hl o z f c v)
  let aX := sixFunctorProjectionTensorAssociator TX _
    (S.higher.integralTensorNormalization X)
    (pullbackTensorIntegralAssociator C.l E X.obj.left)
  let aY := sixFunctorProjectionTensorAssociator TY _
    (S.higher.integralTensorNormalization Y)
    (pullbackTensorIntegralAssociator C.l E Y.obj.left)
  let μ := fun M N ↦ (sixFunctorProjectionIntegralMu S f M N).hom
  let μ' := fun M N ↦ (pullbackTensorSystemComparison C.l E f.hom.left).hom.app (M, N)
  let π := compactSupportProjectionComponent S.higher.integralExchange f c
  let π' := compactificationProjection C.l E o z.compositors z.openComparisons c
  have hπ (M : sfIntegralConstructibleCategory C.l E X.obj.left)
      (P : sfIntegralConstructibleCategory C.l E Y.obj.left) :
      RY.map (π M P) ≫ q.hom.app ((TX.obj M).obj (U.obj P)) ≫ F'.map (b M P).hom =
        tY.hom.app (F.obj M, P) ≫ q.hom.app M ▷ RY.obj P ≫ π' (RX.obj M) (RY.obj P) := by
    have hP : finiteTorConstructibleIntegral C.l E Y.obj.left P.obj := by
      rw [← (integral_residue_tor D C.l C.different E Y.obj.left).2]
      exact P.property
    have h := FixProjectionCompactification.integralProjectionReductionNormalization
      D C E n hn S.toSixFunctorOperationDatum hl o z f c M P hP
    change FixProjectionCompactification.Coordinates.sourceMap
        D C E S.higher hl o z f c M P ≫ π' (RX.obj M) (RY.obj P) =
      RY.map (π M P) ≫ FixProjectionCompactification.Coordinates.targetMap
        D C E S.higher hl o z f c M P at h
    dsimp only [q, NatIso.ofComponents, asIso]
    simpa only [RX, RY, TX, TY, F, U, F', U', tX, tY, u, b, q, π, π',
      action_input, FixProjectionCompactification.Coordinates.sourceMap,
      FixProjectionCompactification.Coordinates.targetMap,
      FixProjectionCompactification.Coordinates.inputReduction,
      ProperCoordinates.pullComparison_hom_app,
      Iso.trans_hom, Iso.trans_inv, Iso.symm_inv, Iso.symm_hom,
      Functor.mapIso_inv, Functor.mapIso_hom, Iso.prod_inv, Iso.prod_hom,
      Iso.refl_hom, Iso.refl_inv, Iso.app_hom, Iso.app_inv,
      NatIso.ofComponents_hom_app, asIso_hom,
      MonoidalCategory.tensorHom_def, tensorIso_hom,
      id_whiskerRight, Category.id_comp, Functor.map_comp, Category.assoc,
      compactSupportProjectionComponent, Functor.comp_map, ObjectProperty.ι_map,
      Functor.comp_obj, Functor.prod_obj, CoefficientClosedStructure.tensor,
      MonoidalCategory.tensor, whiskerLeft_id, Category.comp_id,
      ObjectProperty.ι_obj, Functor.uncurry_obj_obj] using h.symm
  have haX := normalized_associator D C E X.obj.left TX
    (S.higher.integralTensorNormalization X)
  have haY := normalized_associator D C E Y.obj.left TY
    (S.higher.integralTensorNormalization Y)
  have hμ (M P : sfIntegralConstructibleCategory C.l E Y.obj.left) :
      RX.map (μ M P) ≫ tX.hom.app (U.obj M, U.obj P) ≫
        (u.hom.app M ⊗ₘ u.hom.app P) =
      u.hom.app ((TY.obj M).obj P) ≫ U'.map (tY.hom.app (M, P)) ≫
        μ' (RY.obj M) (RY.obj P) := by
    have hv : HEq (μ M P) (canonicalIntegralPullbackTensor C.l E f.hom.left M P).hom := by
      dsimp only [μ, sixFunctorProjectionIntegralMu]
      exact conjugated_hom _ _ _
    exact normalized_reduction D C E o z f.hom.left U TX TY
      (S.higher.integralPullback f) (S.higher.integralTensorNormalization X)
      (S.higher.integralTensorNormalization Y) M P (μ M P) hv
  have h := transport_action TX TY RX RY F U F' U' tY q b aX aY μ μ' π π' hπ
    (system_compactification_natural_left C.l E o z.compositors z.openComparisons c)
    (system_compactification_natural_right C.l E o z.compositors z.openComparisons c)
    haY
    (action_input_assoc TX TY RX RY U U' tX tY u aX μ μ' haX hμ)
    (system_compactification_action C.l E o z.compositors z.openComparisons c) K L N
  have hRY : RY.Faithful := by
    exact (coherentReduction_fullyFaithful C.l E Y.obj.left).2
  have hi := RY.map_injective h
  exact congrArg (fun v ↦ (reduction S.toSixFunctorOperationDatum m Y).map v) hi

end WeilConjectures
