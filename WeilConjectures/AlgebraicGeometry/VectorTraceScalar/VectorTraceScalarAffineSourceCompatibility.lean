/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.VectorTraceScalar.VectorTraceScalarAffineTowerData
public import WeilConjectures.AlgebraicGeometry.Etale.Scalar.EtaleScalarPullbackIdentityNormalization
public import WeilConjectures.AlgebraicGeometry.Etale.Scalar.EtaleScalarPullbackTensorCoherence
public import WeilConjectures.AlgebraicGeometry.Scalar.ScalarPullbackComposition
public import WeilConjectures.AlgebraicGeometry.VectorTraceScalar.FiniteTateScalarPullbackSquare
public import WeilConjectures.SixFunctors.Etale.Derived.SupportsBaseChange

/-! # Scalar compatibility of ordered affine coefficient descent

Source: blueprint/latest, sec-smooth-purity/sk-prop-an,
cor-pur-vector-bundle-purity.proof.md, paragraph 2, Tate coefficient comparisons.
(blueprint: lem-pur-vector-scalar-affine-source-compatibility).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open WeilConjectures.PurityFiniteSetting
namespace AlgebraicGeometry.Etale.VectorTraceScalar

attribute [local irreducible] Functor.leftAdjoint Functor.rightAdjoint
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor Functor.mapDerivedCategory
  derivedTensor upperStar lowerStar

variable {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]

private def tensorMap (φ : A →+* B) (T : Scheme.{u})
    {K L : DerivedCategoryModule A T} {K' L' : DerivedCategoryModule B T}
    (b : (scalarExtension φ T).obj K ⟶ K')
    (l : (scalarExtension φ T).obj L ⟶ L') :
    (scalarExtension φ T).obj (K ⊗ L) ⟶ K' ⊗ L' :=
  (ExceptionalCoefficients.tensorIso φ T).hom.app (K, L) ≫ (b ⊗ₘ l)

private def pullMap (φ : A →+* B) {X Y : Scheme.{u}} (f : X ⟶ Y)
    {K : DerivedCategoryModule A Y} {K' : DerivedCategoryModule B Y}
    (b : (scalarExtension φ Y).obj K ⟶ K') :
    (scalarExtension φ X).obj ((ordinaryFinitePullback A f).obj K) ⟶
      (ordinaryFinitePullback B f).obj K' :=
  (scalarPullbackIso φ f).inv.app K ≫ (ordinaryFinitePullback B f).map b

@[reassoc]
private theorem tensorMap_post (φ : A →+* B) (T : Scheme.{u})
    {K L : DerivedCategoryModule A T} {K' L' M' P' : DerivedCategoryModule B T}
    (b : (scalarExtension φ T).obj K ⟶ K')
    (l : (scalarExtension φ T).obj L ⟶ L') (e : K' ⟶ M') (v : L' ⟶ P') :
    tensorMap φ T b l ≫ (e ⊗ₘ v) = tensorMap φ T (b ≫ e) (l ≫ v) := by
  simp only [tensorMap, Category.assoc, tensorHom_comp_tensorHom]

@[reassoc]
private theorem pullMap_post (φ : A →+* B) {X Y : Scheme.{u}} (f : X ⟶ Y)
    {K : DerivedCategoryModule A Y} {K' M' : DerivedCategoryModule B Y}
    (b : (scalarExtension φ Y).obj K ⟶ K') (e : K' ⟶ M') :
    pullMap φ f b ≫ (ordinaryFinitePullback B f).map e = pullMap φ f (b ≫ e) := by
  simp only [pullMap, Functor.map_comp, Category.assoc]

@[reassoc]
private theorem tensor_pull (φ : A →+* B) {X Y : Scheme.{u}} (f : X ⟶ Y)
    {K L : DerivedCategoryModule A Y} {K' L' : DerivedCategoryModule B Y}
    (b : (scalarExtension φ Y).obj K ⟶ K')
    (l : (scalarExtension φ Y).obj L ⟶ L') :
    (scalarExtension φ X).map (ordinaryFiniteTensorPullback A f K L).hom ≫
        tensorMap φ X (pullMap φ f b) (pullMap φ f l) =
      pullMap φ f (tensorMap φ Y b l) ≫ (ordinaryFiniteTensorPullback B f K' L').hom := by
  have ht := etaleScalarPullback_tensor φ f K L
  change (scalarPullbackIso φ f).hom.app (K ⊗ L) ≫
      (scalarExtension φ X).map (ordinaryFiniteTensorPullback A f K L).hom ≫
      (ExceptionalCoefficients.tensorIso φ X).hom.app
        ((ordinaryFinitePullback A f).obj K, (ordinaryFinitePullback A f).obj L) =
    (ordinaryFinitePullback B f).map
        ((ExceptionalCoefficients.tensorIso φ Y).hom.app (K, L)) ≫
      (ordinaryFiniteTensorPullback B f _ _).hom ≫
        ((scalarPullbackIso φ f).hom.app K ⊗ₘ (scalarPullbackIso φ f).hom.app L) at ht
  apply (cancel_epi ((scalarPullbackIso φ f).hom.app (K ⊗ L))).1
  simp only [tensorMap, pullMap, Category.assoc, Iso.hom_inv_id_app_assoc,
    Functor.map_comp, ← tensorHom_comp_tensorHom]
  rw [reassoc_of% ht]
  simp only [tensorHom_comp_tensorHom_assoc, Iso.hom_inv_id_app]
  have hn := leftDerivedUpperStarTensorIso_hom_naturality
    (ModuleCat.{u + 1} B) f b l
  change (ordinaryFinitePullback B f).map (b ⊗ₘ l) ≫
      (ordinaryFiniteTensorPullback B f K' L').hom =
    (ordinaryFiniteTensorPullback B f _ _).hom ≫
      ((ordinaryFinitePullback B f).map b ⊗ₘ (ordinaryFinitePullback B f).map l) at hn
  rw [hn]
  erw [MonoidalCategory.id_tensorHom_id, Category.id_comp]
  rfl

@[reassoc]
private theorem tensor_pull_inv (φ : A →+* B) {X Y : Scheme.{u}} (f : X ⟶ Y)
    {K L : DerivedCategoryModule A Y} {K' L' : DerivedCategoryModule B Y}
    (b : (scalarExtension φ Y).obj K ⟶ K')
    (l : (scalarExtension φ Y).obj L ⟶ L') :
    (scalarExtension φ X).map (ordinaryFiniteTensorPullback A f K L).inv ≫
        pullMap φ f (tensorMap φ Y b l) =
      tensorMap φ X (pullMap φ f b) (pullMap φ f l) ≫
        (ordinaryFiniteTensorPullback B f K' L').inv := by
  apply (cancel_epi ((scalarExtension φ X).map
    (ordinaryFiniteTensorPullback A f K L).hom)).1
  simp only [← Functor.map_comp_assoc, Iso.hom_inv_id,
    CategoryTheory.Functor.map_id, Category.id_comp]
  rw [← Category.assoc, tensor_pull]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]

private theorem reverse_composite {C : Type*} [Category C]
    {V W X Y Z : C} (a : V ≅ W) (b : W ≅ X) (c : X ≅ Y)
    (d : V ≅ Z) (e : Z ≅ Y)
    (h : a.hom ≫ b.hom ≫ c.hom = d.hom ≫ e.hom) :
    e.inv ≫ d.inv = c.inv ≫ b.inv ≫ a.inv := by
  have hi := congrArg (fun z ↦ e.inv ≫ d.inv ≫ z ≫ c.inv ≫ b.inv ≫ a.inv) h
  simpa only [Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id_assoc,
    Iso.hom_inv_id, Category.comp_id] using hi

private theorem transport_pullback_composition
    {C₀ C₁ C₂ D₀ D₁ D₂ : Type*}
    [Category C₀] [Category C₁] [Category C₂]
    [Category D₀] [Category D₁] [Category D₂]
    (S₀ : C₀ ⥤ D₀) (S₁ : C₁ ⥤ D₁) (S₂ : C₂ ⥤ D₂)
    {F F' : C₀ ⥤ C₁} {G G' : C₁ ⥤ C₂} {H H' : C₀ ⥤ C₂}
    {P P' : D₀ ⥤ D₁} {Q Q' : D₁ ⥤ D₂} {R R' : D₀ ⥤ D₂}
    (eF : F ≅ F') (eG : G ≅ G') (eH : H ≅ H')
    (eP : P ≅ P') (eQ : Q ≅ Q') (eR : R ≅ R')
    (a : S₀ ⋙ P ≅ F ⋙ S₁) (b : S₁ ⋙ Q ≅ G ⋙ S₂)
    (t : S₀ ⋙ R ≅ H ⋙ S₂) (c : H' ≅ F' ⋙ G') (d : R' ≅ P' ⋙ Q')
    (X : C₀)
    (h : d.hom.app (S₀.obj X) ≫
        Q'.map (eP.inv.app (S₀.obj X) ≫ a.hom.app X ≫ S₁.map (eF.hom.app X)) ≫
        eQ.inv.app (S₁.obj (F'.obj X)) ≫ b.hom.app (F'.obj X) ≫
        S₂.map (eG.hom.app (F'.obj X)) =
      eR.inv.app (S₀.obj X) ≫ t.hom.app X ≫ S₂.map (eH.hom.app X) ≫
        S₂.map (c.hom.app X)) :
    (eR.hom.app (S₀.obj X) ≫ d.hom.app (S₀.obj X) ≫
        Q'.map (eP.inv.app (S₀.obj X)) ≫ eQ.inv.app (P.obj (S₀.obj X))) ≫
        Q.map (a.hom.app X) ≫ b.hom.app (F.obj X) =
      t.hom.app X ≫ S₂.map (eH.hom.app X ≫ c.hom.app X ≫
        G'.map (eF.inv.app X) ≫ eG.inv.app (F.obj X)) := by
  have hh := congrArg (fun z ↦ eR.hom.app (S₀.obj X) ≫ z ≫
    S₂.map (G'.map (eF.inv.app X) ≫ eG.inv.app (F.obj X))) h
  simp only [Functor.map_comp, Category.assoc, Iso.hom_inv_id_app_assoc] at hh
  have hnG := eG.hom.naturality (eF.inv.app X)
  have hnb := b.hom.naturality (eF.inv.app X)
  have hnQ := eQ.inv.naturality (S₁.map (eF.inv.app X))
  have hnQa := eQ.inv.naturality (a.hom.app X)
  simp only [Functor.comp_obj, Functor.comp_map] at hnb
  have hnG' : eG.hom.app (F'.obj X) ≫ G'.map (eF.inv.app X) ≫
      eG.inv.app (F.obj X) = G.map (eF.inv.app X) := by
    rw [← reassoc_of% hnG, Iso.hom_inv_id_app, Category.comp_id]
  have hmG := congrArg S₂.map hnG'
  simp only [Functor.map_comp] at hmG
  rw [hmG] at hh
  rw [← hnb, ← reassoc_of% hnQ] at hh
  have hmF : Q'.map (S₁.map (eF.hom.app X)) ≫
      Q'.map (S₁.map (eF.inv.app X)) = 𝟙 _ := by
    rw [← Q'.map_comp, ← S₁.map_comp, Iso.hom_inv_id_app, S₁.map_id, Q'.map_id]
  rw [reassoc_of% hmF, reassoc_of% hnQa] at hh
  simpa only [Functor.map_comp, Category.assoc] using hh

private theorem scalar_derived_composition
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {X T₁ T₂ : Scheme.{u}}
    (v : T₁ ⟶ T₂) (j₁ : X ⟶ T₁) (j₂ : X ⟶ T₂) (h : j₁ ≫ v = j₂)
    (N : DerivedCategoryModule A T₂) :
    (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} B) j₁ v j₂ h.symm).hom.app
        ((Etale.scalarExtension φ T₂).obj N) ≫
      (ordinaryFinitePullback B j₁).map ((Etale.scalarPullbackIso φ v).hom.app N) ≫
      (Etale.scalarPullbackIso φ j₁).hom.app ((ordinaryFinitePullback A v).obj N) =
    (Etale.scalarPullbackIso φ j₂).hom.app N ≫
      (Etale.scalarExtension φ X).map
        ((Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} A) j₁ v j₂ h.symm).hom.app N) := by
  let eA := fun {V W : Scheme.{u}} (p : V ⟶ W) ↦
    leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) p
  let eB := fun {V W : Scheme.{u}} (p : V ⟶ W) ↦
    leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} B) p
  let cA := Functor.mapDerivedCategoryNatIso
      (upperStarComp (ModuleCat.{u + 1} A) j₁ v j₂ h.symm) ≪≫
    Functor.mapDerivedCategoryCompIso _ _
  let cB := Functor.mapDerivedCategoryNatIso
      (upperStarComp (ModuleCat.{u + 1} B) j₁ v j₂ h.symm) ≪≫
    Functor.mapDerivedCategoryCompIso _ _
  have q := scalarPullback_composition φ v j₁ j₂ h N
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Category.assoc] at q
  have ht := transport_pullback_composition (scalarExtension φ T₂) (scalarExtension φ T₁)
    (scalarExtension φ X) (eA v) (eA j₁) (eA j₂) (eB v) (eB j₁) (eB j₂)
    (scalarPullbackIso φ v) (scalarPullbackIso φ j₁) (scalarPullbackIso φ j₂)
    cA cB N (by
      simpa only [eA, eB, cA, cB, Iso.trans_hom, NatTrans.comp_app,
        Functor.map_comp, Category.assoc] using q)
  simpa only [ordinaryFinitePullback, leftDerivedUpperStarComp, Functor.leftDerivedFunctorNatIso,
    Functor.leftDerivedFunctorCompIso, leftDerivedUpperStarIsoMapDerivedCategory,
    eA, eB, cA, cB, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Category.assoc,
    Iso.inv_hom_id_app_assoc] using ht

@[reassoc]
private theorem pull_comp (φ : A →+* B) {X Y Z : Scheme.{u}}
    (g : Y ⟶ Z) (f : X ⟶ Y) (k : X ⟶ Z) (hk : f ≫ g = k)
    {K : DerivedCategoryModule A Z} {K' : DerivedCategoryModule B Z}
    (b : (scalarExtension φ Z).obj K ⟶ K') :
    (scalarExtension φ X).map
        ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) f g k hk.symm).inv.app K) ≫
      pullMap φ k b =
    pullMap φ f (pullMap φ g b) ≫
      (leftDerivedUpperStarComp (ModuleCat.{u + 1} B) f g k hk.symm).inv.app K' := by
  have hc := scalar_derived_composition
    φ g f k hk K
  have hi := reverse_composite
    ((leftDerivedUpperStarComp (ModuleCat.{u + 1} B) f g k hk.symm).app
      ((scalarExtension φ Z).obj K))
    ((ordinaryFinitePullback B f).mapIso ((scalarPullbackIso φ g).app K))
    ((scalarPullbackIso φ f).app ((ordinaryFinitePullback A g).obj K))
    ((scalarPullbackIso φ k).app K)
    ((scalarExtension φ X).mapIso
      ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) f g k hk.symm).app K)) hc
  change (scalarExtension φ X).map
      ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) f g k hk.symm).inv.app K) ≫
    (scalarPullbackIso φ k).inv.app K =
      (scalarPullbackIso φ f).inv.app ((ordinaryFinitePullback A g).obj K) ≫
        (ordinaryFinitePullback B f).map ((scalarPullbackIso φ g).inv.app K) ≫
          (leftDerivedUpperStarComp (ModuleCat.{u + 1} B) f g k hk.symm).inv.app
            ((scalarExtension φ Z).obj K) at hi
  have hn := (leftDerivedUpperStarComp (ModuleCat.{u + 1} B) f g k hk.symm).inv.naturality b
  simp only [Functor.comp_map] at hn
  simp only [pullMap, Functor.map_comp, ← Category.assoc]
  rw [hi]
  simp only [Category.assoc]
  erw [← hn]
  rfl

@[reassoc]
private theorem line_pull (φ : A →+* B) (N : ℕ) (hN : 0 < N)
    (hA : (N : A) = 0) (hB : (N : B) = 0)
    (tA : OrdinaryFiniteTwistTransport A N hA)
    (tB : OrdinaryFiniteTwistTransport B N hB)
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hX : IsUnit (N : Γ(X, ⊤))) (hY : IsUnit (N : Γ(Y, ⊤))) :
    (scalarExtension φ X).map (ordinaryFiniteShiftedLinePullback A N hA tA f hY).inv ≫
        pullMap φ f (line φ N hN hA hB Y hY) =
      line φ N hN hA hB X hX ≫
        (ordinaryFiniteShiftedLinePullback B N hB tB f hY).inv := by
  apply (cancel_epi ((scalarExtension φ X).map
    (ordinaryFiniteShiftedLinePullback A N hA tA f hY).hom)).1
  simp only [← Functor.map_comp_assoc, Iso.hom_inv_id,
    CategoryTheory.Functor.map_id, Category.id_comp]
  rw [← Category.assoc,
    finite_tate_scalar_pullback_square φ N hN hA hB tA tB f hX hY]
  simp only [pullMap, Category.assoc, Iso.hom_inv_id, Category.comp_id]

private theorem tensor_iso_hom (R : Type (u + 1)) [CommRing R] (T : Scheme.{u})
    {K K' L L' : DerivedCategoryModule R T} (e : K ≅ K') (v : L ≅ L') :
    (ordinaryFiniteTensorRightMapIso R T e v).hom = e.hom ⊗ₘ v.hom := by
  rfl

@[reassoc]
private theorem line_arrow (φ : A →+* B) (N : ℕ) (hN : 0 < N)
    (hA : (N : A) = 0) (hB : (N : B) = 0)
    (S : Scheme.{u}) (hS : IsUnit (N : Γ(S, ⊤)))
    {K : DerivedCategoryModule A S} {K' : DerivedCategoryModule B S}
    (b : (scalarExtension φ S).obj K ⟶ K') :
    lineSource φ N hN hA hB S hS K ≫ (affineTraceLineRight B N hB S).map b =
      pullMap φ (ProjectiveLine.affineChart S)
        (tensorMap φ (ProjectiveLine S) (pullMap φ (ProjectiveLine S ↘ S) b)
          (line φ N hN hA hB (ProjectiveLine S) (ordinaryFiniteP1_isUnit N S hS))) := by
  have hs : lineSource φ N hN hA hB S hS K =
      pullMap φ (ProjectiveLine.affineChart S)
        (tensorMap φ (ProjectiveLine S)
          ((scalarPullbackIso φ (ProjectiveLine S ↘ S)).inv.app K)
          (line φ N hN hA hB (ProjectiveLine S) (ordinaryFiniteP1_isUnit N S hS))) := by
    simp only [lineSource, projectiveSource, pullMap, tensorMap, MonoidalCategory.tensorHom_def,
      ordinaryFiniteTensor, derivedTensor, curriedTensor_map_app,
      curriedTensor_obj_map]
    rfl
  rw [hs]
  simp only [affineTraceLineRight, ordinaryFiniteP1Right, ordinaryFiniteTwistedPullback,
    Functor.comp_map, derivedTensorRight, derivedTensor, Functor.flip_obj_map,
    curriedTensor_map_app, ← MonoidalCategory.tensorHom_id]
  change pullMap φ (ProjectiveLine.affineChart S)
      (tensorMap φ (ProjectiveLine S) ((scalarPullbackIso φ (ProjectiveLine S ↘ S)).inv.app K)
        (line φ N hN hA hB (ProjectiveLine S) (ordinaryFiniteP1_isUnit N S hS))) ≫
    (ordinaryFinitePullback B (ProjectiveLine.affineChart S)).map
      ((ordinaryFinitePullback B (ProjectiveLine S ↘ S)).map b ⊗ₘ 𝟙 _) = _
  rw [pullMap_post, tensorMap_post]
  simp only [Category.comp_id]
  rfl

@[reassoc]
private theorem line_descent (φ : A →+* B) (N : ℕ) (hN : 0 < N)
    (hA : (N : A) = 0) (hB : (N : B) = 0)
    (S : Scheme.{u}) (hS : IsUnit (N : Γ(S, ⊤)))
    {K : DerivedCategoryModule A S} {K' : DerivedCategoryModule B S}
    (b : (scalarExtension φ S).obj K ⟶ K') :
    (scalarExtension φ (AffineSpace PUnit.{u + 1} S)).map
        (affineLinearLineDescent A N hA (projectiveLineTraceTransport N hN A hA)
          S hS K).hom ≫
      pullMap φ (AffineSpace PUnit.{u + 1} S ↘ S)
        (tensorMap φ S b (line φ N hN hA hB S hS)) =
    lineSource φ N hN hA hB S hS K ≫ (affineTraceLineRight B N hB S).map b ≫
      (affineLinearLineDescent B N hB (projectiveLineTraceTransport N hN B hB)
        S hS K').hom := by
  let j := ProjectiveLine.affineChart S
  let q := ProjectiveLine S ↘ S
  let h := AffineSpace PUnit.{u + 1} S ↘ S
  let tA := projectiveLineTraceTransport N hN A hA
  let tB := projectiveLineTraceTransport N hN B hB
  have hp := pull_comp φ q j h (ProjectiveLine.affineChart_over S) b
  have hl := line_pull φ N hN hA hB tA tB h
    (affineTraceInvertible N S hS 1) hS
  have hj := finite_tate_scalar_pullback_square φ N hN hA hB tA tB j
    (affineTraceInvertible N S hS 1) (affineTraceProjectiveInvertible N S hS)
  simp only [← Category.assoc] at hj
  change (scalarExtension φ (AffineSpace PUnit.{u + 1} S)).map
      (ordinaryFiniteShiftedLinePullback A N hA tA j
        (affineTraceProjectiveInvertible N S hS)).hom ≫
      line φ N hN hA hB (AffineSpace PUnit.{u + 1} S)
        (affineTraceInvertible N S hS 1) =
    pullMap φ j (line φ N hN hA hB (ProjectiveLine S)
      (affineTraceProjectiveInvertible N S hS)) ≫
      (ordinaryFiniteShiftedLinePullback B N hB tB j
        (affineTraceProjectiveInvertible N S hS)).hom at hj
  simp only [affineLinearLineDescent, Iso.trans_hom, Iso.symm_hom, tensor_iso_hom,
    Iso.app_hom, Functor.map_comp, Category.assoc]
  rw [tensor_pull_inv]
  rw [tensorMap_pre_assoc]
  simp only [Functor.map_comp, Category.assoc]
  rw [hp, hl, reassoc_of% hj]
  rw [← tensorMap_post_assoc, tensor_pull_assoc]
  rw [← line_arrow φ N hN hA hB S hS b]
  simp only [Category.assoc]
  rfl

@[reassoc]
private theorem tensor_descent (φ : A →+* B) (N : ℕ) (hN : 0 < N)
    (hA : (N : A) = 0) (hB : (N : B) = 0)
    (tA : OrdinaryFiniteTwistTransport A N hA)
    (tB : OrdinaryFiniteTwistTransport B N hB)
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hX : IsUnit (N : Γ(X, ⊤))) (hY : IsUnit (N : Γ(Y, ⊤)))
    {K : DerivedCategoryModule A Y} {K' : DerivedCategoryModule B Y}
    {M : DerivedCategoryModule A X} {M' : DerivedCategoryModule B X}
    (eA : M ≅ (ordinaryFinitePullback A f).obj K)
    (eB : M' ≅ (ordinaryFinitePullback B f).obj K')
    (b : (scalarExtension φ Y).obj K ⟶ K') :
    (scalarExtension φ X).map
        (ordinaryFiniteTensorRightMapIso A X eA
            (ordinaryFiniteShiftedLinePullback A N hA tA f hY).symm ≪≫
          (ordinaryFiniteTensorPullback A f K
            ((ordinaryFiniteLine A N hA Y)⟦(2 : ℤ)⟧)).symm).hom ≫
      pullMap φ f (tensorMap φ Y b (line φ N hN hA hB Y hY)) =
    tensorMap φ X ((scalarExtension φ X).map eA.hom ≫ pullMap φ f b ≫ eB.inv)
        (line φ N hN hA hB X hX) ≫
      (ordinaryFiniteTensorRightMapIso B X eB
          (ordinaryFiniteShiftedLinePullback B N hB tB f hY).symm ≪≫
        (ordinaryFiniteTensorPullback B f K'
          ((ordinaryFiniteLine B N hB Y)⟦(2 : ℤ)⟧)).symm).hom := by
  simp only [Iso.trans_hom, tensor_iso_hom, Iso.symm_hom, Functor.map_comp,
    Category.assoc]
  rw [tensor_pull_inv, tensorMap_pre_assoc, line_pull φ N hN hA hB tA tB f hX hY]
  rw [tensorMap_post_assoc]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

private theorem pullback_id_eq (R : Type (u + 1)) [CommRing R] (S : Scheme.{u}) :
    affineLinearPullbackId R S = leftDerivedUpperStarId (ModuleCat.{u + 1} R) S := by
  simp only [affineLinearPullbackId, leftDerivedUpperStarId,
    Functor.leftDerivedFunctorNatIso, leftDerivedUpperStarIsoMapDerivedCategory,
    Iso.trans_assoc, Iso.symm_self_id_assoc]

private theorem source_zero (φ : A →+* B) (N : ℕ) (hN : 0 < N)
    (hA : (N : A) = 0) (hB : (N : B) = 0)
    (S : Scheme.{u}) (hS : IsUnit (N : Γ(S, ⊤))) :
    affineCoefficient φ N hN hA hB S hS 0 = unit φ S := by
  have hi := (etaleScalarPullbackIdentityNormalization φ S).2.2
    (ordinaryFiniteUnit A S)
  dsimp only [affineCoefficient, affineLinearCoefficientDescent, pullBase, base]
  simp only [Category.assoc]
  change (scalarExtension φ S).map
      ((affineLinearPullbackId A S).inv.app (ordinaryFiniteUnit A S)) ≫
    (scalarPullbackIso φ (𝟙 S)).inv.app (ordinaryFiniteUnit A S) ≫
      (ordinaryFinitePullback B (𝟙 S)).map (unit φ S) ≫
        (affineLinearPullbackId B S).hom.app (ordinaryFiniteUnit B S) = _
  rw [pullback_id_eq, pullback_id_eq]
  have hn := (leftDerivedUpperStarId (ModuleCat.{u + 1} B) S).hom.naturality
    (unit φ S)
  simp only [Functor.id_map] at hn
  erw [hn]
  apply (cancel_epi ((scalarExtension φ S).map
    ((leftDerivedUpperStarId (ModuleCat.{u + 1} A) S).hom.app
      (ordinaryFiniteUnit A S)))).1
  simp only [← Functor.map_comp_assoc, Iso.hom_inv_id_app,
    CategoryTheory.Functor.map_id, Category.id_comp]
  rw [← hi]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc]

private theorem source_succ (φ : A →+* B) (N : ℕ) (hN : 0 < N)
    (hA : (N : A) = 0) (hB : (N : B) = 0)
    (S : Scheme.{u}) (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ) :
    affineCoefficient φ N hN hA hB S hS (d + 1) =
      lineSource φ N hN hA hB (affineTraceTower S d)
          (affineTraceInvertible N S hS d)
          ((affineTraceRight A N hA S d).obj (ordinaryFiniteUnit A S)) ≫
        (affineTraceLineRight B N hB (affineTraceTower S d)).map
          (affineCoefficient φ N hN hA hB S hS d) := by
  let X := affineTraceTower S d
  let p := affineTraceProjection S d
  let h := AffineSpace PUnit.{u + 1} X ↘ X
  let tA := projectiveLineTraceTransport N hN A hA
  let tB := projectiveLineTraceTransport N hN B hB
  let eA := affineLinearCoefficientDescent A N hA tA S hS d
  let eB := affineLinearCoefficientDescent B N hB tB S hS d
  let wA := ordinaryFiniteTensorRightMapIso A X eA
      (ordinaryFiniteShiftedLinePullback A N hA tA p hS).symm ≪≫
    (ordinaryFiniteTensorPullback A p (affineLinearBaseCoefficient A N hA S d)
      ((ordinaryFiniteLine A N hA S)⟦(2 : ℤ)⟧)).symm
  let wB := ordinaryFiniteTensorRightMapIso B X eB
      (ordinaryFiniteShiftedLinePullback B N hB tB p hS).symm ≪≫
    (ordinaryFiniteTensorPullback B p (affineLinearBaseCoefficient B N hB S d)
      ((ordinaryFiniteLine B N hB S)⟦(2 : ℤ)⟧)).symm
  have hp := pull_comp φ p h (h ≫ p) rfl (base φ N hN hA hB S hS (d + 1))
  have ht := tensor_descent φ N hN hA hB tA tB p
    (affineTraceInvertible N S hS d) hS eA eB (base φ N hN hA hB S hS d)
  change (scalarExtension φ X).map wA.hom ≫
      pullMap φ p (tensorMap φ S (base φ N hN hA hB S hS d)
        (line φ N hN hA hB S hS)) =
    tensorMap φ X (affineCoefficient φ N hN hA hB S hS d)
      (line φ N hN hA hB X (affineTraceInvertible N S hS d)) ≫ wB.hom at ht
  have hl := line_descent φ N hN hA hB X (affineTraceInvertible N S hS d)
    (affineCoefficient φ N hN hA hB S hS d)
  apply (cancel_mono
    (affineLinearCoefficientDescent B N hB
      (projectiveLineTraceTransport N hN B hB) S hS (d + 1)).hom).1
  conv_lhs =>
    unfold affineCoefficient
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  simp only [Category.assoc]
  change (scalarExtension φ (AffineSpace PUnit.{u + 1} X)).map
      ((affineLinearLineDescent A N hA tA X (affineTraceInvertible N S hS d)
          ((affineTraceRight A N hA S d).obj (ordinaryFiniteUnit A S))).hom ≫
        (ordinaryFinitePullback A h).map wA.hom ≫
          (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) h p).inv.app
            (affineLinearBaseCoefficient A N hA S (d + 1))) ≫
      pullMap φ (h ≫ p) (base φ N hN hA hB S hS (d + 1)) =
    lineSource φ N hN hA hB X (affineTraceInvertible N S hS d)
        ((affineTraceRight A N hA S d).obj (ordinaryFiniteUnit A S)) ≫
      (affineTraceLineRight B N hB X).map (affineCoefficient φ N hN hA hB S hS d) ≫
        (affineLinearLineDescent B N hB tB X (affineTraceInvertible N S hS d)
          ((affineTraceRight B N hB S d).obj (ordinaryFiniteUnit B S))).hom ≫
        (ordinaryFinitePullback B h).map wB.hom ≫
          (leftDerivedUpperStarComp (ModuleCat.{u + 1} B) h p).inv.app
            (affineLinearBaseCoefficient B N hB S (d + 1))
  rw [Functor.map_comp, Functor.map_comp]
  simp only [Category.assoc]
  rw [hp, pullMap_pre_assoc]
  rw [show base φ N hN hA hB S hS (d + 1) =
      tensorMap φ S (base φ N hN hA hB S hS d) (line φ N hN hA hB S hS) from rfl]
  rw [ht, ← pullMap_post]
  simp only [Category.assoc]
  rw [reassoc_of% hl]
  rfl

/-- The recursive source comparison is the specified descended Tate coefficient map.
Source: vector-bundle-purity proof paragraph 2, compatibility of the normalized Tate maps
with pullback and ordered tensor products.
Proof: the balancing family is uniquely determined on local pure root/scalar generators.
Inverse image preserves those generator formulas, hence carries balancing to balancing.
The scalar/single comparison on the flat Tate line identifies the derived line square
with this ordinary square. Shift naturality gives the shifted line square. Induct on d.
At zero the scalar/pullback identity equation identifies the two unit maps. At a successor,
expand affineLinearCoefficientDescentStep. The scalar/pullback tensor equation moves the
scalar tensorator through geometric tensor pullback; the shifted line square moves the
last Tate factor. Pullback-composition coherence joins the chart and projection factors.
Tensorator naturality moves the induction equation through the first tensor factor.
Cancel the inverse descent isomorphisms. The resulting composite is exactly lineSource
followed by the preceding towerSource and the image of the coefficient unit. No tensor
factor is permuted. This works for d=0, N=1, zero rings and empty schemes.
(blueprint: lem-pur-vector-scalar-affine-source-compatibility). -/
theorem affine_source_compatibility (φ : A →+* B) (N : ℕ) (hN : 0 < N)
    (hA : (N : A) = 0) (hB : (N : B) = 0)
    (S : Scheme.{u}) (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ) :
    affineCoefficient φ N hN hA hB S hS d =
      towerSource φ N hN hA hB S hS d (ordinaryFiniteUnit A S) ≫
        (affineTraceRight B N hB S d).map (unit φ S) := by
  induction d with
  | zero =>
      rw [towerSource, Category.id_comp]
      exact (source_zero φ N hN hA hB S hS).trans (by rfl)
  | succ d ih =>
      rw [source_succ, ih]
      simp only [towerSource, Functor.map_comp, Category.assoc, Functor.comp_map]

end AlgebraicGeometry.Etale.VectorTraceScalar
