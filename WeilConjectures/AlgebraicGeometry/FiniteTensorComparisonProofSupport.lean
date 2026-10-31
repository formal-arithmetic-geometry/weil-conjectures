/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.RingedDerivedComparisonData
public import WeilConjectures.AlgebraicGeometry.CochainPullbackTensorShift
public import WeilConjectures.Algebra.Homology.KFlatTotalTensorModelSupplement
public import Mathlib.Algebra.Homology.BifunctorShift

/-! # Proof support for finite tensor comparison descent

Source: Stacks 07A4 and the normalized composition argument. The tensor square
for a composite is obtained by pasting the two representative squares. Fully
faithful restriction then proves its equality on arbitrary derived objects.
The native tensor instance lemmas cache the existing sheaf-module instances. The
uncurried cochain comparison and its tensor-map API retain their original formulas.
(blueprint: lem-pur-finite-tensor-comparison-proof-support).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.defeqAttrib.useBackward false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u w
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor MonoidalCategory
open CategoryTheory.CochainPullback CategoryTheory.RingedDerivedComparisons
open WeilConjectures

attribute [-instance] CategoryTheory.hasSheafCompose_of_preservesMulticospan
attribute [local instance 100000] HomologicalComplex.monoidalCategoryStruct
attribute [local irreducible] CommRingCat.hasForgetToRingCat sheafCompose
  CommRingCat.instConcreteCategoryRingHomCarrier RingCat.instConcreteCategoryRingHomCarrier
  SheafOfModules.instCategory HomologicalComplex.instCategory
  SheafOfModules.monoidalCategory SheafOfModules.instPreadditive
  HomologicalComplex.instPreadditive
  CochainComplex.IsKFlatIndependentCoefficients SheafOfModules.IsFlatOnSite
  SheafOfModules.siteSheafTensorRight
  DerivedCategory instCategoryDerivedCategory DerivedCategory.Q DerivedCategory.Qh
  CategoryTheory.Functor.mapHomologicalComplex
  CategoryTheory.Functor.mapBifunctorHomologicalComplex
  HomologicalComplex.mapBifunctorMap
  CategoryTheory.CochainPullback.compositionModule
  CategoryTheory.Functor.mapHomologicalComplexCompIso
  HomologicalComplex₂.total CategoryTheory.CochainPullback.comparison
  HomologicalComplex.single CategoryTheory.CochainPullback.extensionComparison

namespace CategoryTheory.FiniteTensorComparisonProofSupport

section PrivateInstanceProofs


theorem cachedTensorAdditive {C : Type u} [SmallCategory C]
    {J : GrothendieckTopology C} (R : Sheaf J CommRingCat.{u}) :
    (curriedTensor (Modules R)).Additive := inferInstance

theorem cachedTensorAdditiveObj {C : Type u} [SmallCategory C]
    {J : GrothendieckTopology C} (R : Sheaf J CommRingCat.{u})
    (M : Modules R) : ((curriedTensor (Modules R)).obj M).Additive := inferInstance

theorem cachedTensorLeftZero {C : Type u} [SmallCategory C]
    {J : GrothendieckTopology C} (R : Sheaf J CommRingCat.{u}) (M : Modules R) :
    PreservesColimit (Functor.empty.{0} (Modules R))
      ((curriedTensor (Modules R)).obj M) := inferInstance

theorem cachedTensorRightZero {C : Type u} [SmallCategory C]
    {J : GrothendieckTopology C} (R : Sheaf J CommRingCat.{u}) (M : Modules R) :
    PreservesColimit (Functor.empty.{0} (Modules R))
      ((curriedTensor (Modules R)).flip.obj M) := inferInstance

attribute [local instance high] cachedTensorAdditive cachedTensorAdditiveObj
  cachedTensorLeftZero cachedTensorRightZero

theorem totalTensor_exists {C : Type u} [SmallCategory C]
    {J : GrothendieckTopology C} (R : Sheaf J CommRingCat.{u})
    (P Q : CochainPullback.Complex.{u, u, u} R) :
    HomologicalComplex.HasMapBifunctor P Q (curriedTensor (Modules R)) (.up ℤ) :=
  inferInstance

theorem cachedGradedTensor {C : Type u} [SmallCategory C]
    {J : GrothendieckTopology C} (R : Sheaf J CommRingCat.{u})
    (P Q : GradedObject ℤ (Modules R)) : P.HasTensor Q := inferInstance

theorem cachedGradedFour {C : Type u} [SmallCategory C]
    {J : GrothendieckTopology C} (R : Sheaf J CommRingCat.{u})
    (P Q V W : GradedObject ℤ (Modules R)) :
    GradedObject.HasTensor₄ObjExt P Q V W := inferInstance

theorem cachedGradedLeft {C : Type u} [SmallCategory C]
    {J : GrothendieckTopology C} (R : Sheaf J CommRingCat.{u})
    (P Q V : GradedObject ℤ (Modules R)) :
    GradedObject.HasGoodTensor₁₂Tensor P Q V := inferInstance

theorem cachedGradedRight {C : Type u} [SmallCategory C]
    {J : GrothendieckTopology C} (R : Sheaf J CommRingCat.{u})
    (P Q V : GradedObject ℤ (Modules R)) :
    GradedObject.HasGoodTensorTensor₂₃ P Q V := inferInstance

end PrivateInstanceProofs


section NativeCochainComparison

attribute [local instance high] cachedTensorAdditive cachedTensorAdditiveObj
  cachedTensorLeftZero cachedTensorRightZero cachedGradedTensor cachedGradedFour
  cachedGradedLeft cachedGradedRight totalTensor_exists

def uncurry_comparison
    {A B : Type*} [Category A] [Category B]
    (T : A ⥤ A ⥤ A) (T' : B ⥤ B ⥤ B) (F : A ⥤ B)
    (t : (Functor.postcompose₂.obj F).obj T ⟶
      (((Functor.whiskeringLeft₂ B).obj F).obj F).obj T')
    (h : ∀ P Q, IsIso ((t.app P).app Q)) :
    Functor.uncurry.obj T ⋙ F ≅ F.prod F ⋙ Functor.uncurry.obj T' :=
  NatIso.ofComponents (fun X ↦ @asIso _ _ _ _ ((t.app X.1).app X.2) (h X.1 X.2)) (by
    intro X Y a
    have ha := NatTrans.congr_app (t.naturality a.1) X.2
    have hb := (t.app Y.1).naturality a.2
    change F.map ((T.map a.1).app X.2) ≫ (t.app Y.1).app X.2 =
      (t.app X.1).app X.2 ≫ (T'.map (F.map a.1)).app (F.obj X.2) at ha
    change F.map ((T.obj Y.1).map a.2) ≫ (t.app Y.1).app Y.2 =
      (t.app Y.1).app X.2 ≫ (T'.obj (F.obj Y.1)).map (F.map a.2) at hb
    change F.map ((T.map a.1).app X.2 ≫ (T.obj Y.1).map a.2) ≫
      (t.app Y.1).app Y.2 = (t.app X.1).app X.2 ≫
      ((T'.map (F.map a.1)).app (F.obj X.2) ≫ (T'.obj (F.obj Y.1)).map (F.map a.2))
    rw [F.map_comp, Category.assoc, hb, ← Category.assoc, ha, Category.assoc])

def cochain_comparison {X Y : Site.{u, w}}
    (f : RingedPullback.{u, u, u, u, u} Y.A X.A)
    (k : CochainPullback.Comparison.{u, u, u, u, u} f) :
    coefficientTotalTensor.{u, u, u} Y.J Y.A ⋙ CochainPullback.pull.{u, u, u, u, u} f ≅
      ((CochainPullback.pull.{u, u, u, u, u} f).prod (CochainPullback.pull.{u, u, u, u, u} f)) ⋙
        coefficientTotalTensor.{u, u, u} X.J X.A :=
  uncurry_comparison (SheafOfModules.KFlatFixedTensor.totalTensor.{u, u, u} Y.A)
    (SheafOfModules.KFlatFixedTensor.totalTensor.{u, u, u} X.A)
    (CochainPullback.pull.{u, u, u, u, u} f)
    (CochainPullback.tensorComparisonNatTrans.{u, u, u, u, u} f k) (fun P Q ↦ by
      change IsIso (CochainPullback.comparison f k P Q).hom
      infer_instance)

theorem cochain_comparison_hom_app {X Y : Site.{u, w}}
    (f : RingedPullback.{u, u, u, u, u} Y.A X.A)
    (k : CochainPullback.Comparison.{u, u, u, u, u} f)
    (P Q : CochainPullback.Complex.{u, u, u} Y.A) :
    (cochain_comparison f k).hom.app (P, Q) =
      (CochainPullback.comparison f k P Q).hom := rfl

theorem total_tensor_map (X : Site.{u, w})
    {P Q P' Q' : CochainPullback.Complex.{u, u, u} X.A}
    [HomologicalComplex.HasMapBifunctor P Q (curriedTensor (Modules X.A)) (.up ℤ)]
    [HomologicalComplex.HasMapBifunctor P' Q' (curriedTensor (Modules X.A)) (.up ℤ)]
    (a : P ⟶ P') (b : Q ⟶ Q') :
    (coefficientTotalTensor.{u, u, u} X.J X.A).map (Prod.mkHom a b) =
      HomologicalComplex.tensorHom a b := by
  have : ∀ P Q : CochainPullback.Complex.{u, u, u} X.A,
      HomologicalComplex.HasMapBifunctor P Q (curriedTensor (Modules X.A)) (.up ℤ) :=
    totalTensor_exists X.A
  change HomologicalComplex.mapBifunctorMap a (𝟙 Q) _ _ ≫
    HomologicalComplex.mapBifunctorMap (𝟙 P') b _ _ =
      HomologicalComplex.mapBifunctorMap a b _ _
  simp only [HomologicalComplex.mapBifunctorMap, Functor.map_id, NatTrans.id_app,
    Category.comp_id, Category.id_comp, ← HomologicalComplex₂.total.map_comp]

/-- Naturality of the recorded derived tensor model on K-flat representatives.
Source: Stacks 07A4; this is the supplied model's naturality equation.
(blueprint: lem-pur-finite-tensor-comparison-proof-support). -/
theorem tensor_model_naturality (X : Site.{u, w})
    {P Q P' Q' : CochainPullback.Complex.{u, u, u} X.A}
    (hP : CochainComplex.IsKFlatIndependentCoefficients P)
    (hQ : CochainComplex.IsKFlatIndependentCoefficients Q)
    (hP' : CochainComplex.IsKFlatIndependentCoefficients P')
    (hQ' : CochainComplex.IsKFlatIndependentCoefficients Q')
    (a : P ⟶ P') (b : Q ⟶ Q') :
    DerivedCategory.Q.map (HomologicalComplex.tensorHom a b) ≫
        (X.model.iso X.J X.A X.closed P' Q' hP' hQ').hom =
      (X.model.iso X.J X.A X.closed P Q hP hQ).hom ≫
        X.closed.tensor.map (Prod.mkHom (DerivedCategory.Q.map a) (DerivedCategory.Q.map b)) := by
  have hh := X.model.comparison.hom.naturality
    (Prod.mkHom
      (show (⟨P, hP⟩ : ObjectProperty.FullSubcategory
        (CochainComplex.IsKFlatIndependentCoefficients (J := X.J) (R := X.A))) ⟶
          ⟨P', hP'⟩ from ObjectProperty.homMk a)
      (show (⟨Q, hQ⟩ : ObjectProperty.FullSubcategory
        (CochainComplex.IsKFlatIndependentCoefficients (J := X.J) (R := X.A))) ⟶
          ⟨Q', hQ'⟩ from ObjectProperty.homMk b))
  change DerivedCategory.Q.map
      ((coefficientTotalTensor.{u, u, u} X.J X.A).map (Prod.mkHom a b)) ≫
      (X.model.iso X.J X.A X.closed P' Q' hP' hQ').hom =
    (X.model.iso X.J X.A X.closed P Q hP hQ).hom ≫
      X.closed.tensor.map (Prod.mkHom (DerivedCategory.Q.map a) (DerivedCategory.Q.map b)) at hh
  rw [total_tensor_map] at hh
  exact hh

/-- The existing cochain compositor, before evaluating at a complex.
Source: Stacks 0D6D.
(blueprint: lem-pur-finite-tensor-comparison-proof-support). -/
def cochain_compositor {X Y Z : Site.{u, w}}
    (f : RingedPullback.{u, u, u, u, u} Z.A Y.A)
    (g : RingedPullback.{u, u, u, u, u} Y.A X.A)
    (h : RingedPullback.{u, u, u, u, u} Z.A X.A)
    {kf : Comparison f} {kg : Comparison g} {kh : Comparison h}
    (a : CompositePresentation f g h kf kg kh) :
    CochainPullback.pull h ≅ CochainPullback.pull f ⋙ CochainPullback.pull g :=
  (Functor.mapHomologicalComplexCompIso
    (CochainPullback.compositionModule f g h a.rightModules).symm (.up ℤ)).symm

/-- Evaluating the cochain compositor gives the prescribed composition comparison.
Source: Stacks 0D6D.
(blueprint: lem-pur-finite-tensor-comparison-proof-support). -/
theorem cochain_compositor_hom_app {X Y Z : Site.{u, w}}
    (f : RingedPullback.{u, u, u, u, u} Z.A Y.A)
    (g : RingedPullback.{u, u, u, u, u} Y.A X.A)
    (h : RingedPullback.{u, u, u, u, u} Z.A X.A)
    {kf : Comparison f} {kg : Comparison g} {kh : Comparison h}
    (a : CompositePresentation f g h kf kg kh)
    (P : CochainPullback.Complex.{u, u, u} Z.A) :
    (cochain_compositor f g h a).hom.app P =
      (CochainPullback.composition f g h a P).hom := rfl

/-- Tensor compatibility of the same cochain compositor.
Source: Stacks 07A4 and the balanced cochain composition equation.
(blueprint: lem-pur-finite-tensor-comparison-proof-support). -/
theorem cochain_composition_tensor {X Y Z : Site.{u, w}}
    (f : RingedPullback.{u, u, u, u, u} Z.A Y.A)
    (g : RingedPullback.{u, u, u, u, u} Y.A X.A)
    (h : RingedPullback.{u, u, u, u, u} Z.A X.A)
    (kf : Comparison f) (kg : Comparison g) (kh : Comparison h)
    (a : CompositePresentation f g h kf kg kh)
    (P Q : CochainPullback.Complex.{u, u, u} Z.A) :
    (CochainPullback.comparison h kh P Q).hom ≫
        HomologicalComplex.tensorHom ((cochain_compositor f g h a).hom.app P)
          ((cochain_compositor f g h a).hom.app Q) =
      (cochain_compositor f g h a).hom.app (P ⊗ Q) ≫
        (CochainPullback.pull g).map (CochainPullback.comparison f kf P Q).hom ≫
          (CochainPullback.comparison g kg ((CochainPullback.pull f).obj P)
            ((CochainPullback.pull f).obj Q)).hom := by
  have hh := (CochainPullback.cochainPullbackTensorCoherence f kf).2.1 g h kg kh a P Q
  simp only [CochainPullback.composition, Iso.app_hom] at hh
  with_unfolding_all exact hh

end NativeCochainComparison

section TensorSquare
variable {K H D E : Type*} [Category K] [Category H] [Category D] [Category E]
private def composite_comparison
    {L : Type*} [Category L]
    (T : K × K ⥤ K) (T' : H × H ⥤ H) (T'' : L × L ⥤ L)
    (F : K ⥤ H) (G : H ⥤ L)
    (nF : T ⋙ F ⟶ F.prod F ⋙ T') (nG : T' ⋙ G ⟶ G.prod G ⋙ T'') :
    T ⋙ (F ⋙ G) ⟶ (F ⋙ G).prod (F ⋙ G) ⋙ T'' :=
  Functor.whiskerRight nF G ≫ Functor.whiskerLeft (F.prod F) nG

-- Equality of the derived tensor square follows by cancelling the computation maps.
private theorem normalized_tensor_square
    (q : K ⥤ D) (q' : H ⥤ E) (t : K → K → K) (t' : H → H → H)
    (T : D × D ⥤ D) (T' : E × E ⥤ E)
    (U V : K ⥤ H) (F G : D ⥤ E)
    (eF : q ⋙ F ⟶ U ⋙ q') (eG : q ⋙ G ⟶ V ⋙ q')
    (nF : T ⋙ F ⟶ F.prod F ⋙ T') (nG : T ⋙ G ⟶ G.prod G ⋙ T')
    (bF : ∀ P Q, U.obj (t (P) (Q)) ⟶ t' (U.obj P) (U.obj Q))
    (bG : ∀ P Q, V.obj (t (P) (Q)) ⟶ t' (V.obj P) (V.obj Q))
    (c : F ⟶ G) (a : U ⟶ V) (P Q : K)
    (am : t' (U.obj P) (U.obj Q) ⟶ t' (V.obj P) (V.obj Q))
    (r : q.obj (t (P) (Q)) ≅ T.obj (q.obj P, q.obj Q))
    (rU : q'.obj (t' (U.obj P) (U.obj Q)) ≅
      T'.obj (q'.obj (U.obj P), q'.obj (U.obj Q)))
    (rV : q'.obj (t' (V.obj P) (V.obj Q)) ≅
      T'.obj (q'.obj (V.obj P), q'.obj (V.obj Q)))
    [IsIso (eG.app P)] [IsIso (eG.app Q)]
    (hnF : F.map r.hom ≫ nF.app (q.obj P, q.obj Q) ≫
      T'.map (Prod.mkHom (eF.app P) (eF.app Q)) =
        eF.app (t (P) (Q)) ≫ q'.map (bF P Q) ≫ rU.hom)
    (hnG : G.map r.hom ≫ nG.app (q.obj P, q.obj Q) ≫
      T'.map (Prod.mkHom (eG.app P) (eG.app Q)) =
        eG.app (t (P) (Q)) ≫ q'.map (bG P Q) ≫ rV.hom)
    (hcP : c.app (q.obj P) ≫ eG.app P = eF.app P ≫ q'.map (a.app P))
    (hcQ : c.app (q.obj Q) ≫ eG.app Q = eF.app Q ≫ q'.map (a.app Q))
    (hcT : c.app (q.obj (t (P) (Q))) ≫ eG.app (t (P) (Q)) =
      eF.app (t (P) (Q)) ≫ q'.map (a.app (t (P) (Q))))
    (ha : bF P Q ≫ am =
      a.app (t (P) (Q)) ≫ bG P Q)
    (hr : q'.map (am) ≫ rV.hom =
      rU.hom ≫ T'.map (Prod.mkHom (q'.map (a.app P)) (q'.map (a.app Q)))) :
    nF.app (q.obj P, q.obj Q) ≫ T'.map (Prod.mkHom (c.app (q.obj P)) (c.app (q.obj Q))) =
      c.app (T.obj (q.obj P, q.obj Q)) ≫ nG.app (q.obj P, q.obj Q) := by
  have : IsIso (Prod.mkHom (eG.app P) (eG.app Q)) :=
    ⟨⟨Prod.mkHom (inv (eG.app P)) (inv (eG.app Q)),
      by ext <;> simp, by ext <;> simp⟩⟩
  apply (cancel_epi (F.map r.hom)).1
  apply (cancel_mono (T'.map (Prod.mkHom (eG.app P) (eG.app Q)))).1
  simp only [Category.assoc]
  rw [← T'.map_comp]
  have hp : Prod.mkHom (c.app (q.obj P)) (c.app (q.obj Q)) ≫
      Prod.mkHom (eG.app P) (eG.app Q) =
      Prod.mkHom (eF.app P) (eF.app Q) ≫
        Prod.mkHom (q'.map (a.app P)) (q'.map (a.app Q)) := by
    ext <;> first | exact hcP | exact hcQ
  rw [hp, T'.map_comp]
  calc
    _ = (F.map r.hom ≫ nF.app (q.obj P, q.obj Q) ≫
        T'.map (Prod.mkHom (eF.app P) (eF.app Q))) ≫
        T'.map (Prod.mkHom (q'.map (a.app P)) (q'.map (a.app Q))) := by
      simp only [Category.assoc]
    _ = eF.app (t (P) (Q)) ≫ q'.map (bF P Q) ≫
        rU.hom ≫ T'.map (Prod.mkHom (q'.map (a.app P)) (q'.map (a.app Q))) := by
      rw [hnF]; simp only [Category.assoc]
    _ = eF.app (t (P) (Q)) ≫
        q'.map (bF P Q ≫ am) ≫ rV.hom := by
      rw [q'.map_comp]; simp only [Category.assoc, hr]
    _ = (c.app (q.obj (t (P) (Q))) ≫ eG.app (t (P) (Q))) ≫
        q'.map (bG P Q) ≫ rV.hom := by
      rw [ha, q'.map_comp, hcT]; simp only [Category.assoc]
    _ = c.app (q.obj (t (P) (Q))) ≫ G.map r.hom ≫
        nG.app (q.obj P, q.obj Q) ≫ T'.map (Prod.mkHom (eG.app P) (eG.app Q)) := by
      simp only [Category.assoc]
      rw [← hnG]
    _ = _ := by
      have hn := c.naturality r.hom
      change F.map r.hom ≫ c.app (T.obj (q.obj P, q.obj Q)) =
        c.app (q.obj (t (P) (Q))) ≫ G.map r.hom at hn
      simpa only [Category.assoc] using congrArg
        (fun z ↦ z ≫ nG.app (q.obj P, q.obj Q) ≫
          T'.map (Prod.mkHom (eG.app P) (eG.app Q))) hn.symm

private theorem composite_tensor_square
    {L Z : Type*} [Category L] [Category Z]
    (q : K ⥤ D) (q' : H ⥤ E) (q'' : L ⥤ Z)
    (t : K → K → K) (t' : H → H → H) (t'' : L → L → L)
    (T : D × D ⥤ D) (T' : E × E ⥤ E) (T'' : Z × Z ⥤ Z)
    (U : K ⥤ H) (V : H ⥤ L) (F : D ⥤ E) (G : E ⥤ Z)
    (eF : q ⋙ F ⟶ U ⋙ q') (eG : q' ⋙ G ⟶ V ⋙ q'')
    (nF : T ⋙ F ⟶ F.prod F ⋙ T') (nG : T' ⋙ G ⟶ G.prod G ⋙ T'')
    (bF : ∀ P Q, U.obj (t (P) (Q)) ⟶ t' (U.obj P) (U.obj Q))
    (bG : ∀ P Q, V.obj (t' (P) (Q)) ⟶ t'' (V.obj P) (V.obj Q))
    (P Q : K)
    (r : q.obj (t (P) (Q)) ≅ T.obj (q.obj P, q.obj Q))
    (r' : q'.obj (t' (U.obj P) (U.obj Q)) ≅
      T'.obj (q'.obj (U.obj P), q'.obj (U.obj Q)))
    (r'' : q''.obj (t'' (V.obj (U.obj P)) (V.obj (U.obj Q))) ≅
      T''.obj (q''.obj (V.obj (U.obj P)), q''.obj (V.obj (U.obj Q))))
    (hF : F.map r.hom ≫ nF.app (q.obj P, q.obj Q) ≫
      T'.map (Prod.mkHom (eF.app P) (eF.app Q)) =
        eF.app (t (P) (Q)) ≫ q'.map (bF P Q) ≫ r'.hom)
    (hG : G.map r'.hom ≫ nG.app (q'.obj (U.obj P), q'.obj (U.obj Q)) ≫
      T''.map (Prod.mkHom (eG.app (U.obj P)) (eG.app (U.obj Q))) =
        eG.app (t' (U.obj P) (U.obj Q)) ≫
          q''.map (bG (U.obj P) (U.obj Q)) ≫ r''.hom) :
    G.map (F.map r.hom) ≫
        (G.map (nF.app (q.obj P, q.obj Q)) ≫
          nG.app (F.obj (q.obj P), F.obj (q.obj Q))) ≫
        T''.map (Prod.mkHom
          (G.map (eF.app P) ≫ eG.app (U.obj P))
          (G.map (eF.app Q) ≫ eG.app (U.obj Q))) =
      (G.map (eF.app (t (P) (Q))) ≫ eG.app (U.obj (t (P) (Q)))) ≫
        q''.map (V.map (bF P Q) ≫ bG (U.obj P) (U.obj Q)) ≫ r''.hom := by
  have hp : Prod.mkHom
      (G.map (eF.app P) ≫ eG.app (U.obj P))
      (G.map (eF.app Q) ≫ eG.app (U.obj Q)) =
      Prod.mkHom (G.map (eF.app P)) (G.map (eF.app Q)) ≫
        Prod.mkHom (eG.app (U.obj P)) (eG.app (U.obj Q)) := rfl
  have hn := nG.naturality (Prod.mkHom (eF.app P) (eF.app Q))
  change G.map (T'.map (Prod.mkHom (eF.app P) (eF.app Q))) ≫
      nG.app (q'.obj (U.obj P), q'.obj (U.obj Q)) =
    nG.app (F.obj (q.obj P), F.obj (q.obj Q)) ≫
      T''.map (Prod.mkHom (G.map (eF.app P)) (G.map (eF.app Q))) at hn
  simp only [hp, T''.map_comp, Category.assoc]
  have hn' := congrArg
    (fun z ↦ z ≫ T''.map (Prod.mkHom (eG.app (U.obj P)) (eG.app (U.obj Q)))) hn
  simp only [Category.assoc] at hn'
  rw [← hn']
  have he := eG.naturality (bF P Q)
  change G.map (q'.map (bF P Q)) ≫
      eG.app (t' (U.obj P) (U.obj Q)) =
    eG.app (U.obj (t (P) (Q))) ≫ q''.map (V.map (bF P Q)) at he
  calc
    _ = G.map (F.map r.hom ≫ nF.app (q.obj P, q.obj Q) ≫
        T'.map (Prod.mkHom (eF.app P) (eF.app Q))) ≫
        nG.app (q'.obj (U.obj P), q'.obj (U.obj Q)) ≫
        T''.map (Prod.mkHom (eG.app (U.obj P)) (eG.app (U.obj Q))) := by
      simp only [G.map_comp, Category.assoc]
    _ = G.map (eF.app (t (P) (Q))) ≫ G.map (q'.map (bF P Q)) ≫
        G.map r'.hom ≫ nG.app (q'.obj (U.obj P), q'.obj (U.obj Q)) ≫
        T''.map (Prod.mkHom (eG.app (U.obj P)) (eG.app (U.obj Q))) := by
      rw [hF]; simp only [G.map_comp, Category.assoc]
    _ = G.map (eF.app (t (P) (Q))) ≫ G.map (q'.map (bF P Q)) ≫
        eG.app (t' (U.obj P) (U.obj Q)) ≫
        q''.map (bG (U.obj P) (U.obj Q)) ≫ r''.hom := by
      rw [hG]
    _ = _ := by
      simpa only [Category.assoc, q''.map_comp] using congrArg
        (fun z ↦ G.map (eF.app (t (P) (Q))) ≫ z ≫
          q''.map (bG (U.obj P) (U.obj Q)) ≫ r''.hom) he

/-- A normalized tensor compositor square descends along fully faithful restriction.
Source: Stacks 07A4 and 0D6D, the canonical composition normalization.
(blueprint: lem-pur-finite-tensor-comparison-proof-support).

Proof: form the composite counit and tensor comparison. Naturality pastes the two
normalized representative squares. Compare the pasted square with the specified
third square, cancelling the invertible representative computation maps. This
proves the desired tensor equation after restriction to the resolving subcategory.
Fully faithful precomposition gives equality of the two natural transformations,
and evaluation yields the displayed equation on all objects.
-/
theorem comparison_tensor_descends
    {L Z : Type*} [Category L] [Category Z]
    (q : K ⥤ D) (q' : H ⥤ E) (q'' : L ⥤ Z)
    (t : K → K → K) (t' : H → H → H) (t'' : L → L → L)
    (T : D × D ⥤ D) (T' : E × E ⥤ E) (T'' : Z × Z ⥤ Z)
    (U : K ⥤ H) (V : H ⥤ L) (W : K ⥤ L)
    (F : D ⥤ E) (G : E ⥤ Z) (Fh : D ⥤ Z)
    (eF : q ⋙ F ⟶ U ⋙ q') (eG : q' ⋙ G ⟶ V ⋙ q'')
    (eH : q ⋙ Fh ⟶ W ⋙ q'')
    (nF : T ⋙ F ⟶ F.prod F ⋙ T') (nG : T' ⋙ G ⟶ G.prod G ⋙ T'')
    (nH : T ⋙ Fh ⟶ Fh.prod Fh ⋙ T'')
    (pK : ObjectProperty K) (pH : ObjectProperty H) (pL : ObjectProperty L)
    (hU : ∀ A, pK A → pH (U.obj A)) (hV : ∀ A, pH A → pL (V.obj A))
    (hW : ∀ A, pK A → pL (W.obj A))
    (ht : ∀ A B, pK A → pK B → pK (t A B))
    (ff : (((Functor.whiskeringLeft (pK.FullSubcategory × pK.FullSubcategory)
      (D × D) Z).obj ((pK.ι ⋙ q).prod (pK.ι ⋙ q))).FullyFaithful))
    (r : ∀ A B, pK A → pK B → (q.obj (t A B) ≅ T.obj (q.obj A, q.obj B)))
    (r' : ∀ A B, pH A → pH B → (q'.obj (t' A B) ≅ T'.obj (q'.obj A, q'.obj B)))
    (r'' : ∀ A B, pL A → pL B → (q''.obj (t'' A B) ≅ T''.obj (q''.obj A, q''.obj B)))
    (bF : ∀ A B, U.obj (t A B) ⟶ t' (U.obj A) (U.obj B))
    (bG : ∀ A B, V.obj (t' A B) ⟶ t'' (V.obj A) (V.obj B))
    (bH : ∀ A B, W.obj (t A B) ⟶ t'' (W.obj A) (W.obj B))
    (hnF : ∀ A B hA hB,
      F.map (r A B hA hB).hom ≫ nF.app (q.obj A, q.obj B) ≫
          T'.map (Prod.mkHom (eF.app A) (eF.app B)) =
        eF.app (t A B) ≫ q'.map (bF A B) ≫
          (r' _ _ (hU A hA) (hU B hB)).hom)
    (hnG : ∀ A B hA hB,
      G.map (r' A B hA hB).hom ≫ nG.app (q'.obj A, q'.obj B) ≫
          T''.map (Prod.mkHom (eG.app A) (eG.app B)) =
        eG.app (t' A B) ≫ q''.map (bG A B) ≫
          (r'' _ _ (hV A hA) (hV B hB)).hom)
    (hnH : ∀ A B hA hB,
      Fh.map (r A B hA hB).hom ≫ nH.app (q.obj A, q.obj B) ≫
          T''.map (Prod.mkHom (eH.app A) (eH.app B)) =
        eH.app (t A B) ≫ q''.map (bH A B) ≫
          (r'' _ _ (hW A hA) (hW B hB)).hom)
    (heF : ∀ A, pK A → IsIso (eF.app A))
    (heG : ∀ A, pH A → IsIso (eG.app A))
    (c : Fh ≅ F ⋙ G) (a : W ≅ U ⋙ V)
    (hc : ∀ A, pK A → c.hom.app (q.obj A) ≫ G.map (eF.app A) ≫ eG.app (U.obj A) =
      eH.app A ≫ q''.map (a.hom.app A))
    (am : ∀ A B, t'' (W.obj A) (W.obj B) ⟶ t'' (V.obj (U.obj A)) (V.obj (U.obj B)))
    (ha : ∀ A B, bH A B ≫ am A B =
      a.hom.app (t A B) ≫ V.map (bF A B) ≫ bG (U.obj A) (U.obj B))
    (hr : ∀ A B (hA : pK A) (hB : pK B),
      q''.map (am A B) ≫ (r'' _ _ (hV _ (hU A hA)) (hV _ (hU B hB))).hom =
        (r'' _ _ (hW A hA) (hW B hB)).hom ≫
          T''.map (Prod.mkHom (q''.map (a.hom.app A)) (q''.map (a.hom.app B)))) :
    ∀ M N : D, nH.app (M, N) ≫ T''.map (Prod.mkHom (c.hom.app M) (c.hom.app N)) =
      c.hom.app (T.obj (M, N)) ≫ G.map (nF.app (M, N)) ≫ nG.app (F.obj M, F.obj N) := by
  let e : q ⋙ (F ⋙ G) ⟶ (U ⋙ V) ⋙ q'' :=
    Functor.whiskerRight eF G ≫ Functor.whiskerLeft U eG
  let n := composite_comparison T T' T'' F G nF nG
  let bn A B := V.map (bF A B) ≫ bG (U.obj A) (U.obj B)
  let lhs := nH ≫ Functor.whiskerRight (NatTrans.prod c.hom c.hom) T''
  let rhs := Functor.whiskerLeft T c.hom ≫ n
  have he A (hA : pK A) : IsIso (e.app A) := by
    have := heF A hA
    have := heG _ (hU A hA)
    change IsIso (G.map (eF.app A) ≫ eG.app (U.obj A))
    infer_instance
  have hs : lhs = rhs := by
    apply ff.map_injective
    ext ⟨⟨A, hA⟩, ⟨B, hB⟩⟩
    have := he A hA
    have := he B hB
    apply normalized_tensor_square q q'' t t'' T T'' W (U ⋙ V) Fh (F ⋙ G) eH e
      nH n bH bn c.hom a.hom A B (am A B)
      (r A B hA hB) (r'' _ _ (hW A hA) (hW B hB))
      (r'' _ _ (hV _ (hU A hA)) (hV _ (hU B hB))) (hnH A B hA hB)
      (composite_tensor_square q q' q'' t t' t'' T T' T'' U V F G eF eG nF nG
        bF bG A B (r A B hA hB) (r' _ _ (hU A hA) (hU B hB))
        (r'' _ _ (hV _ (hU A hA)) (hV _ (hU B hB)))
        (hnF A B hA hB) (hnG _ _ (hU A hA) (hU B hB)))
      (hc A hA) (hc B hB) (by
        simpa only [e, NatTrans.comp_app, whiskerRight_app, whiskerLeft_app,
          Category.assoc] using hc (t A B) (ht A B hA hB))
      (by simpa only [bn, Category.assoc] using ha A B) (hr A B hA hB)
  intro M N
  exact congr_app hs (M, N)

end TensorSquare

end CategoryTheory.FiniteTensorComparisonProofSupport
