/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q1
-/
module

public import Sheaf.SecSmoothPurity.CochainCoefficientArrows
public import Sheaf.Paper.PullbackTensorCanonicalShiftUnit
import Sheaf.Algebra.Homology.RingedKFlatWordComparisonDescent
import Sheaf.Paper.DerivedResolvingPairRestriction
import Sheaf.Algebra.Homology.KFlatTotalTensorModel
import Sheaf.Paper.KFlatRingedToposPullback
import Sheaf.Paper.PullbackTensorResolvingComputation
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.Algebra.Homology.DerivedCategory.Fractions

/-! # Normalized coefficient squares for universal derived pullbacks

Source: Stacks Project, sites-cohomology.tex, Tags 07A4, 0G7E and 0D6D,
and the balanced cochain coefficient identity.
(blueprint: lem-pur-normalized-coefficient-tensor-square).

The ordinary scalar-association isomorphism descends using the composite universal
counits. Tensor compatibility follows by pasting their representative squares.
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
open CategoryTheory.CochainPullback

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
  SheafOfModules.PullbackTensorCanonical.canonicalDerivedTensor
  SheafOfModules.PullbackTensorCanonical.canonicalRepresentativeIso
  SheafOfModules.siteDerivedTensorIndependentCoefficients

namespace CategoryTheory.NormalizedCoefficientTensor

section PrivateInstanceProofs

private theorem cachedTensorAdditive {C : Type u} [SmallCategory C]
    {J : GrothendieckTopology C} (R : Sheaf J CommRingCat.{u}) :
    (curriedTensor (Modules R)).Additive := inferInstance

private theorem cachedTensorAdditiveObj {C : Type u} [SmallCategory C]
    {J : GrothendieckTopology C} (R : Sheaf J CommRingCat.{u})
    (M : Modules R) : ((curriedTensor (Modules R)).obj M).Additive := inferInstance

private theorem cachedTensorLeftZero {C : Type u} [SmallCategory C]
    {J : GrothendieckTopology C} (R : Sheaf J CommRingCat.{u}) (M : Modules R) :
    PreservesColimit (Functor.empty.{0} (Modules R))
      ((curriedTensor (Modules R)).obj M) := inferInstance

private theorem cachedTensorRightZero {C : Type u} [SmallCategory C]
    {J : GrothendieckTopology C} (R : Sheaf J CommRingCat.{u}) (M : Modules R) :
    PreservesColimit (Functor.empty.{0} (Modules R))
      ((curriedTensor (Modules R)).flip.obj M) := inferInstance

attribute [local instance high] cachedTensorAdditive cachedTensorAdditiveObj
  cachedTensorLeftZero cachedTensorRightZero

private theorem totalTensor_exists {C : Type u} [SmallCategory C]
    {J : GrothendieckTopology C} (R : Sheaf J CommRingCat.{u})
    (P Q : CochainPullback.Complex.{u, u, u} R) :
    HomologicalComplex.HasMapBifunctor P Q (curriedTensor (Modules R)) (.up ℤ) :=
  inferInstance

private theorem cachedGradedTensor {C : Type u} [SmallCategory C]
    {J : GrothendieckTopology C} (R : Sheaf J CommRingCat.{u})
    (P Q : GradedObject ℤ (Modules R)) : P.HasTensor Q := inferInstance

private theorem cachedGradedFour {C : Type u} [SmallCategory C]
    {J : GrothendieckTopology C} (R : Sheaf J CommRingCat.{u})
    (P Q V W : GradedObject ℤ (Modules R)) :
    GradedObject.HasTensor₄ObjExt P Q V W := inferInstance

private theorem cachedGradedLeft {C : Type u} [SmallCategory C]
    {J : GrothendieckTopology C} (R : Sheaf J CommRingCat.{u})
    (P Q V : GradedObject ℤ (Modules R)) :
    GradedObject.HasGoodTensor₁₂Tensor P Q V := inferInstance

private theorem cachedGradedRight {C : Type u} [SmallCategory C]
    {J : GrothendieckTopology C} (R : Sheaf J CommRingCat.{u})
    (P Q V : GradedObject ℤ (Modules R)) :
    GradedObject.HasGoodTensorTensor₂₃ P Q V := inferInstance

end PrivateInstanceProofs

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

end TensorSquare

attribute [local irreducible]
  CategoryTheory.CochainPullback.extensionPullback
  CategoryTheory.CochainPullback.extensionFunctor
  CategoryTheory.CochainPullback.changed
  SheafOfModules.PullbackTensorCanonical.IsNormalized
  CategoryTheory.CochainPullback.kappa

section Coefficients

variable {C D : Type u} [SmallCategory C] [SmallCategory D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  {R : Sheaf J CommRingCat.{u}} {S : Sheaf K CommRingCat.{u}}
  [HasDerivedCategory.{w} (Modules.{u, u, u} R)]
  [HasDerivedCategory.{w} (Modules.{u, u, u} S)]

open SheafOfModules.PullbackTensorCanonical

attribute [local instance high] cachedTensorAdditive cachedTensorAdditiveObj
  cachedTensorLeftZero cachedTensorRightZero cachedGradedTensor cachedGradedFour
  cachedGradedLeft cachedGradedRight totalTensor_exists

omit [HasDerivedCategory.{w} (Modules.{u, u, u} R)] in
private theorem coefficient_resolutions
    (P : CochainPullback.Complex.{u, u, u} R) :
    ∃ (Q : CochainPullback.Complex.{u, u, u} R) (q : Q ⟶ P),
      QuasiIso q ∧ Q.IsKFlatIndependentCoefficients ∧
        ∀ n : ℤ, SheafOfModules.IsFlatOnSite (J := J) (R := R) (Q.X n) := by
  obtain ⟨Q, q, hk, hf, hq, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients P
  refine ⟨Q, q, hq, hk, ?_⟩
  intro n
  unfold SheafOfModules.IsFlatOnSite
  exact (exactFunctor _ _).prop_of_iso
    (SheafOfModules.siteSheafTensorRightIso R (Q.X n)).symm (hf n)

omit [HasDerivedCategory.{w} (Modules.{u, u, u} R)]
  [HasDerivedCategory.{w} (Modules.{u, u, u} S)] in
private theorem coefficient_pull_resolving
    (f : RingedPullback.{u, u, u, u, u} R S)
    (P : CochainPullback.Complex.{u, u, u} R)
    (hp : P.IsKFlatIndependentCoefficients)
    (hf : ∀ n : ℤ, SheafOfModules.IsFlatOnSite (J := J) (R := R) (P.X n)) :
    CochainComplex.IsKFlatIndependentCoefficients ((CochainPullback.pull f).obj P) ∧
      ∀ n : ℤ, SheafOfModules.IsFlatOnSite (J := K) (R := S)
        (((CochainPullback.pull f).obj P).X n) := by
  let := f.finiteLimits
  exact SheafOfModules.isKFlat_ringedToposPullback f.uInv f.uPush f.adj f.I
    f.coefficient f.L f.hobj f.hmap P hp hf

private theorem coefficient_computes
    (f : RingedPullback.{u, u, u, u, u} R S) (d : DerivedCategory (Modules.{u, u, u} R) ⥤
      DerivedCategory (Modules.{u, u, u} S))
    (e : DerivedCategory.Q.{w} ⋙ d ⟶
      CochainPullback.pull.{u, u, u, u, u} f ⋙ DerivedCategory.Q.{w})
    (hd : d.IsLeftDerivedFunctor e
      (HomologicalComplex.quasiIso (Modules.{u, u, u} R) (.up ℤ)))
    (P : CochainPullback.Complex.{u, u, u} R)
    (hp : P.IsKFlatIndependentCoefficients)
    (hf : ∀ n : ℤ, SheafOfModules.IsFlatOnSite (J := J) (R := R) (P.X n)) :
    IsIso (e.app P) :=
  SheafOfModules.PullbackTensorResolving.pullback_resolving_computation
    f d e hd P hp hf

private theorem coefficient_normalization
    (f : RingedPullback.{u, u, u, u, u} R S)
    (k : CochainPullback.Comparison.{u, u, u, u, u} f) (d : DerivedCategory (Modules.{u, u, u} R) ⥤
      DerivedCategory (Modules.{u, u, u} S))
    (e : DerivedCategory.Q.{w} ⋙ d ⟶
      CochainPullback.pull.{u, u, u, u, u} f ⋙ DerivedCategory.Q.{w})
    (hd : d.IsLeftDerivedFunctor e
      (HomologicalComplex.quasiIso (Modules.{u, u, u} R) (.up ℤ))) :
    (∃ s : (SheafOfModules.KFlatFixedTensor.derivedTensor S).CommShift₂Int,
      letI := s; HasCanonicalTensorShifts (R := S)) ∧
    ∃ nu : Phi.{u, u, u, u, u, w, w} d ≅ Psi.{u, u, u, u, u, w, w} d,
      IsNormalized f k d e nu.hom := by
  obtain ⟨_, _, s, _, _, hc, _, nu, hn, _⟩ :=
    pullback_tensor_canonical_shift_unit f k d e hd
  exact ⟨⟨s, hc⟩, nu, hn⟩

private theorem coefficient_tensor_resolving
    (P Q : CochainPullback.Complex.{u, u, u} R)
    (hp : P.IsKFlatIndependentCoefficients) (hq : Q.IsKFlatIndependentCoefficients)
    (hf : ∀ n : ℤ, SheafOfModules.IsFlatOnSite (J := J) (R := R) (P.X n))
    (hg : ∀ n : ℤ, SheafOfModules.IsFlatOnSite (J := J) (R := R) (Q.X n)) :
    CochainComplex.IsKFlatIndependentCoefficients (P ⊗ Q) ∧
      ∀ n : ℤ, SheafOfModules.IsFlatOnSite (J := J) (R := R) ((P ⊗ Q).X n) := by
  have h := SheafOfModules.KFlatTotalTensorModel.kFlat_total_tensor_model
    R P Q hp hq hf hg
  exact ⟨h.1, h.2.1⟩

private theorem coefficient_model_square
    (f : RingedPullback.{u, u, u, u, u} R S)
    (k : CochainPullback.Comparison.{u, u, u, u, u} f) (d : DerivedCategory (Modules.{u, u, u} R) ⥤
      DerivedCategory (Modules.{u, u, u} S))
    (e : DerivedCategory.Q.{w} ⋙ d ⟶
      CochainPullback.pull.{u, u, u, u, u} f ⋙ DerivedCategory.Q.{w})
    (nu : Phi.{u, u, u, u, u, w, w} d ≅ Psi.{u, u, u, u, u, w, w} d)
    (hn : IsNormalized f k d e nu.hom)
    (P Q : CochainPullback.Complex.{u, u, u} R)
    (hP : P.IsKFlatIndependentCoefficients ∧
      ∀ n : ℤ, SheafOfModules.IsFlatOnSite (J := J) (R := R) (P.X n))
    (hQ : Q.IsKFlatIndependentCoefficients ∧
      ∀ n : ℤ, SheafOfModules.IsFlatOnSite (J := J) (R := R) (Q.X n)) :
    d.map (canonicalRepresentativeIso R P Q hP.1 hQ.1 hP.2 hQ.2).hom ≫
        nu.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫
        (Functor.uncurry.obj (canonicalDerivedTensor S)).map
          (Prod.mkHom (e.app P) (e.app Q)) =
      e.app (P ⊗ Q) ≫
        DerivedCategory.Q.map (CochainPullback.comparison f k P Q).hom ≫
        (canonicalRepresentativeIso S _ _
          (coefficient_pull_resolving f P hP.1 hP.2).1
          (coefficient_pull_resolving f Q hQ.1 hQ.2).1
          (coefficient_pull_resolving f P hP.1 hP.2).2
          (coefficient_pull_resolving f Q hQ.1 hQ.2).2).hom := by
  unfold IsNormalized at hn
  obtain ⟨_, _, _, _, he⟩ := hn P Q hP.1 hQ.1 hP.2 hQ.2
  exact he

private theorem coefficient_model_naturality
    (hs : ∃ s : (SheafOfModules.KFlatFixedTensor.derivedTensor R).CommShift₂Int,
      letI := s; HasCanonicalTensorShifts (R := R))
    (P Q P' Q' : CochainPullback.Complex.{u, u, u} R)
    (hP : P.IsKFlatIndependentCoefficients ∧
      ∀ n : ℤ, SheafOfModules.IsFlatOnSite (J := J) (R := R) (P.X n))
    (hQ : Q.IsKFlatIndependentCoefficients ∧
      ∀ n : ℤ, SheafOfModules.IsFlatOnSite (J := J) (R := R) (Q.X n))
    (hP' : P'.IsKFlatIndependentCoefficients ∧
      ∀ n : ℤ, SheafOfModules.IsFlatOnSite (J := J) (R := R) (P'.X n))
    (hQ' : Q'.IsKFlatIndependentCoefficients ∧
      ∀ n : ℤ, SheafOfModules.IsFlatOnSite (J := J) (R := R) (Q'.X n))
    (a : P ⟶ P') (b : Q ⟶ Q') :
    DerivedCategory.Q.map (HomologicalComplex.tensorHom a b) ≫
        (canonicalRepresentativeIso R P' Q' hP'.1 hQ'.1 hP'.2 hQ'.2).hom =
      (canonicalRepresentativeIso R P Q hP.1 hQ.1 hP.2 hQ.2).hom ≫
        (Functor.uncurry.obj (canonicalDerivedTensor R)).map
          (Prod.mkHom (DerivedCategory.Q.map a) (DerivedCategory.Q.map b)) := by
  obtain ⟨s, hc⟩ := hs
  let := s
  have he := canonicalRepresentativeIso_naturality hc P Q P' Q'
    hP.1 hQ.1 hP'.1 hQ'.1 hP.2 hQ.2 hP'.2 hQ'.2 a b
  have : ∀ P Q : CochainPullback.Complex.{u, u, u} R,
      HomologicalComplex.HasMapBifunctor P Q (curriedTensor (Modules R)) (.up ℤ) :=
    totalTensor_exists R
  have hh : (((SheafOfModules.KFlatFixedTensor.totalTensor R).map a).app Q ≫
      ((SheafOfModules.KFlatFixedTensor.totalTensor R).obj P').map b) =
        HomologicalComplex.tensorHom a b := by
    change HomologicalComplex.mapBifunctorMap a (𝟙 Q) _ _ ≫
      HomologicalComplex.mapBifunctorMap (𝟙 P') b _ _ =
      HomologicalComplex.mapBifunctorMap a b _ _
    simp only [HomologicalComplex.mapBifunctorMap, Functor.map_id, NatTrans.id_app,
      Category.comp_id, Category.id_comp, ← HomologicalComplex₂.total.map_comp]
  rw [hh] at he
  exact he

set_option maxHeartbeats 800000 in
-- The four cochain and derived tensor presentations are checked simultaneously.
/-- Simultaneous coefficient square, normalized by all four tensor representative
squares and by the ordinary balanced scalar-association map. The four tensors here
are the fixed published tensors `canonicalDerivedTensor`, an equivalent presentation
of the site tensor used above. No coefficient map is required to be flat.
Source: Stacks 07A4, 0G7E, and the balanced coefficient square of the DAG
(blueprint: lem-pur-normalized-coefficient-tensor-square).

Proof: regard both coefficient extensions as identity-topos ringed pullbacks.
By lem-trf-ringed-kflat-word-comparison-descent, a single flat-term K-flat
representative computes every intermediate scalar and pullback word, including
nonflat quotient changes. Descend the specified scalarAssociation, which is
uniquely fixed on generalized scalar-extension generators. Its normalization is
the displayed counit equation. Apply the representative normalization to the
four edges. On a common pair P,Q, the two routes are the first coefficient
equation of lem-pur-cochain-pullback-tensor-coherence: starting with
s' tensor ((x tensor y) tensor r), both give
((1 tensor x) tensor s' phi'(r)) tensor ((1 tensor y) tensor 1).
Insert all four representative maps and cancel adjacent computation inverses.
Fully faithful two-variable tensor descent proves the square on all unbounded
derived inputs. Unary descent gives uniqueness of kappa from its normalization;
the four tensor comparisons are likewise the uniquely normalized comparisons. -/
theorem normalizedCoefficientTensorSquare
    (f : RingedPullback.{u, u, u, u, u} R S) (k : CochainPullback.Comparison.{u, u, u, u, u} f)
    (a : CochainPullback.CoefficientSquare.{u, u, u, u, u} f) (k' : CochainPullback.Comparison.{u,
      u, u, u, u} (CochainPullback.changed.{u, u, u, u, u} f a))
    [HasDerivedCategory.{w} (Modules.{u, u, u} a.R')]
    [HasDerivedCategory.{w} (Modules.{u, u, u} a.S')]
    (df : DerivedCategory (Modules.{u, u, u} R) ⥤
      DerivedCategory (Modules.{u, u, u} S))
    (df' : DerivedCategory (Modules.{u, u, u} a.R') ⥤
      DerivedCategory (Modules.{u, u, u} a.S'))
    (dR : DerivedCategory (Modules.{u, u, u} R) ⥤
      DerivedCategory (Modules.{u, u, u} a.R'))
    (dS : DerivedCategory (Modules.{u, u, u} S) ⥤
      DerivedCategory (Modules.{u, u, u} a.S'))
    (ef : DerivedCategory.Q.{w} ⋙ df ⟶
      CochainPullback.pull.{u, u, u, u, u} f ⋙ DerivedCategory.Q.{w})
    (ef' : DerivedCategory.Q.{w} ⋙ df' ⟶
      CochainPullback.pull.{u, u, u, u, u} (CochainPullback.changed f a) ⋙
        DerivedCategory.Q.{w})
    (eR : DerivedCategory.Q.{w} ⋙ dR ⟶ extend.{u, u, u} a.sourceMap ⋙ DerivedCategory.Q.{w})
    (eS : DerivedCategory.Q.{w} ⋙ dS ⟶ extend.{u, u, u} a.targetMap ⋙ DerivedCategory.Q.{w})
    (hdf : df.IsLeftDerivedFunctor ef
      (HomologicalComplex.quasiIso (Modules.{u, u, u} R) (.up ℤ)))
    (hdf' : df'.IsLeftDerivedFunctor ef'
      (HomologicalComplex.quasiIso (Modules.{u, u, u} a.R') (.up ℤ)))
    (hdR : dR.IsLeftDerivedFunctor eR
      (HomologicalComplex.quasiIso (Modules.{u, u, u} R) (.up ℤ)))
    (hdS : dS.IsLeftDerivedFunctor eS
      (HomologicalComplex.quasiIso (Modules.{u, u, u} S) (.up ℤ))) :
    ∃ (nu : Phi.{u, u, u, u, u, w, w} (R := R) (S := S) df ≅ Psi.{u, u, u, u, u, w, w} (R := R)
        (S := S) df)
      (nu' : Phi.{u, u, u, u, u, w, w} (R := a.R') (S := a.S') df' ≅ Psi.{u, u, u, u, u, w, w}
        (R := a.R') (S := a.S') df')
      (epsR : Phi.{u, u, u, u, u, w, w} (R := R) (S := a.R') dR ≅ Psi.{u, u, u, u, u, w, w} (R
        := R) (S := a.R') dR)
      (epsS : Phi.{u, u, u, u, u, w, w} (R := S) (S := a.S') dS ≅ Psi.{u, u, u, u, u, w, w} (R
        := S) (S := a.S') dS)
      (b : dR ⋙ df' ≅ df ⋙ dS),
      IsNormalized.{u, u, u, u, u, w, w} (R := R) (S := S) f k df ef nu.hom ∧
      IsNormalized.{u, u, u, u, u, w, w} (R := a.R') (S := a.S')
        (CochainPullback.changed.{u, u, u, u, u} f a) k' df' ef' nu'.hom ∧
      IsNormalized.{u, u, u, u, u, w, w} (R := R) (S := a.R') (extensionPullback.{u, u, u}
          a.sourceMap)
        (extensionComparison.{u, u, u} a.sourceMap)
        dR eR epsR.hom ∧
      IsNormalized.{u, u, u, u, u, w, w} (R := S) (S := a.S') (extensionPullback.{u, u, u}
          a.targetMap)
        (extensionComparison.{u, u, u} a.targetMap)
        dS eS epsS.hom ∧
      (∀ (P : CochainPullback.Complex.{u, u, u} R), P.IsKFlatIndependentCoefficients →
        (∀ n : ℤ, SheafOfModules.IsFlatOnSite (J := J) (R := R) (P.X n)) →
        b.hom.app ((DerivedCategory.Q.{w} (C := Modules.{u, u, u} R)).obj P) ≫ dS.map
        (ef.app P) ≫
            eS.app ((CochainPullback.pull.{u, u, u, u, u} f).obj P) =
          df'.map (eR.app P) ≫ ef'.app ((extend.{u, u, u} a.sourceMap).obj P) ≫
            (DerivedCategory.Q.{w} (C := Modules.{u, u, u} a.S')).map (CochainPullback.kappa.{u,
          u, u,
        u, u} f k a k' P).hom) ∧
      (∀ M N : DerivedCategory (Modules.{u, u, u} R),
        df'.map (epsR.hom.app (M, N)) ≫
            nu'.hom.app (dR.obj M, dR.obj N) ≫
            (Functor.uncurry.obj (canonicalDerivedTensor.{u, u, u, w} a.S')).map
              (Prod.mkHom (b.hom.app M) (b.hom.app N)) =
          b.hom.app (((canonicalDerivedTensor.{u, u, u, w} R).obj M).obj N) ≫
            dS.map (nu.hom.app (M, N)) ≫
            epsS.hom.app (df.obj M, df.obj N)) ∧
      (∀ b' : dR ⋙ df' ≅ df ⋙ dS,
        (∀ (P : CochainPullback.Complex.{u, u, u} R), P.IsKFlatIndependentCoefficients →
          (∀ n : ℤ, SheafOfModules.IsFlatOnSite (J := J) (R := R) (P.X n)) →
          b'.hom.app ((DerivedCategory.Q.{w} (C := Modules.{u, u, u} R)).obj P) ≫ dS.map
        (ef.app P) ≫
              eS.app ((CochainPullback.pull.{u, u, u, u, u} f).obj P) =
            df'.map (eR.app P) ≫ ef'.app ((extend.{u, u, u} a.sourceMap).obj P) ≫
              (DerivedCategory.Q.{w} (C := Modules.{u, u, u} a.S')).map
          (CochainPullback.kappa.{u, u,
        u, u, u} f k a k' P).hom) → b' =
                b) := by
  obtain ⟨_, nu, hn⟩ := coefficient_normalization f k df ef hdf
  obtain ⟨hcS', nu', hn'⟩ := coefficient_normalization (CochainPullback.changed f a) k' df' ef' hdf'
  obtain ⟨_, epsR, hR⟩ := coefficient_normalization (extensionPullback a.sourceMap)
    (extensionComparison a.sourceMap) dR eR hdR
  obtain ⟨_, epsS, hS⟩ := coefficient_normalization (extensionPullback a.targetMap)
    (extensionComparison a.targetMap) dS eS hdS
  let U := extend.{u, u, u} a.sourceMap
  let V := CochainPullback.pull.{u, u, u, u, u} (CochainPullback.changed f a)
  let W := CochainPullback.pull.{u, u, u, u, u} f
  let T := extend.{u, u, u} a.targetMap
  let eL : DerivedCategory.Q ⋙ (dR ⋙ df') ⟶ (U ⋙ V) ⋙ DerivedCategory.Q :=
    Functor.whiskerRight eR df' ≫ Functor.whiskerLeft U ef'
  let eRight : DerivedCategory.Q ⋙ (df ⋙ dS) ⟶ (W ⋙ T) ⋙ DerivedCategory.Q :=
    Functor.whiskerRight ef dS ≫ Functor.whiskerLeft W eS
  let c : U ⋙ V ≅ W ⋙ T :=
    NatIso.ofComponents (CochainPullback.kappa.{u, u, u, u, u} f k a k') (by
      intro P Q r
      ext n : 1
      with_unfolding_all exact (scalarAssociation f k a k').hom.naturality (r.f n))
  have heL (P : CochainPullback.Complex.{u, u, u} R) (hp : P.IsKFlatIndependentCoefficients)
      (hf : ∀ n : ℤ, SheafOfModules.IsFlatOnSite (J := J) (R := R) (P.X n)) :
      IsIso (eL.app P) := by
    have := coefficient_computes (extensionPullback a.sourceMap) dR eR hdR P hp hf
    obtain ⟨hp', hf'⟩ := coefficient_pull_resolving (extensionPullback a.sourceMap) P hp hf
    have := coefficient_computes (CochainPullback.changed f a) df' ef' hdf' (U.obj P) hp' hf'
    change IsIso (df'.map (eR.app P) ≫ ef'.app (U.obj P))
    infer_instance
  have heR (P : CochainPullback.Complex.{u, u, u} R) (hp : P.IsKFlatIndependentCoefficients)
      (hf : ∀ n : ℤ, SheafOfModules.IsFlatOnSite (J := J) (R := R) (P.X n)) :
      IsIso (eRight.app P) := by
    have := coefficient_computes f df ef hdf P hp hf
    obtain ⟨hp', hf'⟩ := coefficient_pull_resolving f P hp hf
    have := coefficient_computes (extensionPullback a.targetMap) dS eS hdS (W.obj P) hp' hf'
    change IsIso (dS.map (ef.app P) ≫ eS.app (W.obj P))
    infer_instance
  obtain ⟨b, hb, hu⟩ := RingedKFlatWord.comparison_descent_iso
    (fun P : CochainPullback.Complex.{u, u, u} R ↦
      P.IsKFlatIndependentCoefficients ∧
        ∀ n : ℤ, SheafOfModules.IsFlatOnSite (J := J) (R := R) (P.X n))
    coefficient_resolutions (dR ⋙ df') (df ⋙ dS)
    ((U ⋙ V) ⋙ DerivedCategory.Q) ((W ⋙ T) ⋙ DerivedCategory.Q)
    eL eRight (fun P hP ↦ heL P hP.1 hP.2) (fun P hP ↦ heR P hP.1 hP.2)
    (isoWhiskerRight c DerivedCategory.Q)
  have hb' (P : CochainPullback.Complex.{u, u, u} R) hp hf := hb P ⟨hp, hf⟩
  refine ⟨nu, nu', epsR, epsS, b, hn, hn', hR, hS, ?_, ?_, ?_⟩
  · intro P hp hf
    simpa only [eL, eRight, NatTrans.comp_app, whiskerRight_app, whiskerLeft_app,
      isoWhiskerRight_hom, whiskerRight_app, c, NatIso.ofComponents_hom_app, Iso.app_hom,
      Category.assoc] using hb' P hp hf
  · let pR : ObjectProperty (CochainPullback.Complex.{u, u, u} R) := fun P ↦
      P.IsKFlatIndependentCoefficients ∧
        ∀ n : ℤ, SheafOfModules.IsFlatOnSite (J := J) (R := R) (P.X n)
    let pR' : ObjectProperty (CochainPullback.Complex.{u, u, u} a.R') := fun P ↦
      P.IsKFlatIndependentCoefficients ∧
        ∀ n : ℤ, SheafOfModules.IsFlatOnSite (J := J) (R := a.R') (P.X n)
    let pS : ObjectProperty (CochainPullback.Complex.{u, u, u} S) := fun P ↦
      P.IsKFlatIndependentCoefficients ∧
        ∀ n : ℤ, SheafOfModules.IsFlatOnSite (J := K) (R := S) (P.X n)
    let pS' : ObjectProperty (CochainPullback.Complex.{u, u, u} a.S') := fun P ↦
      P.IsKFlatIndependentCoefficients ∧
        ∀ n : ℤ, SheafOfModules.IsFlatOnSite (J := K) (R := a.S') (P.X n)
    let hU P (hP : pR P) : pR' (U.obj P) :=
      coefficient_pull_resolving (extensionPullback a.sourceMap) P hP.1 hP.2
    let hV P (hP : pR' P) : pS' (V.obj P) :=
      coefficient_pull_resolving (CochainPullback.changed f a) P hP.1 hP.2
    let hW P (hP : pR P) : pS (W.obj P) :=
      coefficient_pull_resolving f P hP.1 hP.2
    let hT P (hP : pS P) : pS' (T.obj P) :=
      coefficient_pull_resolving (extensionPullback a.targetMap) P hP.1 hP.2
    let rR P Q (hP : pR P) (hQ : pR Q) :=
      canonicalRepresentativeIso R P Q hP.1 hQ.1 hP.2 hQ.2
    let rR' P Q (hP : pR' P) (hQ : pR' Q) :=
      canonicalRepresentativeIso a.R' P Q hP.1 hQ.1 hP.2 hQ.2
    let rS P Q (hP : pS P) (hQ : pS Q) :=
      canonicalRepresentativeIso S P Q hP.1 hQ.1 hP.2 hQ.2
    let rS' P Q (hP : pS' P) (hQ : pS' Q) :=
      canonicalRepresentativeIso a.S' P Q hP.1 hQ.1 hP.2 hQ.2
    let TR := Functor.uncurry.obj (canonicalDerivedTensor.{u, u, u, w} R)
    let TR' := Functor.uncurry.obj (canonicalDerivedTensor.{u, u, u, w} a.R')
    let TS := Functor.uncurry.obj (canonicalDerivedTensor.{u, u, u, w} S)
    let TS' := Functor.uncurry.obj (canonicalDerivedTensor.{u, u, u, w} a.S')
    let nL := composite_comparison TR TR' TS' dR df' epsR.hom nu'.hom
    let nR := composite_comparison TR TS TS' df dS nu.hom epsS.hom
    let cR P Q := (CochainPullback.comparison (extensionPullback a.sourceMap)
      (extensionComparison a.sourceMap) P Q).hom
    let cV P Q := (CochainPullback.comparison (CochainPullback.changed f a) k' P Q).hom
    let cW P Q := (CochainPullback.comparison f k P Q).hom
    let cT P Q := (CochainPullback.comparison (extensionPullback a.targetMap)
      (extensionComparison a.targetMap) P Q).hom
    let bL P Q := V.map (cR P Q) ≫ cV (U.obj P) (U.obj Q)
    let bR P Q := T.map (cW P Q) ≫ cT (W.obj P) (W.obj Q)
    obtain ⟨ff⟩ := derivedResolvingPairRestriction (DerivedCategory (Modules.{u, u, u} a.S'))
      pR (fun K ↦ by
        obtain ⟨P, p, hp, hP⟩ := coefficient_resolutions K
        exact ⟨P, p, hP, hp⟩)
    have hs : nL ≫ Functor.whiskerRight (NatTrans.prod b.hom b.hom) TS' =
        Functor.whiskerLeft TR b.hom ≫ nR := by
      apply ff.map_injective
      ext ⟨⟨P, hP⟩, ⟨Q, hQ⟩⟩
      have := heR P hP.1 hP.2
      have := heR Q hQ.1 hQ.2
      apply normalized_tensor_square DerivedCategory.Q DerivedCategory.Q
        (fun P Q ↦ HomologicalComplex.tensorObj P Q)
        (fun P Q ↦ HomologicalComplex.tensorObj P Q)
        TR TS' (U ⋙ V) (W ⋙ T) (dR ⋙ df') (df ⋙ dS) eL eRight nL nR bL bR
        b.hom c.hom P Q (HomologicalComplex.tensorHom (c.hom.app P) (c.hom.app Q))
        (rR P Q hP hQ)
        (rS' _ _ (hV _ (hU P hP)) (hV _ (hU Q hQ)))
        (rS' _ _ (hT _ (hW P hP)) (hT _ (hW Q hQ)))
      · exact composite_tensor_square DerivedCategory.Q DerivedCategory.Q DerivedCategory.Q
          (fun P Q ↦ HomologicalComplex.tensorObj P Q)
          (fun P Q ↦ HomologicalComplex.tensorObj P Q)
          (fun P Q ↦ HomologicalComplex.tensorObj P Q)
          TR TR' TS' U V dR df' eR ef' epsR.hom nu'.hom
          cR cV P Q (rR P Q hP hQ) (rR' _ _ (hU P hP) (hU Q hQ))
          (rS' _ _ (hV _ (hU P hP)) (hV _ (hU Q hQ)))
          (coefficient_model_square _ _ dR eR epsR hR P Q hP hQ)
          (coefficient_model_square _ _ df' ef' nu' hn' _ _ (hU P hP) (hU Q hQ))
      · exact composite_tensor_square DerivedCategory.Q DerivedCategory.Q DerivedCategory.Q
          (fun P Q ↦ HomologicalComplex.tensorObj P Q)
          (fun P Q ↦ HomologicalComplex.tensorObj P Q)
          (fun P Q ↦ HomologicalComplex.tensorObj P Q)
          TR TS TS' W T df dS ef eS nu.hom epsS.hom
          cW cT P Q (rR P Q hP hQ) (rS _ _ (hW P hP) (hW Q hQ))
          (rS' _ _ (hT _ (hW P hP)) (hT _ (hW Q hQ)))
          (coefficient_model_square _ _ df ef nu hn P Q hP hQ)
          (coefficient_model_square _ _ dS eS epsS hS _ _ (hW P hP) (hW Q hQ))
      · exact hb P hP
      · exact hb Q hQ
      · exact hb _ (coefficient_tensor_resolving P Q hP.1 hQ.1 hP.2 hQ.2)
      · have hh :=
          ((CochainPullback.cochainPullbackTensorCoherence.{u, u, u, u, u, u, u}
            f k).2.2 a k').1 P Q
        with_unfolding_all exact hh
      · exact coefficient_model_naturality hcS' _ _ _ _
          (hV _ (hU P hP)) (hV _ (hU Q hQ)) (hT _ (hW P hP)) (hT _ (hW Q hQ))
          (c.hom.app P) (c.hom.app Q)
    intro M N
    simpa only [nL, nR, TR, TS', composite_comparison, NatTrans.comp_app, whiskerRight_app,
      whiskerLeft_app, NatTrans.prod, Functor.prod_obj, Functor.comp_obj,
      Functor.uncurry_obj_obj, Category.assoc] using congr_app hs (M, N)
  · intro b' hb'
    apply hu b'
    intro P hP
    simpa only [eL, eRight, NatTrans.comp_app, whiskerRight_app, whiskerLeft_app,
      isoWhiskerRight_hom, whiskerRight_app, c, NatIso.ofComponents_hom_app, Iso.app_hom,
      Category.assoc] using hb' P hP.1 hP.2

end Coefficients

end CategoryTheory.NormalizedCoefficientTensor

attribute [instance high] CategoryTheory.hasSheafCompose_of_preservesMulticospan
