/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.AdicQbarRealization.Proper.NativePullbackFiniteTensorDescent
import WeilConjectures.SixFunctors.IntegralOrdinary.IntegralTensorPullbackAugmentation
import WeilConjectures.PoincareDuality.StrictTensorAugmentation.StrictTensorAugmentationNormalization
import WeilConjectures.SixFunctors.ConstructibleTensorModel.ConstructibleTensorCompletionCoordinates
import WeilConjectures.Algebra.Homology.CochainTensorModelRigidity
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.Localization.Construction
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.CategoryTheory.Functor.Currying
import Mathlib.CategoryTheory.Whiskering
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.CategoryTheory.Localization.Prod
import Mathlib.Algebra.Homology.BifunctorFlip
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorHomotopy
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
import Mathlib.CategoryTheory.Localization.CalculusOfFractions
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import WeilConjectures.SixFunctors.AdicQbarRealization.Proper.NativePullbackScalarTensorChain
import all WeilConjectures.SixFunctors.IntegralOrdinary.IntegralPullbackComplexIdentification
import WeilConjectures.SixFunctors.LocallyFiniteAdicRealization.NativeIntegralCoefficientFlat
import WeilConjectures.SixFunctors.AdicQbarRealization.Proper.NativePullbackCoefficientMap
import WeilConjectures.SixFunctors.AdicQbarRealization.Proper.NativePullbackExactCounits
import all WeilConjectures.SixFunctors.PurCompactSupport.ScalarPullTensorCoefficientCoherence
import all WeilConjectures.SixFunctors.AdicQbarRealization.AdicOrdinaryScalarTensorReindexing

/-! # The native completed integral tensor square

Source: Bhatt--Scholze, Proposition 6.8.14 and Remark 6.8.15.
(blueprint: lem-sf-native-pullback-finite-tensor-coherence)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.AdicQbarRealization.Proper
attribute [local irreducible] HasDerivedCategory.standard
  SheafOfModules.monoidalCategory ContinuousRational.modulePull ordinaryIntegralModulePull
  Functor.mapDerivedCategory proEtaleRingDerivedPullbackFactors
attribute [local implicit_reducible] WeilConjectures.PurCompactSupport.completed
  WeilConjectures.completedIntegralCommRingSheafUnrestricted
attribute [local implicit_reducible] CategoryTheory.Functor.map₂HomologicalComplex
  CategoryTheory.Functor.mapHomologicalComplex
set_option backward.defeqAttrib.useBackward true

section Presentation
variable (l : ℕ) [Fact l.Prime] (k : Type u) [Field k]
  [Algebra (Padic l) k] [FiniteDimensional (Padic l) k] (X : Scheme.{u})

private def ordinaryPresentationComparison
    (N : ConstructibleTensorCompletionPresentation l k X) :
    N.tensor ≅ (IntegralOrdinary.tensorModel l k X).tensor := by
  let q := integralOperationsGoodLocalization l k X
  let T := (Functor.whiskeringLeft _ _
    (DerivedCategory (integralTowerModules l k X))).obj (q.prod q)
  let h := (SheafOfModules.cochain_tensor_model_rigidity (ProEt.topology X)
    (completedIntegralCommRingSheafUnrestricted l k X)).choose_spec.2.2
  let ff : T.FullyFaithful :=
    ((Functor.FullyFaithful.nonempty_iff_map_bijective T).2
      (fun U V ↦ h _ inferInstance U V)).some
  exact ff.preimageIso
    (N.model.symm ≪≫ ConstructibleTensorModel.tensorRepresentativeIso l k X)

private theorem ordinaryPresentation_model
    (N : ConstructibleTensorCompletionPresentation l k X)
    (P Q : (integralOperationsGoodComplex l k X).FullSubcategory) :
    N.model.hom.app (P, Q) ≫ (ordinaryPresentationComparison l k X N).hom.app
        (DerivedCategory.Q.obj P.obj, DerivedCategory.Q.obj Q.obj) =
      (ConstructibleTensorModel.tensorRepresentativeIso l k X).hom.app (P, Q) := by
  let q := integralOperationsGoodLocalization l k X
  let T := (Functor.whiskeringLeft _ _
    (DerivedCategory (integralTowerModules l k X))).obj (q.prod q)
  let h := (SheafOfModules.cochain_tensor_model_rigidity (ProEt.topology X)
    (completedIntegralCommRingSheafUnrestricted l k X)).choose_spec.2.2
  let ff : T.FullyFaithful :=
    ((Functor.FullyFaithful.nonempty_iff_map_bijective T).2
      (fun U V ↦ h _ inferInstance U V)).some
  have he : T.map (ordinaryPresentationComparison l k X N).hom =
      (N.model.symm ≪≫ ConstructibleTensorModel.tensorRepresentativeIso l k X).hom := by
    unfold ordinaryPresentationComparison
    exact ff.map_preimage _
  have ht := congrArg (fun τ ↦ τ.app (P, Q)) he
  change (ordinaryPresentationComparison l k X N).hom.app
    (DerivedCategory.Q.obj P.obj, DerivedCategory.Q.obj Q.obj) =
      N.model.inv.app (P, Q) ≫
        (ConstructibleTensorModel.tensorRepresentativeIso l k X).hom.app (P, Q) at ht
  rw [ht, Iso.hom_inv_id_app_assoc]

private def ordinaryPresentationCompletion
    (N : ConstructibleTensorCompletionPresentation l k X) :
    (IntegralOrdinary.tensorModel l k X).tensor ⟶ integralCompletedTensor l k X :=
  (ordinaryPresentationComparison l k X N).inv ≫ N.comparison

private theorem ordinaryPresentation_chain
    (N : ConstructibleTensorCompletionPresentation l k X) :
    N.cochain = ConstructibleTensorModel.tensorCompletionChain l k X := by
  apply (StrictTensorAugmentation.existsUnique_normalized l k X).unique
  · exact ⟨N.normalized.1, fun P Q i ↦ N.normalized.2.1 P Q i (i - 1) (by omega)⟩
  · exact ⟨ConstructibleTensorModel.tensorChain_first l k X,
      fun P Q i ↦ ConstructibleTensorModel.tensorChain_second l k X P Q i (i - 1)
        (by omega)⟩

private theorem ordinaryPresentation_normalized
    (N : ConstructibleTensorCompletionPresentation l k X) :
    IntegralOrdinary.TensorAugmentationNormalized l k X
      (ordinaryPresentationCompletion l k X N) := by
  intro P Q
  rw [← ordinaryPresentation_model l k X N P Q]
  simp only [ordinaryPresentationCompletion, NatTrans.comp_app, Category.assoc,
    Iso.hom_inv_id_app_assoc]
  rw [N.normalized.2.2.1 P Q, ordinaryPresentation_chain l k X N]

end Presentation

private def ordinaryPresentationScalar (l : ℕ) [Fact l.Prime] (X : Scheme.{u})
    (R : LocallyFiniteAdicRealization.Realization l X)
    [∀ x : X, Invertible (l : X.residueField x)] (A : At l X R)
    (E : AlgebraicallyClosedCoefficients.Index l (PadicAlgCl l))
    (N : FiniteNormalization l X R A E) :
    (IntegralOrdinary.tensorModel l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) X).tensor ⋙
        pbcDerivedExtend (coefficientMap l X R E) ≅
      (pbcDerivedExtend (coefficientMap l X R E)).prod
        (pbcDerivedExtend (coefficientMap l X R E)) ⋙ A.closed.tensor :=
  Functor.isoWhiskerRight (ordinaryPresentationComparison l _ X N.completion).symm
    (pbcDerivedExtend (coefficientMap l X R E)) ≪≫ N.ordinary

private theorem ordinaryPresentation_factor (l : ℕ) [Fact l.Prime] (X : Scheme.{u})
    (R : LocallyFiniteAdicRealization.Realization l X)
    [∀ x : X, Invertible (l : X.residueField x)] (A : At l X R)
    (E : AlgebraicallyClosedCoefficients.Index l (PadicAlgCl l))
    (N : FiniteNormalization l X R A E)
    (K L : sfIntegralConstructibleCategory l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) X) :
    finiteIntegralTensorMap l X R A E N K L =
      (ordinaryPresentationScalar l X R A E N).inv.app (K.obj, L.obj) ≫
        (pbcDerivedExtend (coefficientMap l X R E)).map
          ((ordinaryPresentationCompletion l _ X N.completion).app (K.obj, L.obj)) := by
  simp only [finiteIntegralTensorMap, ordinaryPresentationScalar, Iso.trans_inv,
    NatTrans.comp_app, Functor.isoWhiskerRight_inv, Functor.whiskerRight_app,
    Iso.symm_inv, ordinaryPresentationCompletion, Functor.map_comp, Category.assoc,
    ← Functor.map_comp_assoc, Iso.hom_inv_id_app]
  erw [CategoryTheory.Functor.map_id, Category.id_comp]

private def nativeOrdinaryBalance (l : ℕ) [Fact l.Prime]
    {X Y : Scheme.{u}} (p : X ⟶ Y)
    (R : LocallyFiniteAdicRealization.Realization l X)
    (S : LocallyFiniteAdicRealization.Realization l Y)
    (O : Operations l p R S)
    (E : AlgebraicallyClosedCoefficients.Index l (PadicAlgCl l))
    (I : IntegralComparison l p R S O E) :
    pbcDerivedExtend (coefficientMap l Y S E) ⋙
        ContinuousRational.derivedPull p O.coefficient ≅
      PurCompactSupport.pull (PurCompactSupport.completed l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E)) p ⋙
          pbcDerivedExtend (coefficientMap l X R E) :=
  I.derived.symm ≪≫ Functor.isoWhiskerRight (IntegralOrdinary.pullIso l _ p).symm
    (pbcDerivedExtend (coefficientMap l X R E))

private theorem nativePullbackIntegralMap_factor (l : ℕ) [Fact l.Prime]
    {X Y : Scheme.{u}} (p : X ⟶ Y)
    (R : LocallyFiniteAdicRealization.Realization l X)
    (S : LocallyFiniteAdicRealization.Realization l Y)
    (O : Operations l p R S)
    (E : AlgebraicallyClosedCoefficients.Index l (PadicAlgCl l))
    (I : IntegralComparison l p R S O E)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (K : sfIntegralConstructibleCategory l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) Y) :
    nativePullbackIntegralMap l p R S O E I K =
      (nativeOrdinaryBalance l p R S O E I).hom.app K.obj ≫
        (pbcDerivedExtend (coefficientMap l X R E)).map
          ((IntegralOrdinary.pullComparison l _ p).app K.obj) := by
  simp only [nativePullbackIntegralMap, nativeOrdinaryBalance, Iso.trans_hom,
    NatTrans.comp_app, Iso.symm_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, IntegralOrdinary.pullComparison,
    ← Functor.map_comp, Category.assoc, Iso.inv_hom_id_app_assoc, I.completion_hom]

private theorem ordinaryPresentationScalar_representative (l : ℕ) [Fact l.Prime]
    (X : Scheme.{u}) (R : LocallyFiniteAdicRealization.Realization l X)
    [∀ x : X, Invertible (l : X.residueField x)] (A : At l X R)
    (E : AlgebraicallyClosedCoefficients.Index l (PadicAlgCl l))
    (N : FiniteNormalization l X R A E)
    (P Q : (integralOperationsGoodComplex l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) X).FullSubcategory) :
    (pbcDerivedExtend (coefficientMap l X R E)).map
        ((ConstructibleTensorModel.tensorRepresentativeIso l _ X).hom.app (P, Q)) ≫
      (ordinaryPresentationScalar l X R A E N).hom.app
        (DerivedCategory.Q.obj P.obj, DerivedCategory.Q.obj Q.obj) ≫
      A.closed.tensor.map (Prod.mkHom
        (pbcComplexCounit (coefficientMap l X R E) P.obj)
        (pbcComplexCounit (coefficientMap l X R E) Q.obj)) =
    pbcComplexCounit (coefficientMap l X R E)
        ((constructibleTensorTotal l _ X).obj (P.obj, Q.obj)) ≫
      DerivedCategory.Q.map (N.balance.hom.app (P.obj, Q.obj)) ≫
      (A.models.iso _ _ _ _ _ (N.kflat P) (N.kflat Q)).hom := by
  exact model_cancellation (pbcDerivedExtend (coefficientMap l X R E)) _ _
    ((ordinaryPresentationComparison l _ X N.completion).app
      (DerivedCategory.Q.obj P.obj, DerivedCategory.Q.obj Q.obj))
    (N.ordinary.hom.app (DerivedCategory.Q.obj P.obj, DerivedCategory.Q.obj Q.obj)) _ _
    (ordinaryPresentation_model l _ X N.completion P Q) (N.representative P Q)

private theorem nativeOrdinaryBalance_representative (l : ℕ) [Fact l.Prime]
    {X Y : Scheme.{u}} (p : X ⟶ Y)
    (R : LocallyFiniteAdicRealization.Realization l X)
    (S : LocallyFiniteAdicRealization.Realization l Y) (O : Operations l p R S)
    (E : AlgebraicallyClosedCoefficients.Index l (PadicAlgCl l))
    (I : IntegralComparison l p R S O E)
    (Z : CochainComplex (integralTowerModules l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) Y) ℤ) :
    let k := AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E
    let C := PurCompactSupport.completed l k
    let Hc :=
      (proEtaleRingModulePullback p (C.ring Y) (C.ring X) (C.pull p)).mapHomologicalComplex (.up ℤ)
    let EX := pbcDerivedExtend (coefficientMap l X R E)
    let F := ContinuousRational.derivedPull p O.coefficient
    let γ := NatIso.mapHomologicalComplex (nativeModuleBalance l p R S O E I) (.up ℤ)
    (nativeOrdinaryBalance l p R S O E I).inv.app (DerivedCategory.Q.obj Z) ≫
        F.map (pbcComplexCounit (coefficientMap l Y S E) Z) ≫
        O.pullCounit.app ((integralComplex l Y S E).obj Z) =
      EX.map ((proEtaleRingDerivedPullbackFactors p (C.ring Y) (C.ring X) (C.pull p)).hom.app Z) ≫
        pbcComplexCounit (coefficientMap l X R E) (Hc.obj Z) ≫
          DerivedCategory.Q.map (γ.hom.app Z) := by
  intro k C Hc EX F γ
  let b := NatIso.mapHomologicalComplex (IntegralOrdinary.pullbackModuleIso l k p) (.up ℤ)
  let c := NatIso.mapHomologicalComplex I.balance (.up ℤ)
  have hγ : γ.hom.app Z = (integralComplex l X R E).map (b.hom.app Z) ≫ c.hom.app Z := by
    ext n
    rfl
  have hn := (scalar_counit (coefficientMap l X R E)).naturality (b.hom.app Z)
  have he := IntegralOrdinary.pullIso_factor l k p Z
  have hi := I.representative Z
  change (EX.map ((IntegralOrdinary.pullIso l k p).hom.app (DerivedCategory.Q.obj Z)) ≫
      I.derived.hom.app (DerivedCategory.Q.obj Z)) ≫
      F.map (pbcComplexCounit (coefficientMap l Y S E) Z) ≫
      O.pullCounit.app ((integralComplex l Y S E).obj Z) = _
  simp only [Category.assoc]
  calc
    _ = EX.map ((IntegralOrdinary.pullIso l k p).hom.app (DerivedCategory.Q.obj Z)) ≫
        EX.map (ordinaryIntegralPullComplexCounit l k p Z) ≫
        pbcComplexCounit (coefficientMap l X R E)
          ((ordinaryIntegralPullComplex l k p).obj Z) ≫ DerivedCategory.Q.map (c.hom.app Z) := by
      simpa only [Category.assoc] using congrArg
        (fun f ↦ EX.map ((IntegralOrdinary.pullIso l k p).hom.app
          (DerivedCategory.Q.obj Z)) ≫ f) hi
    _ = EX.map ((proEtaleRingDerivedPullbackFactors p (C.ring Y) (C.ring X)
          (C.pull p)).hom.app Z) ≫ EX.map (DerivedCategory.Q.map (b.hom.app Z)) ≫
        pbcComplexCounit (coefficientMap l X R E)
          ((ordinaryIntegralPullComplex l k p).obj Z) ≫ DerivedCategory.Q.map (c.hom.app Z) := by
      simpa only [b, C, NatIso.mapHomologicalComplex,
        Functor.map_comp, Category.assoc] using congrArg
        (fun f ↦ EX.map f ≫ pbcComplexCounit (coefficientMap l X R E)
          ((ordinaryIntegralPullComplex l k p).obj Z) ≫ DerivedCategory.Q.map (c.hom.app Z)) he
    _ = _ := by
      rw [hγ, DerivedCategory.Q.map_comp]
      simpa only [EX, Hc, C, ordinaryIntegralPullComplex, integralComplex,
        scalar_counit, Functor.comp_map, Category.assoc] using congrArg
        (fun f ↦ EX.map ((proEtaleRingDerivedPullbackFactors p (C.ring Y) (C.ring X)
          (C.pull p)).hom.app Z) ≫ f ≫ DerivedCategory.Q.map (c.hom.app Z)) hn

set_option maxHeartbeats 2400000 in
-- Normalize the endpoints of the two composite tensor representative diagrams.
private theorem nativeOrdinaryTensor_good (l : ℕ) [Fact l.Prime]
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y] (p : X ⟶ Y)
    (R : LocallyFiniteAdicRealization.Realization l X)
    (S : LocallyFiniteAdicRealization.Realization l Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (O : Operations l p R S) (A : At l X R) (B : At l Y S)
    (E : AlgebraicallyClosedCoefficients.Index l (PadicAlgCl l))
    (NX : FiniteNormalization l X R A E) (NY : FiniteNormalization l Y S B E)
    (I : IntegralComparison l p R S O E) (W : TensorComparison l p R S O A B)
    (P Q : (integralOperationsGoodComplex l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) Y).FullSubcategory) :
    let k := AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E
    let C := PurCompactSupport.completed l k
    let EX := pbcDerivedExtend (coefficientMap l X R E)
    let EY := pbcDerivedExtend (coefficientMap l Y S E)
    let F := ContinuousRational.derivedPull p O.coefficient
    let H := PurCompactSupport.pull C p
    let T := (IntegralOrdinary.tensorModel l k Y).tensor
    let μ := proEtaleCanonicalTensorComparison p (C.ring Y) (C.ring X) (C.pull p)
      (IntegralOrdinary.tensorModel l k Y) (IntegralOrdinary.tensorModel l k X)
    let v := nativeOrdinaryBalance l p R S O E I
    v.inv.app (T.obj (DerivedCategory.Q.obj P.obj, DerivedCategory.Q.obj Q.obj)) ≫
        F.map ((ordinaryPresentationScalar l Y S B E NY).hom.app
          (DerivedCategory.Q.obj P.obj, DerivedCategory.Q.obj Q.obj)) ≫
        W.tensor.hom.app (EY.obj (DerivedCategory.Q.obj P.obj),
          EY.obj (DerivedCategory.Q.obj Q.obj)) =
      EX.map (μ.hom.app (DerivedCategory.Q.obj P.obj, DerivedCategory.Q.obj Q.obj)) ≫
        (ordinaryPresentationScalar l X R A E NX).hom.app
          (H.obj (DerivedCategory.Q.obj P.obj), H.obj (DerivedCategory.Q.obj Q.obj)) ≫
        A.closed.tensor.map (Prod.mkHom (v.inv.app (DerivedCategory.Q.obj P.obj))
          (v.inv.app (DerivedCategory.Q.obj Q.obj))) := by
  intro k C EX EY F H TY μ v
  let H₀ := proEtaleRingModulePullback p (C.ring Y) (C.ring X) (C.pull p)
  let Hc := H₀.mapHomologicalComplex (.up ℤ)
  let Fc := (ContinuousRational.modulePull p O.coefficient).mapHomologicalComplex (.up ℤ)
  let eX := integralComplex l X R E
  let eY := integralComplex l Y S E
  let cY := constructibleTensorTotal l k Y
  let cX := constructibleTensorTotal l k X
  let tX := coefficientTotalTensor.{u + 1, u + 1, u} (ProEt.topology X) (ring l X R)
  let tY := coefficientTotalTensor.{u + 1, u + 1, u} (ProEt.topology Y) (ring l Y S)
  let TX := (IntegralOrdinary.tensorModel l k X).tensor
  let AX := A.closed.tensor
  let BY := B.closed.tensor
  let δH := proEtaleRingDerivedPullbackFactors p (C.ring Y) (C.ring X) (C.pull p)
  let γ := NatIso.mapHomologicalComplex (nativeModuleBalance l p R S O E I) (.up ℤ)
  let σX := ordinaryPresentationScalar l X R A E NX
  let σY := ordinaryPresentationScalar l Y S B E NY
  have hp : proEtaleFlatRepresentatives Y (C.ring Y) P.obj :=
    ⟨(CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat P.obj).1 P.property.1,
      P.property.2⟩
  have hq : proEtaleFlatRepresentatives Y (C.ring Y) Q.obj :=
    ⟨(CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat Q.obj).1 Q.property.1,
      Q.property.2⟩
  let hμ := (proEtaleCanonicalTensorPullback p (C.ring Y) (C.ring X) (C.pull p)
    (IntegralOrdinary.tensorModel l k Y) (IntegralOrdinary.tensorModel l k X)).2
  obtain ⟨hpH, hqH, hH⟩ := hμ.exists.choose_spec P.obj Q.obj hp hq
  let HP : (integralOperationsGoodComplex l k X).FullSubcategory :=
    ⟨Hc.obj P.obj, ⟨(CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat _).2 hpH.1,
      hpH.2⟩⟩
  let HQ : (integralOperationsGoodComplex l k X).FullSubcategory :=
    ⟨Hc.obj Q.obj, ⟨(CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat _).2 hqH.1,
      hqH.2⟩⟩
  let T := cY.obj (P.obj, Q.obj)
  let J := (proEtaleTensorPullbackTotalIso p (C.ring Y) (C.ring X) (C.pull p)
    P.obj Q.obj).inv
  let rY := (ConstructibleTensorModel.tensorRepresentativeIso l k Y).hom.app (P, Q)
  let rH := (ConstructibleTensorModel.tensorRepresentativeIso l k X).hom.app (HP, HQ)
  let rN := (B.models.iso _ _ _ _ _ (NY.kflat P) (NY.kflat Q)).hom
  let rL := (A.models.iso _ _ _ _ _
    (W.kflat _ (NY.kflat P)) (W.kflat _ (NY.kflat Q))).hom
  let rR := (A.models.iso _ _ _ _ _ (NX.kflat HP) (NX.kflat HQ)).hom
  change H.map rY ≫ μ.hom.app (DerivedCategory.Q.obj P.obj, DerivedCategory.Q.obj Q.obj) ≫
      TX.map (Prod.mkHom (δH.hom.app P.obj) (δH.hom.app Q.obj)) =
    δH.hom.app T ≫ DerivedCategory.Q.map J ≫ rH at hH
  have hσX := ordinaryPresentationScalar_representative l X R A E NX HP HQ
  have hσY := ordinaryPresentationScalar_representative l Y S B E NY P Q
  have hW := W.representative (eY.obj P.obj) (eY.obj Q.obj) (NY.kflat P) (NY.kflat Q)
  have hL := PurCompactSupport.tensor_composite_normalize F BY AX W.tensor.hom
    (EY.map rY ≫ σY.hom.app (DerivedCategory.Q.obj P.obj, DerivedCategory.Q.obj Q.obj))
    (pbcComplexCounit (coefficientMap l Y S E) P.obj)
    (pbcComplexCounit (coefficientMap l Y S E) Q.obj)
    (O.pullCounit.app (eY.obj P.obj)) (O.pullCounit.app (eY.obj Q.obj))
    (pbcComplexCounit (coefficientMap l Y S E) T)
    (DerivedCategory.Q.map (NY.balance.hom.app (P.obj, Q.obj))) rN
    (O.pullCounit.app (tY.obj (eY.obj P.obj, eY.obj Q.obj)))
    (DerivedCategory.Q.map (W.cochain.hom.app (eY.obj P.obj, eY.obj Q.obj))) rL
    (by simpa only [Category.assoc] using hσY) hW
  have hR := PurCompactSupport.tensor_composite_normalize EX TX AX σX.hom
    (H.map rY ≫ μ.hom.app (DerivedCategory.Q.obj P.obj, DerivedCategory.Q.obj Q.obj))
    (δH.hom.app P.obj) (δH.hom.app Q.obj)
    (pbcComplexCounit (coefficientMap l X R E) HP.obj)
    (pbcComplexCounit (coefficientMap l X R E) HQ.obj)
    (δH.hom.app T) (DerivedCategory.Q.map J) rH
    (pbcComplexCounit (coefficientMap l X R E) (cX.obj (HP.obj, HQ.obj)))
    (DerivedCategory.Q.map (NX.balance.hom.app (HP.obj, HQ.obj))) rR
    (by simpa only [Category.assoc] using hH) hσX
  simp only [Functor.map_comp, Category.assoc] at hL hR
  have hnL := O.pullCounit.naturality (NY.balance.hom.app (P.obj, Q.obj))
  have hnR := (scalar_counit (coefficientMap l X R E)).naturality J
  dsimp only [Functor.comp_map] at hnL hnR
  change F.map (DerivedCategory.Q.map (NY.balance.hom.app (P.obj, Q.obj))) ≫
      O.pullCounit.app (tY.obj (eY.obj P.obj, eY.obj Q.obj)) =
    O.pullCounit.app (eY.obj T) ≫
      DerivedCategory.Q.map (Fc.map (NY.balance.hom.app (P.obj, Q.obj))) at hnL
  change EX.map (DerivedCategory.Q.map J) ≫
      pbcComplexCounit (coefficientMap l X R E) (cX.obj (HP.obj, HQ.obj)) =
    pbcComplexCounit (coefficientMap l X R E) (Hc.obj T) ≫
      DerivedCategory.Q.map (eX.map J) at hnR
  erw [reassoc_of% hnL] at hL
  erw [reassoc_of% hnR] at hR
  let lc (Z : CochainComplex (integralTowerModules l k Y) ℤ) :=
    F.map (pbcComplexCounit (coefficientMap l Y S E) Z) ≫ O.pullCounit.app (eY.obj Z)
  let rc (Z : CochainComplex (integralTowerModules l k Y) ℤ) :=
    EX.map (δH.hom.app Z) ≫ pbcComplexCounit (coefficientMap l X R E) (Hc.obj Z)
  let μL : TY ⋙ EY ⋙ F ⟶ (EY ⋙ F).prod (EY ⋙ F) ⋙ AX :=
    Functor.whiskerRight σY.hom F ≫ Functor.whiskerLeft (EY.prod EY) W.tensor.hom
  let μR : TY ⋙ H ⋙ EX ⟶ (H ⋙ EX).prod (H ⋙ EX) ⋙ AX :=
    Functor.whiskerRight μ.hom EX ≫ Functor.whiskerLeft (H.prod H) σX.hom
  have hL' : (EY ⋙ F).map rY ≫ μL.app
      (DerivedCategory.Q.obj P.obj, DerivedCategory.Q.obj Q.obj) ≫
        AX.map (Prod.mkHom (lc P.obj) (lc Q.obj)) =
      lc T ≫ DerivedCategory.Q.map (Fc.map (NY.balance.hom.app (P.obj, Q.obj)) ≫
        W.cochain.hom.app (eY.obj P.obj, eY.obj Q.obj)) ≫ rL := by
    simpa only [μL, lc, EY, Functor.prod_obj, Functor.comp_obj, Functor.comp_map,
      Functor.whiskerRight_app, Functor.whiskerLeft_app, NatTrans.comp_app,
      Functor.map_comp, Category.assoc] using hL
  have hR' : (H ⋙ EX).map rY ≫ μR.app
      (DerivedCategory.Q.obj P.obj, DerivedCategory.Q.obj Q.obj) ≫
        AX.map (Prod.mkHom (rc P.obj) (rc Q.obj)) =
      rc T ≫ DerivedCategory.Q.map (eX.map J ≫ NX.balance.hom.app (HP.obj, HQ.obj)) ≫ rR := by
    simpa only [μR, rc, H, HP, HQ, Functor.prod_obj, Functor.comp_obj, Functor.comp_map,
      Functor.whiskerRight_app, Functor.whiskerLeft_app, NatTrans.comp_app,
      Functor.map_comp, Category.assoc] using hR
  have norm (Z : CochainComplex (integralTowerModules l k Y) ℤ) :
      v.inv.app (DerivedCategory.Q.obj Z) ≫ lc Z =
        rc Z ≫ DerivedCategory.Q.map (γ.hom.app Z) :=
    by simpa only [lc, rc, Category.assoc] using
      nativeOrdinaryBalance_representative l p R S O E I Z
  have hγ := A.models.comparison.hom.naturality
    (X := (⟨eX.obj HP.obj, NX.kflat HP⟩, ⟨eX.obj HQ.obj, NX.kflat HQ⟩))
    (Y := (⟨Fc.obj (eY.obj P.obj), W.kflat _ (NY.kflat P)⟩,
      ⟨Fc.obj (eY.obj Q.obj), W.kflat _ (NY.kflat Q)⟩))
    (Prod.mkHom (ObjectProperty.homMk (γ.hom.app P.obj))
      (ObjectProperty.homMk (γ.hom.app Q.obj)))
  have hchain := congrArg DerivedCategory.Q.map
    (nativeScalarTensor_cochain l p R S O E I A B NX NY W P.obj Q.obj)
  let := R.commutative
  let := S.commutative
  have : PreservesFiniteLimits (pbcExtend (coefficientMap l Y S E)) :=
    LocallyFiniteAdicRealization.nativeIntegralCoefficient_flat l Y k
      (LocallyFiniteAdicRealization.embedding l E) (S.coefficient E)
  have : PreservesColimitsOfSize.{0, 0} (pbcExtend (coefficientMap l Y S E)) :=
    (pbcScalarAdjunction (coefficientMap l Y S E)).leftAdjoint_preservesColimits
  have := nativePullbackCoefficient_isIso l p R S O
  have hpost (Z : CochainComplex (integralTowerModules l k Y) ℤ) : IsIso (lc Z) := by
    have := nativePullbackScalarCounit_isIso (coefficientMap l Y S E) Z
    have := nativePullbackNormalizedCounit_isIso p O.coefficient O.pullCounit
      O.pull_normalized (eY.obj Z)
    dsimp only [lc]
    infer_instance
  have := hpost P.obj
  have := hpost Q.obj
  have : IsIso rY := by dsimp only [rY]; infer_instance
  have hf := PurCompactSupport.tensor_square_of_normalizations (EY ⋙ F) (H ⋙ EX) TY AX
    μL μR v.inv (DerivedCategory.Q.obj P.obj) (DerivedCategory.Q.obj Q.obj) _ rY
    (lc P.obj) (lc Q.obj) (rc P.obj) (rc Q.obj)
    (DerivedCategory.Q.map (γ.hom.app P.obj)) (DerivedCategory.Q.map (γ.hom.app Q.obj))
    (lc T) (rc T) (DerivedCategory.Q.map (γ.hom.app T))
    (DerivedCategory.Q.map (Fc.map (NY.balance.hom.app (P.obj, Q.obj)) ≫
      W.cochain.hom.app (eY.obj P.obj, eY.obj Q.obj)))
    (DerivedCategory.Q.map (eX.map J ≫ NX.balance.hom.app (HP.obj, HQ.obj)))
    (DerivedCategory.Q.map (tX.map (Prod.mkHom (γ.hom.app P.obj) (γ.hom.app Q.obj))))
    rL rR hL' hR' (norm P.obj) (norm Q.obj) (norm T)
    (by simpa only [Functor.map_comp, Category.assoc] using hchain.symm) hγ
  simpa only [μL, μR, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    NatTrans.comp_app, Functor.prod_obj, Functor.comp_obj, Category.assoc] using hf

-- Ordinary tensor compatibility, before completion.
private theorem nativeOrdinaryTensorSquare (l : ℕ) [Fact l.Prime]
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y] (p : X ⟶ Y)
    (R : LocallyFiniteAdicRealization.Realization l X)
    (S : LocallyFiniteAdicRealization.Realization l Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (O : Operations l p R S) (A : At l X R) (B : At l Y S)
    (E : AlgebraicallyClosedCoefficients.Index l (PadicAlgCl l))
    (NX : FiniteNormalization l X R A E) (NY : FiniteNormalization l Y S B E)
    (I : IntegralComparison l p R S O E) (W : TensorComparison l p R S O A B)
    (M N : DerivedCategory (integralTowerModules l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) Y)) :
    let k := AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E
    let EX := pbcDerivedExtend (coefficientMap l X R E)
    let EY := pbcDerivedExtend (coefficientMap l Y S E)
    let F := ContinuousRational.derivedPull p O.coefficient
    let H := PurCompactSupport.pull (PurCompactSupport.completed l k) p
    let T := (IntegralOrdinary.tensorModel l k Y).tensor
    let μ := proEtaleCanonicalTensorComparison p
      ((PurCompactSupport.completed l k).ring Y)
      ((PurCompactSupport.completed l k).ring X) ((PurCompactSupport.completed l k).pull p)
      (IntegralOrdinary.tensorModel l k Y) (IntegralOrdinary.tensorModel l k X)
    let v := nativeOrdinaryBalance l p R S O E I
    F.map ((ordinaryPresentationScalar l Y S B E NY).inv.app (M, N)) ≫
        v.hom.app (T.obj (M, N)) ≫ EX.map (μ.hom.app (M, N)) =
      W.tensor.hom.app (EY.obj M, EY.obj N) ≫
        A.closed.tensor.map (Prod.mkHom (v.hom.app M) (v.hom.app N)) ≫
        (ordinaryPresentationScalar l X R A E NX).inv.app (H.obj M, H.obj N) := by
  classical
  intro k EX EY F H TY μ v
  let σX := ordinaryPresentationScalar l X R A E NX
  let σY := ordinaryPresentationScalar l Y S B E NY
  let L := Functor.isoWhiskerRight μ.symm EX ≪≫
    Functor.isoWhiskerLeft TY v.symm ≪≫
    Functor.isoWhiskerRight σY F ≪≫
    Functor.isoWhiskerLeft (EY.prod EY) W.tensor
  let T := Functor.isoWhiskerLeft (H.prod H) σX ≪≫
    Functor.isoWhiskerRight (NatIso.prod v.symm v.symm) A.closed.tensor
  have he : L.hom = T.hom := by
    have hfaith := (SheafOfModules.cochain_tensor_model_rigidity (ProEt.topology Y)
      (completedIntegralCommRingSheafUnrestricted l k Y)).choose_spec.2.2
    apply (hfaith _ inferInstance _ _).injective
    apply NatTrans.ext
    funext PQ
    have h := nativeOrdinaryTensor_good l p R S O A B E NX NY I W PQ.1 PQ.2
    change v.inv.app (TY.obj (DerivedCategory.Q.obj PQ.1.obj,
        DerivedCategory.Q.obj PQ.2.obj)) ≫
        F.map (σY.hom.app (DerivedCategory.Q.obj PQ.1.obj,
          DerivedCategory.Q.obj PQ.2.obj)) ≫
        W.tensor.hom.app (EY.obj (DerivedCategory.Q.obj PQ.1.obj),
          EY.obj (DerivedCategory.Q.obj PQ.2.obj)) =
      EX.map (μ.hom.app (DerivedCategory.Q.obj PQ.1.obj,
        DerivedCategory.Q.obj PQ.2.obj)) ≫
        σX.hom.app (H.obj (DerivedCategory.Q.obj PQ.1.obj),
          H.obj (DerivedCategory.Q.obj PQ.2.obj)) ≫
        A.closed.tensor.map (Prod.mkHom (v.inv.app (DerivedCategory.Q.obj PQ.1.obj))
          (v.inv.app (DerivedCategory.Q.obj PQ.2.obj))) at h
    have h' := congrArg (fun f ↦ EX.map (μ.inv.app
      (DerivedCategory.Q.obj PQ.1.obj, DerivedCategory.Q.obj PQ.2.obj)) ≫ f) h
    simpa only [L, T, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
      Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
      Functor.whiskerLeft_app, Functor.whiskerRight_app, NatIso.prod_hom, NatTrans.prod,
      SheafOfModules.cochainTensorRepresentativeLocalization,
      Functor.prod_obj, Functor.comp_obj, ObjectProperty.ι_obj, Category.assoc,
      ← EX.map_comp_assoc, Iso.inv_hom_id_app, EX.map_id, Category.id_comp] using h'
  have h := congrArg (fun τ ↦ τ.app (M, N)) he
  have hr := iso_rotate (EX.mapIso (μ.app (M, N)).symm)
    (v.app (TY.obj (M, N))).symm (F.mapIso (σY.app (M, N)))
    (W.tensor.app (EY.obj M, EY.obj N)) (σX.app (H.obj M, H.obj N))
    (A.closed.tensor.mapIso ((v.app M).symm.prod (v.app N).symm))
    (by
      simpa only [L, T, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
        Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
        Functor.whiskerLeft_app, Functor.whiskerRight_app, NatIso.prod_hom, NatTrans.prod,
        Functor.mapIso_hom, Iso.app_hom, Iso.app_inv, Iso.prod_hom,
        Functor.prod_obj, Functor.comp_obj] using h)
  simpa only [Functor.mapIso_inv, Functor.mapIso_hom, Iso.symm_inv, Iso.symm_hom,
    Iso.prod_inv, Iso.app_inv, Iso.app_hom] using hr

set_option maxHeartbeats 2400000 in
-- Normalize the finite tensor factorization and the augmentation square.
/-- The normalized native comparison respects the completed integral tensor
square over one fixed coefficient field. Source: BS Remark 6.8.15; the whole-tower
augmentation square is IntegralOrdinary.tensorPullback_augmentation.
(blueprint: lem-sf-native-pullback-finite-tensor-coherence).

Proof: noetherianity makes native integral scalar extension exact, so its
computation counits are invertible.
Fix integral K,L and choose flat-term K-flat representatives. First compare the
ordinary cochain maps, before completion: use NY.balance to separate the two scalar
extensions, I.balance on the factors and their total tensor, and NX.balance to combine
the target factors. Transpose through the normalized module adjunction. The formulas
NY.balance_sections, NX.balance_sections, I.sections and W.pure send a homogeneous
pure tensor to the same balanced tensor with the same insertion-of-one factors.
All coefficient factors have degree zero; hence the signed total differentials agree.
Sheafified tensor generation and coproduct universality prove the cochain square.
Use the all-cochain representative equation of I, the K-flat representatives of NX,NY,
and W.representative to descend this square, cancelling their invertible model maps
and exact computation counits. This gives the ordinary scalar/native tensor square
in the specified ambient closed models, rather than an independently chosen tensor.
For completion, tensorPresentationComparison identifies NX.completion and NY.completion
with the canonical integral tensor presentation. Its augmentation theorem identifies
their maps with the canonical normalized augmentation. Apply
IntegralOrdinary.tensorPullback_augmentation, which holds for arbitrary scheme maps
on the complete strict towers. Its unary pullComparison is pullIso.hom followed by
the specified ordinaryIntegralCompletionComparison. The normalization I.completion_hom
identifies the latter with I.completion; uniqueness of the ordinary exact derived
comparison identifies pullIso with the comparison used in the preceding square.
Paste with that square and cancel the model comparison isomorphisms. The resulting
formula is exactly the asserted square with d_K = I.derived.inv(K) followed by
EX(I.completion(K).hom). This uses the actual tower augmentation, including quotient
transitions and shifted zero coordinates, rather than only its individual reductions.
It assumes neither flatness of quotient-ring maps nor commutation of inverse image
with products, and it never cancels an incomplete completion unit. Zero or torsion
inputs and empty schemes obey the same functorial equations. -/
theorem nativePullbackFiniteTensorCoherence (l : ℕ) [Fact l.Prime]
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y] (p : X ⟶ Y)
    (R : LocallyFiniteAdicRealization.Realization l X)
    (S : LocallyFiniteAdicRealization.Realization l Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (O : Operations l p R S) (A : At l X R) (B : At l Y S)
    (E : AlgebraicallyClosedCoefficients.Index l (PadicAlgCl l))
    (NX : FiniteNormalization l X R A E) (NY : FiniteNormalization l Y S B E)
    (I : IntegralComparison l p R S O E) (W : TensorComparison l p R S O A B) :
    NativePullbackFiniteTensorSquare l p R S O A B E NX NY I W := by
  intro K L
  let k := AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E
  let EX := pbcDerivedExtend (coefficientMap l X R E)
  let EY := pbcDerivedExtend (coefficientMap l Y S E)
  let F := ContinuousRational.derivedPull p O.coefficient
  let H := PurCompactSupport.pull (PurCompactSupport.completed l k) p
  let P := constructibleIntegralPullback l k p
  let TX := (IntegralOrdinary.tensorModel l k X).tensor
  let TY := (IntegralOrdinary.tensorModel l k Y).tensor
  let UY := constructibleIntegralTensor l k Y
  let τX := ordinaryPresentationCompletion l k X NX.completion
  let τY := ordinaryPresentationCompletion l k Y NY.completion
  let tY := τY.app (K.obj, L.obj)
  let tX := τX.app ((P.obj K).obj, (P.obj L).obj)
  let sY := (ordinaryPresentationScalar l Y S B E NY).inv.app (K.obj, L.obj)
  let sX := (ordinaryPresentationScalar l X R A E NX).inv.app
    (H.obj K.obj, H.obj L.obj)
  let sX' := (ordinaryPresentationScalar l X R A E NX).inv.app
    ((P.obj K).obj, (P.obj L).obj)
  let ρ := IntegralOrdinary.pullComparison l k p
  let iK := ρ.app K.obj
  let iL := ρ.app L.obj
  let iT := ρ.app (UY.obj (K, L)).obj
  let n := (canonicalIntegralPullbackTensor l k p K L).hom.hom
  let μ := proEtaleCanonicalTensorComparison p
    ((PurCompactSupport.completed l k).ring Y)
    ((PurCompactSupport.completed l k).ring X) ((PurCompactSupport.completed l k).pull p)
    (IntegralOrdinary.tensorModel l k Y) (IntegralOrdinary.tensorModel l k X)
  let m := μ.hom.app (K.obj, L.obj)
  let v := nativeOrdinaryBalance l p R S O E I
  have ho := nativeOrdinaryTensorSquare l p R S O A B E NX NY I W K.obj L.obj
  change F.map sY ≫ v.hom.app (TY.obj (K.obj, L.obj)) ≫ EX.map m =
    W.tensor.hom.app (EY.obj K.obj, EY.obj L.obj) ≫
      A.closed.tensor.map (Prod.mkHom (v.hom.app K.obj) (v.hom.app L.obj)) ≫ sX at ho
  have hc₀ := IntegralOrdinary.tensorPullback_augmentation l k p τX τY
    (ordinaryPresentation_normalized l k X NX.completion)
    (ordinaryPresentation_normalized l k Y NY.completion) K L
  have hn := τX.naturality (Prod.mkHom iK iL)
  have hc : H.map tY ≫ iT ≫ n = m ≫ TX.map (Prod.mkHom iK iL) ≫ tX := by
    exact hc₀.trans (by rw [← hn]; rfl)
  have hv := v.hom.naturality tY
  change F.map (EY.map tY) ≫ v.hom.app (UY.obj (K, L)).obj =
    v.hom.app (TY.obj (K.obj, L.obj)) ≫ EX.map (H.map tY) at hv
  have hs := (ordinaryPresentationScalar l X R A E NX).inv.naturality
    (Prod.mkHom iK iL)
  change A.closed.tensor.map (Prod.mkHom (EX.map iK) (EX.map iL)) ≫ sX' =
    sX ≫ EX.map (TX.map (Prod.mkHom iK iL)) at hs
  have fY := ordinaryPresentation_factor l Y S B E NY K L
  change finiteIntegralTensorMap l Y S B E NY K L = sY ≫ EY.map tY at fY
  have fX := ordinaryPresentation_factor l X R A E NX (P.obj K) (P.obj L)
  change finiteIntegralTensorMap l X R A E NX (P.obj K) (P.obj L) =
    sX' ≫ EX.map tX at fX
  dsimp only []
  erw [nativePullbackIntegralMap_factor, nativePullbackIntegralMap_factor,
    nativePullbackIntegralMap_factor]
  change F.map (finiteIntegralTensorMap l Y S B E NY K L) ≫
      (v.hom.app (UY.obj (K, L)).obj ≫ EX.map iT) ≫ EX.map n =
    W.tensor.hom.app (EY.obj K.obj, EY.obj L.obj) ≫
      A.closed.tensor.map (Prod.mkHom (v.hom.app K.obj ≫ EX.map iK)
        (v.hom.app L.obj ≫ EX.map iL)) ≫
      finiteIntegralTensorMap l X R A E NX (P.obj K) (P.obj L)
  simp only [fY, fX]
  calc
    _ = F.map sY ≫ v.hom.app (TY.obj (K.obj, L.obj)) ≫
        EX.map (H.map tY ≫ iT ≫ n) := by
      simpa only [Functor.map_comp, Category.assoc] using
        congrArg (fun z ↦ F.map sY ≫ z ≫ EX.map iT ≫ EX.map n) hv
    _ = F.map sY ≫ v.hom.app (TY.obj (K.obj, L.obj)) ≫
        EX.map m ≫ EX.map (TX.map (Prod.mkHom iK iL)) ≫ EX.map tX := by
      simpa only [Functor.map_comp, Category.assoc] using
        congrArg (fun z ↦ F.map sY ≫ v.hom.app (TY.obj (K.obj, L.obj)) ≫ EX.map z) hc
    _ = W.tensor.hom.app (EY.obj K.obj, EY.obj L.obj) ≫
        A.closed.tensor.map (Prod.mkHom (v.hom.app K.obj) (v.hom.app L.obj)) ≫
        sX ≫ EX.map (TX.map (Prod.mkHom iK iL)) ≫ EX.map tX := by
      simpa only [Category.assoc] using congrArg
        (fun z ↦ z ≫ EX.map (TX.map (Prod.mkHom iK iL)) ≫ EX.map tX) ho
    _ = W.tensor.hom.app (EY.obj K.obj, EY.obj L.obj) ≫
        A.closed.tensor.map (Prod.mkHom (v.hom.app K.obj) (v.hom.app L.obj)) ≫
        A.closed.tensor.map (Prod.mkHom (EX.map iK) (EX.map iL)) ≫ sX' ≫ EX.map tX := by
      simpa only [Category.assoc] using congrArg
        (fun z ↦ W.tensor.hom.app (EY.obj K.obj, EY.obj L.obj) ≫
          A.closed.tensor.map (Prod.mkHom (v.hom.app K.obj) (v.hom.app L.obj)) ≫
          z ≫ EX.map tX) hs.symm
    _ = _ := by
      simp only [← Category.assoc, ← Functor.map_comp]
      rfl

end WeilConjectures.AdicQbarRealization.Proper
