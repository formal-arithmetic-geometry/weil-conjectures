/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.CategoryTheory.LocalizedModuleExactForSystems
public import WeilConjectures.Algebra.Homology.SmoothPurity.LocalizedModuleExactIndependent
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
public import WeilConjectures.CategoryTheory.RingedSliceExtensionTensor
public import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.CategoryTheory.RingedSliceExtensionTensorHomData
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import WeilConjectures.Mathlib.Algebra.Homology.Bifunctor
import Mathlib.Algebra.Homology.BifunctorFlip
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology

/-! # Total tensor and K-flatness for ringed slice extension

Source: Stacks Project, Modules on Sites, Tag 0E8I (lemma-j-shriek-and-tensor),
Homology, Tag 012Z, and Cohomology on Sites, Tags 06YN and 06YS
(blueprint: lem-sf-ringed-open-total-tensor-kflat).

The total tensor is Mathlib's direct-sum total cochain complex. Both module functors
are the existing localized-system functors, applied termwise. The site object and
morphism universes remain independent; coefficients live in a universe containing both.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe c v r

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

namespace SheafOfModules

variable {S : Type c} [Category.{v} S] {J : GrothendieckTopology S}
  (R : Sheaf J CommRingCat.{max c v r}) (U : S)

/-- The recorded ringed-slice functor, with canonical sheafification instances explicit.
Source: Stacks Project, Modules on Sites, Tags 03DJ and 0E8I
(blueprint: lem-sf-ringed-open-total-tensor-kflat). -/
def ringedOpenExtension :=
  letI : HasSheafify J AddCommGrpCat.{max c v r} :=
    hasSheafify_coefficientUniverse.{c, v, max c v r} (J := J)
  letI : HasSheafify (J.over U) AddCommGrpCat.{max c v r} :=
    hasSheafify_coefficientUniverse.{max c v, v, max c v r} (J := J.over U)
  letI : J.WEqualsLocallyBijective AddCommGrpCat.{max c v r} :=
    wEqualsLocallyBijective_coefficientUniverse.{c, v, max c v r} (J := J)
  letI : (J.over U).WEqualsLocallyBijective AddCommGrpCat.{max c v r} :=
    wEqualsLocallyBijective_coefficientUniverse.{max c v, v, max c v r} (J := J.over U)
  localizedSystemExtension.{c, v, r} R U

/-- Termwise application of the actual direct-sum extension followed by sheafification.
Source: Stacks Project, Modules on Sites, Tags 03DI--03DJ and 0E8I
(blueprint: lem-sf-ringed-open-total-tensor-kflat). -/
abbrev ringedOpenExtensionOnComplexes :
    CochainComplex (SheafOfModules.{max c v r}
      (((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj
        R).over U)) ℤ ⥤
    CochainComplex (SheafOfModules.{max c v r}
      ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) ℤ :=
  letI : HasSheafify J AddCommGrpCat.{max c v r} :=
    hasSheafify_coefficientUniverse.{c, v, max c v r} (J := J)
  letI := localizedSystemExtensionAdditive.{c, v, r} R U
  (localizedSystemExtension.{c, v, r} R U).mapHomologicalComplex (ComplexShape.up ℤ)

/-- The existing sheaf tensor with its coefficient ring specified explicitly.
Source: Stacks Project, Modules on Sites, Section 03EK
(blueprint: lem-sf-ringed-open-total-tensor-kflat). -/
def ringedOpenTensor {T : Type c} [Category.{v} T] {K : GrothendieckTopology T}
    (A : Sheaf K CommRingCat.{max c v r}) :=
  @curriedTensor (SheafOfModules.{max c v r}
    ((sheafCompose K (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj A)) _
    (cochainModulesMonoidal.{c, v, max c v r} A)

/-- Zero-map preservation for the specified existing tensor.
Source: Stacks Project, Modules on Sites, Section 03EK
(blueprint: lem-sf-ringed-open-total-tensor-kflat). -/
instance ringedOpenTensorZero {T : Type c} [Category.{v} T] {K : GrothendieckTopology T}
    (A : Sheaf K CommRingCat.{max c v r}) :
    (ringedOpenTensor.{c, v, r} A).PreservesZeroMorphisms :=
  letI := cochainModulesMonoidal.{c, v, max c v r} A
  letI := cochainModulesPreadditive.{c, v, max c v r} A
  inferInstanceAs ((curriedTensor (SheafOfModules.{max c v r}
    ((sheafCompose K
      (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj A))).PreservesZeroMorphisms)

/-- Zero-map preservation in the second variable of the existing tensor.
Source: Stacks Project, Modules on Sites, Section 03EK
(blueprint: lem-sf-ringed-open-total-tensor-kflat). -/
instance ringedOpenTensorObjZero {T : Type c} [Category.{v} T] {K : GrothendieckTopology T}
    (A : Sheaf K CommRingCat.{max c v r})
    (M : SheafOfModules.{max c v r}
      ((sheafCompose K (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj A)) :
    ((ringedOpenTensor.{c, v, r} A).obj M).PreservesZeroMorphisms :=
  letI := cochainModulesMonoidal.{c, v, max c v r} A
  letI := cochainModulesPreadditive.{c, v, max c v r} A
  inferInstanceAs (((curriedTensor (SheafOfModules.{max c v r}
    ((sheafCompose K
      (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj A))).obj M).PreservesZeroMorphisms)

/-- The existing total tensor has the required direct sums on this small ringed site.
Source: Stacks Project, Homology, Tag 012Z
(blueprint: lem-sf-ringed-open-total-tensor-kflat). -/
instance ringedOpenHasTotalTensor {T : Type c} [Category.{v} T]
    {K : GrothendieckTopology T} (A : Sheaf K CommRingCat.{max c v r})
    (P C : CochainComplex (SheafOfModules.{max c v r}
      ((sheafCompose K (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj A)) ℤ) :
    P.HasMapBifunctor C (ringedOpenTensor.{c, v, r} A) :=
  letI : HasSheafify K AddCommGrpCat.{max c v r} :=
    hasSheafify_coefficientUniverse.{c, v, max c v r} (J := K)
  letI : K.WEqualsLocallyBijective AddCommGrpCat.{max c v r} :=
    wEqualsLocallyBijective_coefficientUniverse.{c, v, max c v r} (J := K)
  inferInstance

/-- The existing total tensor bifunctor, with its canonical instances supplied explicitly.
Source: Stacks Project, Homology, Tag 012Z
(blueprint: lem-sf-ringed-open-total-tensor-kflat). -/
def ringedOpenTotalTensor {T : Type c} [Category.{v} T] {K : GrothendieckTopology T}
    (A : Sheaf K CommRingCat.{max c v r}) :=
  letI := ringedOpenTensorZero.{c, v, r} A
  letI := ringedOpenTensorObjZero.{c, v, r} A
  letI := ringedOpenHasTotalTensor.{c, v, r} A
  (ringedOpenTensor.{c, v, r} A).map₂CochainComplex

/-- The simultaneous map of the existing total tensor bifunctor on two chain maps.
Source: Stacks Project, Homology, Tag 012Z
(blueprint: lem-sf-ringed-open-total-tensor-kflat). -/
def ringedOpenTotalTensorMap {T : Type c} [Category.{v} T] {K : GrothendieckTopology T}
    (A : Sheaf K CommRingCat.{max c v r})
    {P P' C C' : CochainComplex (SheafOfModules.{max c v r}
      ((sheafCompose K (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj A)) ℤ}
    (a : P ⟶ P') (b : C ⟶ C') :
    ((ringedOpenTotalTensor.{c, v, r} A).obj P).obj C ⟶
      ((ringedOpenTotalTensor.{c, v, r} A).obj P').obj C' :=
  (((ringedOpenTotalTensor.{c, v, r} A).map a).app C) ≫
    ((ringedOpenTotalTensor.{c, v, r} A).obj P').map b

private theorem precompose_preservesZero
    {A B D : Type*} [Category* A] [Category* B] [Category* D]
    [HasZeroMorphisms A] [HasZeroMorphisms B] [HasZeroMorphisms D]
    (H : A ⥤ A ⥤ D) [H.PreservesZeroMorphisms]
    (T : B ⥤ A) :
    (H ⋙ (Functor.whiskeringLeft B A D).obj T).PreservesZeroMorphisms := by
  constructor
  intro M M'
  apply NatTrans.ext
  funext N
  change (H.map 0).app (T.obj N) = 0
  rw [Functor.map_zero]
  rfl

private theorem precompose_obj_preservesZero
    {A B D : Type*} [Category* A] [Category* B] [Category* D]
    [HasZeroMorphisms A] [HasZeroMorphisms B] [HasZeroMorphisms D]
    (H : A ⥤ A ⥤ D) [∀ M, (H.obj M).PreservesZeroMorphisms]
    (T : B ⥤ A) [T.PreservesZeroMorphisms] (M : A) :
    ((H ⋙ (Functor.whiskeringLeft B A D).obj T).obj M).PreservesZeroMorphisms :=
  inferInstanceAs (T ⋙ H.obj M).PreservesZeroMorphisms

private theorem precompose_hasTotal
    {A B D : Type*} [Category* A] [Category* B] [Category* D]
    [HasZeroMorphisms A] [HasZeroMorphisms B] [Preadditive D]
    (H : A ⥤ A ⥤ D) [H.PreservesZeroMorphisms]
    [∀ M, (H.obj M).PreservesZeroMorphisms]
    (T : B ⥤ A) [T.PreservesZeroMorphisms]
    [(H ⋙ (Functor.whiskeringLeft B A D).obj T).PreservesZeroMorphisms]
    [∀ M, ((H ⋙ (Functor.whiskeringLeft B A D).obj T).obj M).PreservesZeroMorphisms]
    [∀ (P C : CochainComplex A ℤ), HomologicalComplex.HasMapBifunctor P C H (.up ℤ)]
    (P : CochainComplex A ℤ) (C : CochainComplex B ℤ) :
    HomologicalComplex.HasMapBifunctor P C
      (H ⋙ (Functor.whiskeringLeft B A D).obj T) (.up ℤ) :=
  inferInstanceAs (HomologicalComplex.HasMapBifunctor P
    ((T.mapHomologicalComplex (.up ℤ)).obj C) H (.up ℤ))

private theorem map₂_map_eq {D₁ D₂ D₃ : Type*}
    [Category* D₁] [Category* D₂] [Category* D₃]
    [HasZeroMorphisms D₁] [HasZeroMorphisms D₂] [Preadditive D₃]
    (F : D₁ ⥤ D₂ ⥤ D₃) [F.PreservesZeroMorphisms]
    [∀ M, (F.obj M).PreservesZeroMorphisms]
    [∀ (P : CochainComplex D₁ ℤ) (C : CochainComplex D₂ ℤ),
      HomologicalComplex.HasMapBifunctor P C F (.up ℤ)]
    {P P' : CochainComplex D₁ ℤ} {C C' : CochainComplex D₂ ℤ}
    (a : P ⟶ P') (b : C ⟶ C') :
    ((F.map₂CochainComplex.map a).app C) ≫ (F.map₂CochainComplex.obj P').map b =
      HomologicalComplex.mapBifunctorMap a b F (.up ℤ) := by
  ext n
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q h
  simp [HomologicalComplex.ι_mapBifunctorMap,
    HomologicalComplex.ι_mapBifunctorMap_assoc]

private theorem mapBifunctorMap_precompose
    {D₁ D₂ D₃ D₄ : Type*} [Category* D₁] [Category* D₂] [Category* D₃] [Category* D₄]
    [HasZeroMorphisms D₁] [HasZeroMorphisms D₂] [HasZeroMorphisms D₃] [Preadditive D₄]
    (H : D₁ ⥤ D₃ ⥤ D₄) (T : D₂ ⥤ D₃) [T.PreservesZeroMorphisms]
    [H.PreservesZeroMorphisms] [∀ M, (H.obj M).PreservesZeroMorphisms]
    [(H ⋙ (Functor.whiskeringLeft D₂ D₃ D₄).obj T).PreservesZeroMorphisms]
    [∀ M, ((H ⋙ (Functor.whiskeringLeft D₂ D₃ D₄).obj T).obj M).PreservesZeroMorphisms]
    [∀ (P : CochainComplex D₁ ℤ) (C : CochainComplex D₃ ℤ),
      HomologicalComplex.HasMapBifunctor P C H (.up ℤ)]
    [∀ (P : CochainComplex D₁ ℤ) (C : CochainComplex D₂ ℤ),
      HomologicalComplex.HasMapBifunctor P C
        (H ⋙ (Functor.whiskeringLeft D₂ D₃ D₄).obj T) (.up ℤ)]
    {P P' : CochainComplex D₁ ℤ} {C C' : CochainComplex D₂ ℤ}
    (a : P ⟶ P') (b : C ⟶ C') :
    HomologicalComplex.mapBifunctorMap a b
        (H ⋙ (Functor.whiskeringLeft D₂ D₃ D₄).obj T) (.up ℤ) =
      HomologicalComplex.mapBifunctorMap a ((T.mapHomologicalComplex (.up ℤ)).map b)
        H (.up ℤ) := by
  ext n : 1
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q h
  change _ = HomologicalComplex.ιMapBifunctor P
      ((T.mapHomologicalComplex (.up ℤ)).obj C) H (.up ℤ) p q n h ≫ _
  rw [HomologicalComplex.ι_mapBifunctorMap, HomologicalComplex.ι_mapBifunctorMap]
  rfl

private theorem comparison_precompose_natural
    {A B : Type*} [Category* A] [Category* B] [Preadditive A] [Preadditive B]
    (E : A ⥤ B) [E.Additive] [PreservesColimitsOfSize.{0, 0} E]
    (T : B ⥤ A) [T.PreservesZeroMorphisms]
    (H : A ⥤ A ⥤ A) (H' : B ⥤ B ⥤ B)
    [H.PreservesZeroMorphisms] [∀ M, (H.obj M).PreservesZeroMorphisms]
    [H'.PreservesZeroMorphisms] [∀ M, (H'.obj M).PreservesZeroMorphisms]
    [(H ⋙ (Functor.whiskeringLeft B A A).obj T).PreservesZeroMorphisms]
    [∀ M, ((H ⋙ (Functor.whiskeringLeft B A A).obj T).obj M).PreservesZeroMorphisms]
    [∀ (P C : CochainComplex A ℤ), HomologicalComplex.HasMapBifunctor P C H (.up ℤ)]
    [∀ (P C : CochainComplex B ℤ), HomologicalComplex.HasMapBifunctor P C H' (.up ℤ)]
    [∀ (P : CochainComplex A ℤ) (C : CochainComplex B ℤ),
      HomologicalComplex.HasMapBifunctor P C
        (H ⋙ (Functor.whiskeringLeft B A A).obj T) (.up ℤ)]
    (τ : (Functor.postcompose₂.obj E).obj
        (H ⋙ (Functor.whiskeringLeft B A A).obj T) ⟶
      (((Functor.whiskeringLeft₂ B).obj E).obj (𝟭 B)).obj H')
    {P P' : CochainComplex A ℤ} {C C' : CochainComplex B ℤ}
    (a : P ⟶ P') (b : C ⟶ C') :
    (E.mapHomologicalComplex (.up ℤ)).map
        (HomologicalComplex.mapBifunctorMap a ((T.mapHomologicalComplex (.up ℤ)).map b)
          H (.up ℤ)) ≫ HomologicalComplex.mapBifunctorComparison τ (.up ℤ) P' C' =
      HomologicalComplex.mapBifunctorComparison τ (.up ℤ) P C ≫
        HomologicalComplex.mapBifunctorMap ((E.mapHomologicalComplex (.up ℤ)).map a)
          b H' (.up ℤ) := by
  rw [← mapBifunctorMap_precompose H T a b]
  exact HomologicalComplex.mapBifunctorComparison_naturality τ (.up ℤ) a b

@[irreducible] private def comparisonPrecomposeIso
    {A B : Type*} [Category* A] [Category* B] [Preadditive A] [Preadditive B]
    (E : A ⥤ B) [E.Additive] [PreservesColimitsOfSize.{0, 0} E]
    (T : B ⥤ A) [T.PreservesZeroMorphisms]
    (H : A ⥤ A ⥤ A) (H' : B ⥤ B ⥤ B)
    [H.PreservesZeroMorphisms] [∀ M, (H.obj M).PreservesZeroMorphisms]
    [H'.PreservesZeroMorphisms] [∀ M, (H'.obj M).PreservesZeroMorphisms]
    [(H ⋙ (Functor.whiskeringLeft B A A).obj T).PreservesZeroMorphisms]
    [∀ M, ((H ⋙ (Functor.whiskeringLeft B A A).obj T).obj M).PreservesZeroMorphisms]
    [∀ (P C : CochainComplex A ℤ), HomologicalComplex.HasMapBifunctor P C H (.up ℤ)]
    [∀ (P C : CochainComplex B ℤ), HomologicalComplex.HasMapBifunctor P C H' (.up ℤ)]
    [∀ (P : CochainComplex A ℤ) (C : CochainComplex B ℤ),
      HomologicalComplex.HasMapBifunctor P C
        (H ⋙ (Functor.whiskeringLeft B A A).obj T) (.up ℤ)]
    (τ : (Functor.postcompose₂.obj E).obj
        (H ⋙ (Functor.whiskeringLeft B A A).obj T) ≅
      (((Functor.whiskeringLeft₂ B).obj E).obj (𝟭 B)).obj H')
    (P : CochainComplex A ℤ) (C : CochainComplex B ℤ) :
    (E.mapHomologicalComplex (.up ℤ)).obj
        (CochainComplex.mapBifunctor P ((T.mapHomologicalComplex (.up ℤ)).obj C) H) ≅
      CochainComplex.mapBifunctor ((E.mapHomologicalComplex (.up ℤ)).obj P) C H' :=
  asIso (HomologicalComplex.mapBifunctorComparison τ.hom (.up ℤ) P C)

private theorem comparisonPrecomposeIso_ι
    {A B : Type*} [Category* A] [Category* B] [Preadditive A] [Preadditive B]
    (E : A ⥤ B) [E.Additive] [PreservesColimitsOfSize.{0, 0} E]
    (T : B ⥤ A) [T.PreservesZeroMorphisms]
    (H : A ⥤ A ⥤ A) (H' : B ⥤ B ⥤ B)
    [H.PreservesZeroMorphisms] [∀ M, (H.obj M).PreservesZeroMorphisms]
    [H'.PreservesZeroMorphisms] [∀ M, (H'.obj M).PreservesZeroMorphisms]
    [(H ⋙ (Functor.whiskeringLeft B A A).obj T).PreservesZeroMorphisms]
    [∀ M, ((H ⋙ (Functor.whiskeringLeft B A A).obj T).obj M).PreservesZeroMorphisms]
    [∀ (P C : CochainComplex A ℤ), HomologicalComplex.HasMapBifunctor P C H (.up ℤ)]
    [∀ (P C : CochainComplex B ℤ), HomologicalComplex.HasMapBifunctor P C H' (.up ℤ)]
    [∀ (P : CochainComplex A ℤ) (C : CochainComplex B ℤ),
      HomologicalComplex.HasMapBifunctor P C
        (H ⋙ (Functor.whiskeringLeft B A A).obj T) (.up ℤ)]
    (τ : (Functor.postcompose₂.obj E).obj
        (H ⋙ (Functor.whiskeringLeft B A A).obj T) ≅
      (((Functor.whiskeringLeft₂ B).obj E).obj (𝟭 B)).obj H')
    (P : CochainComplex A ℤ) (C : CochainComplex B ℤ)
    (p q n : ℤ) (h : p + q = n) :
    E.map (HomologicalComplex.ιMapBifunctor P
        ((T.mapHomologicalComplex (.up ℤ)).obj C) H (.up ℤ) p q n h) ≫
        (comparisonPrecomposeIso E T H H' τ P C).hom.f n =
      (τ.hom.app (P.X p)).app (C.X q) ≫
        HomologicalComplex.ιMapBifunctor
          ((E.mapHomologicalComplex (.up ℤ)).obj P) C H' (.up ℤ) p q n h := by
  unfold comparisonPrecomposeIso
  exact HomologicalComplex.map_ιMapBifunctor_mapBifunctorComparisonX
    τ.hom (.up ℤ) P C p q n h

private theorem comparisonPrecomposeIso_natural
    {A B : Type*} [Category* A] [Category* B] [Preadditive A] [Preadditive B]
    (E : A ⥤ B) [E.Additive] [PreservesColimitsOfSize.{0, 0} E]
    (T : B ⥤ A) [T.PreservesZeroMorphisms]
    (H : A ⥤ A ⥤ A) (H' : B ⥤ B ⥤ B)
    [H.PreservesZeroMorphisms] [∀ M, (H.obj M).PreservesZeroMorphisms]
    [H'.PreservesZeroMorphisms] [∀ M, (H'.obj M).PreservesZeroMorphisms]
    [(H ⋙ (Functor.whiskeringLeft B A A).obj T).PreservesZeroMorphisms]
    [∀ M, ((H ⋙ (Functor.whiskeringLeft B A A).obj T).obj M).PreservesZeroMorphisms]
    [∀ (P C : CochainComplex A ℤ), HomologicalComplex.HasMapBifunctor P C H (.up ℤ)]
    [∀ (P C : CochainComplex B ℤ), HomologicalComplex.HasMapBifunctor P C H' (.up ℤ)]
    [∀ (P : CochainComplex A ℤ) (C : CochainComplex B ℤ),
      HomologicalComplex.HasMapBifunctor P C
        (H ⋙ (Functor.whiskeringLeft B A A).obj T) (.up ℤ)]
    (τ : (Functor.postcompose₂.obj E).obj
        (H ⋙ (Functor.whiskeringLeft B A A).obj T) ≅
      (((Functor.whiskeringLeft₂ B).obj E).obj (𝟭 B)).obj H')
    {P P' : CochainComplex A ℤ} {C C' : CochainComplex B ℤ}
    (a : P ⟶ P') (b : C ⟶ C') :
    (E.mapHomologicalComplex (.up ℤ)).map
        (HomologicalComplex.mapBifunctorMap a ((T.mapHomologicalComplex (.up ℤ)).map b)
          H (.up ℤ)) ≫ (comparisonPrecomposeIso E T H H' τ P' C').hom =
      (comparisonPrecomposeIso E T H H' τ P C).hom ≫
        HomologicalComplex.mapBifunctorMap ((E.mapHomologicalComplex (.up ℤ)).map a)
          b H' (.up ℤ) := by
  unfold comparisonPrecomposeIso
  exact comparison_precompose_natural E T H H' τ.hom a b

private theorem comparisonPrecomposeIso_map₂_natural
    {A B : Type*} [Category* A] [Category* B] [Preadditive A] [Preadditive B]
    (E : A ⥤ B) [E.Additive] [PreservesColimitsOfSize.{0, 0} E]
    (T : B ⥤ A) [T.PreservesZeroMorphisms]
    (H : A ⥤ A ⥤ A) (H' : B ⥤ B ⥤ B)
    [H.PreservesZeroMorphisms] [∀ M, (H.obj M).PreservesZeroMorphisms]
    [H'.PreservesZeroMorphisms] [∀ M, (H'.obj M).PreservesZeroMorphisms]
    [(H ⋙ (Functor.whiskeringLeft B A A).obj T).PreservesZeroMorphisms]
    [∀ M, ((H ⋙ (Functor.whiskeringLeft B A A).obj T).obj M).PreservesZeroMorphisms]
    [∀ (P C : CochainComplex A ℤ), HomologicalComplex.HasMapBifunctor P C H (.up ℤ)]
    [∀ (P C : CochainComplex B ℤ), HomologicalComplex.HasMapBifunctor P C H' (.up ℤ)]
    [∀ (P : CochainComplex A ℤ) (C : CochainComplex B ℤ),
      HomologicalComplex.HasMapBifunctor P C
        (H ⋙ (Functor.whiskeringLeft B A A).obj T) (.up ℤ)]
    (τ : (Functor.postcompose₂.obj E).obj
        (H ⋙ (Functor.whiskeringLeft B A A).obj T) ≅
      (((Functor.whiskeringLeft₂ B).obj E).obj (𝟭 B)).obj H')
    {P P' : CochainComplex A ℤ} {C C' : CochainComplex B ℤ}
    (a : P ⟶ P') (b : C ⟶ C') :
    (E.mapHomologicalComplex (.up ℤ)).map
        (((H.map₂CochainComplex.map a).app ((T.mapHomologicalComplex (.up ℤ)).obj C)) ≫
          (H.map₂CochainComplex.obj P').map ((T.mapHomologicalComplex (.up ℤ)).map b)) ≫
        (comparisonPrecomposeIso E T H H' τ P' C').hom =
      (comparisonPrecomposeIso E T H H' τ P C).hom ≫
        (((H'.map₂CochainComplex.map ((E.mapHomologicalComplex (.up ℤ)).map a)).app C) ≫
          (H'.map₂CochainComplex.obj
            ((E.mapHomologicalComplex (.up ℤ)).obj P')).map b) := by
  rw [map₂_map_eq, map₂_map_eq]
  exact comparisonPrecomposeIso_natural E T H H' τ a b

@[irreducible] private def bifunctorIsoOfComponents {D₁ D₂ D₃ : Type*}
    [Category* D₁] [Category* D₂] [Category* D₃] (F G : D₁ ⥤ D₂ ⥤ D₃)
    (e : ∀ M N, (F.obj M).obj N ≅ (G.obj M).obj N)
    (h : ∀ {M M' N N'} (a : M ⟶ M') (b : N ⟶ N'),
      (F.map a).app N ≫ (F.obj M').map b ≫ (e M' N').hom =
        (e M N).hom ≫ (G.map a).app N ≫ (G.obj M').map b) : F ≅ G :=
  NatIso.ofComponents (fun M ↦ NatIso.ofComponents (e M) (by
    intro N N' b
    simpa using h (𝟙 M) b)) (by
      intro M M' a
      apply NatTrans.ext
      funext N
      simpa using h a (𝟙 N))

private theorem bifunctorIsoOfComponents_hom {D₁ D₂ D₃ : Type*}
    [Category* D₁] [Category* D₂] [Category* D₃] (F G : D₁ ⥤ D₂ ⥤ D₃)
    (e : ∀ M N, (F.obj M).obj N ≅ (G.obj M).obj N)
    (h : ∀ {M M' N N'} (a : M ⟶ M') (b : N ⟶ N'),
      (F.map a).app N ≫ (F.obj M').map b ≫ (e M' N').hom =
        (e M N).hom ≫ (G.map a).app N ≫ (G.obj M').map b)
    (M : D₁) (N : D₂) :
    (((bifunctorIsoOfComponents F G e h).hom.app M).app N) = (e M N).hom := by
  unfold bifunctorIsoOfComponents
  rfl

private theorem tensor_acyclic_swap {D : Type*} [Category* D] [Preadditive D]
    [MonoidalCategory D] [MonoidalPreadditive D]
    (P C : CochainComplex D ℤ)
    [HomologicalComplex.HasMapBifunctor P C (curriedTensor D) (.up ℤ)]
    [HomologicalComplex.HasMapBifunctor C P (curriedTensor D) (.up ℤ)]
    [SymmetricCategory D]
    (h : (CochainComplex.mapBifunctor P C (curriedTensor D)).Acyclic) :
    (CochainComplex.mapBifunctor C P (curriedTensor D)).Acyclic := by
  let F := curriedTensor D
  let e : (((F.mapBifunctorHomologicalComplex (.up ℤ) (.up ℤ)).obj P).obj C) ≅
      (((F.flip.mapBifunctorHomologicalComplex (.up ℤ) (.up ℤ)).obj P).obj C) :=
    HomologicalComplex.Hom.isoOfComponents
      (fun p ↦ HomologicalComplex.Hom.isoOfComponents
        (fun q ↦ β_ (P.X p) (C.X q)) (by
          intro q q' hqq'
          exact (BraidedCategory.braiding_naturality_right (P.X p) (C.d q q')).symm))
      (by
        intro p p' hpp'
        ext q : 1
        exact (BraidedCategory.braiding_naturality_left (P.d p p') (C.X q)).symm)
  intro n
  exact (h n).of_iso (HomologicalComplex₂.total.mapIso e (.up ℤ) ≪≫
    HomologicalComplex.mapBifunctorFlipIso C P F (.up ℤ))

end SheafOfModules
