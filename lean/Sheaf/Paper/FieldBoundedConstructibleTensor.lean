/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF groups NE, D7
-/
module

public import Sheaf.AlgebraicGeometry.CoefficientProEtaleTorAmplitude
public import Sheaf.AlgebraicGeometry.CoefficientBoundedConstructibleProEtale
public import Sheaf.Paper.CondensedConstantConstructibility
public import Sheaf.AlgebraicGeometry.FiniteLocallyClosedStratification
public import Sheaf.Algebra.Homology.RingedKFlatSingleTensorComparison
public import Sheaf.AlgebraicGeometry.NoetherianGlobalConstructibility
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Algebra.Field.Defs
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.ConstantFieldFlat
public import Sheaf.Algebra.Homology.BoundedFlatIndependentCoefficients
import Sheaf.CategoryTheory.ConstantScalarRestrictionTensor
import all Sheaf.Paper.FiniteComparisonModelRealization
import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
import WeilConjectures.CategoryTheory.Sites.ConstantSheafMonoidal
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.RingTheory.TensorProduct.Finite
import all Sheaf.AlgebraicGeometry.CoefficientProEtaleFiniteLocalModelsPullback
import all Sheaf.AlgebraicGeometry.NoetherianGlobalConstructibility
import all Sheaf.AlgebraicGeometry.ProEtaleFinitelyPresentedLocalModelsComparison
import Sheaf.CategoryTheory.FiniteTypeLocallyConstantSerre
import Sheaf.AlgebraicGeometry.CoefficientProEtaleConstructibleIso
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologyProperty
import WeilConjectures.Mathlib.CategoryTheory.Functor.Flat
import Sheaf.CategoryTheory.Triangulated.BoundedPostnikovTower
import Sheaf.Algebra.Homology.RingedFlatSingleTensorCohomology
import Sheaf.Algebra.Homology.TensorColimitsIndependentCoefficients
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import WeilConjectures.ConstructibleSheaf.Refinement
import Sheaf.Algebra.Homology.KFlatFixedTensorTriangulated

/-! # Bounded constructible tensor over a constant field

Source: blueprint main-20261015, det-lem-int-tensor-product.proof.md, third paragraph;
Stacks Project, Tags 03ET and 06YU (blueprint: lem-sfb-field-bounded-constructible-tensor).

The coefficient-sized site is equivalent to the small pro-etale site. Constructibility
uses the existing finite constant models: over a field finitely presented modules are
finite free. The Noetherian global comparison identifies the affine-local predicate with
the finite constructible stratification required here. No completion is performed.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u v w

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped ZeroObject

namespace AlgebraicGeometry.Scheme.FieldConstructibleTensor

/-- The associated constant field ring sheaf on the existing small site model.
Source: Stacks Tag 09A5 (blueprint: lem-sfb-field-bounded-constructible-tensor). -/
abbrev ring (X : Scheme.{u}) (κ : Type (max v (u + 1))) [Field κ] :=
  ConstantCompletion.constant (coefficientProEtaleModelTopology.{u, v} X) κ

/-- The existing intrinsic module-sheaf category, specialized to constant field coefficients.
Source: Stacks Tag 03DA (blueprint: lem-sfb-field-bounded-constructible-tensor). -/
abbrev Modules (X : Scheme.{u}) (κ : Type (max v (u + 1))) [Field κ] :=
  ConstantCompletion.Mod (ring.{u, v} X κ)

/-- The standard ordinary unbounded derived category of the intrinsic module sheaves.
Source: Stacks Tag 05RU (blueprint: lem-sfb-field-bounded-constructible-tensor). -/
abbrev D (X : Scheme.{u}) (κ : Type (max v (u + 1))) [Field κ] :=
  ConstantCompletion.D (ring.{u, v} X κ)

/-- The existing ordinary sheaf tensor, with no chosen monoidal structure on the derived
category. Source: Stacks Tag 03EK (blueprint: lem-sfb-field-bounded-constructible-tensor). -/
abbrev ordinary (X : Scheme.{u}) (κ : Type (max v (u + 1))) [Field κ] :=
  SheafOfModules.KFlatFixedTensor.ordinaryTensor (ring.{u, v} X κ)

/-- The published K-flat descent tensor on a coefficient-sized small site.
Source: Stacks Tag 06YU (blueprint: lem-sfb-field-bounded-constructible-tensor). -/
def tensor {C : Type w} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{w}) :
    ConstantCompletion.D R ⥤ ConstantCompletion.D R ⥤ ConstantCompletion.D R :=
  letI := HasDerivedCategory.standard (ConstantCompletion.Mod R)
  SheafOfModules.KFlatFixedTensor.derivedTensor R

/-- The existing degree-zero embedding followed by the standard localization.
Source: Stacks Tag 05RU (blueprint: lem-sfb-field-bounded-constructible-tensor). -/
def single {C : Type w} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{w}) : ConstantCompletion.Mod R ⥤ ConstantCompletion.D R :=
  HomologicalComplex.single (ConstantCompletion.Mod R) (.up ℤ) 0 ⋙ ConstantCompletion.Q R

/-- The canonical degree-zero comparison: the normalized K-flat single-tensor comparison,
followed by the termwise-tensor identification of a single complex. Its construction uses
flatness of every constant-field module and the bounded-above flat K-flat criterion.
Source: Stacks Tags 03ET and 06YU (blueprint: lem-sfb-field-bounded-constructible-tensor). -/
def singleComparison {C : Type w} [SmallCategory C] (J : GrothendieckTopology C)
    (κ : Type w) [Field κ]
    (F G : ConstantCompletion.Mod (ConstantCompletion.constant J κ)) :
    ((tensor (ConstantCompletion.constant J κ)).obj
        ((single (ConstantCompletion.constant J κ)).obj F)).obj
        ((single (ConstantCompletion.constant J κ)).obj G) ≅
      (single (ConstantCompletion.constant J κ)).obj
        (((SheafOfModules.KFlatFixedTensor.ordinaryTensor
          (ConstantCompletion.constant J κ)).obj F).obj G) :=
  let R := ConstantCompletion.constant J κ
  letI := HasDerivedCategory.standard (ConstantCompletion.Mod R)
  let P := (HomologicalComplex.single (ConstantCompletion.Mod R) (.up ℤ) 0).obj F
  let hP := SheafOfModules.isKFlatIndependentCoefficients_of_boundedAbove_flatOnSite
    R P 0 (fun n ↦ SheafOfModules.isFlat_constantFieldModule J κ (P.X n))
  (SheafOfModules.ringed_kFlat_single_tensor_comparison R).choose P hP G ≪≫
    (ConstantCompletion.Q R).mapIso
      ((HomologicalComplex.singleMapHomologicalComplex
        ((SheafOfModules.KFlatFixedTensor.ordinaryTensor R).flip.obj G) (.up ℤ) 0).app F)

section TensorProof

attribute [local instance] Sheaf.monoidalCategory Sheaf.symmetricCategory
attribute [local instance] Functor.CommShift₂.commShiftObj
  Functor.CommShift₂.commShiftFlipObj Functor.CommShift₂.commShift_map

attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall
  ConstantScalarRestriction.fixedSheafify ConstantScalarRestriction.fixedAbelian
  ConstantScalarRestriction.ringAbelian ConstantScalarRestriction.ringPreadditive
  ConstantScalarRestriction.fixedPreadditive ConstantScalarRestriction.ringZeroMorphisms
  ConstantScalarRestriction.fixedZeroMorphisms

private local instance modelAddSheafify {C : Type w} [SmallCategory C]
    (J : GrothendieckTopology C) : HasSheafify J AddCommGrpCat.{w} :=
  GrothendieckTopology.hasSheafify_of_isGrothendieckAbelian J AddCommGrpCat.{w}

private local instance modelSheafify {C : Type w} [SmallCategory C]
    (J : GrothendieckTopology C) (κ : Type w) [Field κ] :
    HasSheafify J (ModuleCat.{w} κ) :=
  GrothendieckTopology.hasSheafify_of_isGrothendieckAbelian J (ModuleCat.{w} κ)

private local instance modelAbelian {C : Type w} [SmallCategory C]
    (J : GrothendieckTopology C) (κ : Type w) [Field κ] :
    Abelian (ConstantCompletion.Mod (ConstantCompletion.constant J κ)) := inferInstance

private local instance modelFixedAbelian {C : Type w} [SmallCategory C]
    (J : GrothendieckTopology C) (κ : Type w) [Field κ] :
    Abelian (Sheaf J (ModuleCat.{w} κ)) := inferInstance

private local instance fixedAdditive {C : Type w} [SmallCategory C]
    (J : GrothendieckTopology C) (κ : Type w) [Field κ] :
    (coefficientModelFixedScalars J κ).Additive := by
  have := coefficientModelFixedScalars_isEquivalence J κ
  exact Functor.additive_of_preserves_binary_products _

private local instance coefficientFixedMonoidal
    {C : Type w} [SmallCategory C] (J : GrothendieckTopology C)
    (A : Type w) [CommRing A] : (coefficientModelFixedScalars J A).Monoidal := by
  letI : (ConstantScalarRestriction.restriction J A).Monoidal :=
    (ConstantScalarRestriction.ordinary J A).braided.toMonoidal
  let i : ConstantScalarRestriction.restriction J A ≅ coefficientModelFixedScalars J A :=
    CategoryTheory.restrictionIso J A
  exact Functor.Monoidal.transport i

private def freeTensorIso (κ : Type w) [Field κ] (r s : ℕ) :
    ModuleCat.of κ (Fin r → κ) ⊗ ModuleCat.of κ (Fin s → κ) ≅
      ModuleCat.of κ (Fin (r * s) → κ) :=
  (((Pi.basisFun κ (Fin r)).tensorProduct (Pi.basisFun κ (Fin s))).equivFun ≪≫ₗ
    LinearEquiv.funCongrLeft κ κ finProdFinEquiv.symm).toModuleIso

private def pullTensorIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    (κ : Type (max v (u + 1))) [Field κ] (F G : Modules.{u, v} Y κ) :
    (coefficientProEtaleFixedModulePullback.{u, v} f κ).obj
        ((coefficientModelFixedScalars _ κ).obj (((ordinary Y κ).obj F).obj G)) ≅
      (coefficientProEtaleFixedModulePullback.{u, v} f κ).obj
        ((coefficientModelFixedScalars _ κ).obj F) ⊗
      (coefficientProEtaleFixedModulePullback.{u, v} f κ).obj
        ((coefficientModelFixedScalars _ κ).obj G) := by
  let J := coefficientProEtaleModelTopology.{u, v} Y
  let K := coefficientProEtaleModelTopology.{u, v} X
  let V := coefficientProEtaleModelBaseChange.{u, v} f
  have : PreservesFiniteLimits V := by
    have : PreservesFiniteLimits
        (AsSmall.down : coefficientProEtaleSiteModel.{u, v} Y ⥤ Y.ProEt) :=
      inferInstanceAs (PreservesFiniteLimits
        (AsSmall.equiv.{u, u + 1, max v (u + 1)} (C := Y.ProEt)).inverse)
    have : PreservesFiniteLimits
        (AsSmall.up : X.ProEt ⥤ coefficientProEtaleSiteModel.{u, v} X) :=
      inferInstanceAs (PreservesFiniteLimits
        (AsSmall.equiv.{u, u + 1, max v (u + 1)} (C := X.ProEt)).functor)
    dsimp only [V, coefficientProEtaleModelBaseChange]
    infer_instance
  let P := coefficientProEtaleFixedModulePullback.{u, v} f κ
  let E := coefficientModelFixedScalars J κ
  have : RepresentablyFlat V := flat_of_preservesFiniteLimits V
  letI (Z : (coefficientProEtaleSiteModel.{u, v} X)ᵒᵖ) :
      IsSifted (CostructuredArrow V.op Z) := inferInstance
  letI : P.Monoidal :=
    Functor.sheafPullbackConstruction.sheafPullbackMonoidal V (ModuleCat κ) J K
  letI : MonoidalCategory (Modules Y κ) := SheafOfModules.monoidalCategory (ring Y κ)
  exact P.mapIso ((Functor.Monoidal.μIso E F G).symm) ≪≫
    (Functor.Monoidal.μIso P (E.obj F) (E.obj G)).symm

private theorem chartTensor {X Y : Scheme.{u}} (f : X ⟶ Y)
    (κ : Type (max v (u + 1))) [Field κ] (F G : Modules.{u, v} Y κ)
    (r s : ℕ)
    (eF : Nonempty ((coefficientProEtaleFixedModulePullback.{u, v} f κ).obj
      ((coefficientModelFixedScalars _ κ).obj F) ≅
      (constantSheaf (coefficientProEtaleModelTopology.{u, v} X) (ModuleCat κ)).obj
        (ModuleCat.of κ (Fin r → κ))))
    (eG : Nonempty ((coefficientProEtaleFixedModulePullback.{u, v} f κ).obj
      ((coefficientModelFixedScalars _ κ).obj G) ≅
      (constantSheaf (coefficientProEtaleModelTopology.{u, v} X) (ModuleCat κ)).obj
        (ModuleCat.of κ (Fin s → κ)))) :
    Nonempty ((coefficientProEtaleFixedModulePullback.{u, v} f κ).obj
      ((coefficientModelFixedScalars _ κ).obj (((ordinary Y κ).obj F).obj G)) ≅
      (constantSheaf (coefficientProEtaleModelTopology.{u, v} X) (ModuleCat κ)).obj
        (ModuleCat.of κ (Fin (r * s) → κ))) := by
  obtain ⟨eF⟩ := eF
  obtain ⟨eG⟩ := eG
  let c := constantSheaf (coefficientProEtaleModelTopology.{u, v} X) (ModuleCat κ)
  exact ⟨pullTensorIso f κ F G ≪≫ tensorIso eF eG ≪≫
    Functor.Monoidal.μIso c _ _ ≪≫ c.mapIso (freeTensorIso κ r s)⟩

private def overTensorIso {C : Type w} [SmallCategory C]
    (J : GrothendieckTopology C) (κ : Type w) [Field κ]
    (F G : Sheaf J (ModuleCat κ)) (U : C) :
    (F ⊗ G).over U ≅ F.over U ⊗ G.over U := by
  let V := J.overPullback (ModuleCat κ) U
  let c := (Over.forget U).pushforwardContinuousSheafificationCompatibility
    (ModuleCat κ) (J.over U) J
  exact V.mapIso ((Sheaf.tensorLeftIso F).app G) ≪≫
    (c.app (F.obj ⊗ G.obj)).symm ≪≫
    (presheafToSheaf (J.over U) (ModuleCat κ)).mapIso
      (NatIso.ofComponents (fun _ ↦ Iso.refl _)) ≪≫
    ((Sheaf.tensorLeftIso (F.over U)).app (G.over U)).symm

private theorem finiteTensor {C : Type w} [SmallCategory C]
    (J : GrothendieckTopology C) (κ : Type w) [Field κ]
    (F G : Sheaf J (ModuleCat κ))
    (hF : IsCoefficientModelLocallyConstantFinite J κ F)
    (hG : IsCoefficientModelLocallyConstantFinite J κ G) :
    IsCoefficientModelLocallyConstantFinite J κ (F ⊗ G) := by
  intro V
  obtain ⟨S, hS, hs⟩ := hF V
  obtain ⟨T, hT, ht⟩ := hG V
  refine ⟨S ⊓ T, J.intersection_covering hS hT, ?_⟩
  intro W f hf
  obtain ⟨M, hM, ⟨eM⟩⟩ := hs W f hf.1
  obtain ⟨N, hN, ⟨eN⟩⟩ := ht W f hf.2
  have := hM
  have := hN
  let c := constantSheaf (J.over W) (ModuleCat κ)
  exact ⟨M ⊗ N, inferInstanceAs (Module.Finite κ (TensorProduct κ M N)),
    ⟨overTensorIso J κ F G W ≪≫ tensorIso eM eN ≪≫
    Functor.Monoidal.μIso c M N⟩⟩

private theorem ordinaryClosure (X : Scheme.{u}) [CompactSpace X] [IsLocallyNoetherian X]
    (κ : Type (max v (u + 1))) [Field κ] (F G : Modules.{u, v} X κ)
    (hF : IsCoefficientAffineLocallyConstructibleProEtaleModuleSheaf X κ F)
    (hG : IsCoefficientAffineLocallyConstructibleProEtaleModuleSheaf X κ G) :
    IsCoefficientAffineLocallyConstructibleProEtaleModuleSheaf X κ
      (((ordinary X κ).obj F).obj G) := by
  have : IsNoetherian X := ⟨⟩
  obtain ⟨S, hcS, hs⟩ := (proEtale_noetherian_global_constructibility X κ F).mp hF
  obtain ⟨T, hcT, ht⟩ := (proEtale_noetherian_global_constructibility X κ G).mp hG
  apply (proEtale_noetherian_global_constructibility X κ _).mpr
  refine ⟨S.inter T, (S.inter T).isConstructible_stratum, ?_⟩
  intro a
  apply (finiteLocalModels_iff_presentation _ κ _).mp
  let i := (finProdFinEquiv.symm a).1
  let j := (finProdFinEquiv.symm a).2
  have hFs := (finiteLocalModels_iff_presentation _ κ _).mpr (hs i)
  have hGt := (finiteLocalModels_iff_presentation _ κ _).mpr (ht j)
  have hF' := ProEtale.coefficientProEtale_finite_comp
    (pullback.fst (S.immersion i) (T.immersion j)) (S.immersion i) κ _ hFs
  have hG' := ProEtale.coefficientProEtale_finite_comp
    (pullback.snd (S.immersion i) (T.immersion j)) (T.immersion j) κ _ hGt
  rw [← pullback.condition] at hG'
  exact ProEtale.coefficientProEtale_finite_iso κ
    (pullTensorIso ((S.inter T).immersion a) κ F G).symm
    (finiteTensor _ κ _ _ hF' hG')

private theorem finiteTypeIso {C : Type w} [SmallCategory C]
    (J : GrothendieckTopology C) (κ : Type w) [Field κ]
    {F G : ringedSiteModules ((constantSheaf J RingCat).obj (RingCat.of κ))}
    (e : F ≅ G) (h : SheafOfModules.IsFiniteTypeLocallyConstant J κ F) :
    SheafOfModules.IsFiniteTypeLocallyConstant J κ G := by
  intro U
  obtain ⟨S, hS, hs⟩ := h U
  refine ⟨S, hS, fun V f hf ↦ ?_⟩
  obtain ⟨M, hM, ⟨i⟩⟩ := hs V f hf
  exact ⟨M, hM, ⟨(SheafOfModules.overFunctor _ V).mapIso e.symm ≪≫ i⟩⟩

private theorem finiteSerre {C : Type w} [SmallCategory C]
    (J : GrothendieckTopology C) (κ : Type w) [Field κ] :
    (∀ (F G : Sheaf J (ModuleCat κ)) (f : F ⟶ G),
      IsCoefficientModelLocallyConstantFinite J κ F →
      IsCoefficientModelLocallyConstantFinite J κ G →
      IsCoefficientModelLocallyConstantFinite J κ (kernel f) ∧
      IsCoefficientModelLocallyConstantFinite J κ (cokernel f)) ∧
    (∀ S : ShortComplex (Sheaf J (ModuleCat κ)), S.ShortExact →
      IsCoefficientModelLocallyConstantFinite J κ S.X₁ →
      IsCoefficientModelLocallyConstantFinite J κ S.X₃ →
      IsCoefficientModelLocallyConstantFinite J κ S.X₂) := by
  obtain ⟨⟨e, he, hae, hai, _⟩, _⟩ := constant_ring_module_sheaves J κ
  let E := e.inverse
  have : E.Additive := hai
  have h (F : Sheaf J (ModuleCat κ)) :
      IsCoefficientModelLocallyConstantFinite J κ F ↔
        SheafOfModules.IsFiniteTypeLocallyConstant J κ (E.obj F) := by
    rw [← ProFiniteModels.fixedModels_constantRing]
    change ProFiniteModels.fixedModels J κ F ↔ _
    rw [← he]
    exact ⟨ProFiniteModels.fixedModels_of_iso J κ (e.counitIso.app F).symm,
      ProFiniteModels.fixedModels_of_iso J κ (e.counitIso.app F)⟩
  obtain ⟨hk, hx⟩ :=
    SheafOfModules.finiteTypeLocallyConstant_closedUnder_kernels_cokernels_extensions J κ
  constructor
  · intro F G f hF hG
    obtain ⟨hK, hC⟩ := hk _ _ (E.map f) ((h F).mp hF) ((h G).mp hG)
    exact ⟨(h _).mpr (finiteTypeIso J κ
      (PreservesKernel.iso E f).symm hK),
      (h _).mpr (finiteTypeIso J κ
        (PreservesCokernel.iso E f).symm hC)⟩
  · intro S hS h₁ h₃
    exact (h _).mpr (hx (S.map E) (hS.map_of_exact E)
      ((h _).mp h₁) ((h _).mp h₃))

private theorem finiteZero {C : Type w} [SmallCategory C]
    (J : GrothendieckTopology C) (κ : Type w) [Field κ]
    (F : Sheaf J (ModuleCat κ)) (hF : IsZero F) :
    IsCoefficientModelLocallyConstantFinite J κ F := by
  intro U
  refine ⟨⊤, J.top_mem U, fun V f _ ↦ ?_⟩
  refine ⟨ModuleCat.of κ (Fin 0 → κ), inferInstance, ⟨?_⟩⟩
  exact ((J.overPullback _ V).map_isZero hF).iso
    ((constantSheaf (J.over V) (ModuleCat κ)).map_isZero
      (ModuleCat.isZero_of_subsingleton _))

private local instance pullbackExact {X Y : Scheme.{u}} (f : X ⟶ Y)
    (κ : Type (max v (u + 1))) [Field κ] :
    PreservesFiniteLimits (coefficientProEtaleFixedModulePullback.{u, v} f κ) := by
  have := ProEtale.model_preserves.{u, v} f
  have : RepresentablyFlat (coefficientProEtaleModelBaseChange.{u, v} f) :=
    flat_of_preservesFiniteLimits _
  have : PreservesFiniteLimits
      ((coefficientProEtaleModelBaseChange.{u, v} f).op.lan :
        _ ⥤ _ ⥤ ModuleCat.{max v (u + 1)} κ) :=
    preservesFiniteLimits_op_lan_of_flat _
  dsimp only [coefficientProEtaleFixedModulePullback]
  infer_instance

private local instance pullbackColimits {X Y : Scheme.{u}} (f : X ⟶ Y)
    (κ : Type (max v (u + 1))) [Field κ] :
    PreservesFiniteColimits (coefficientProEtaleFixedModulePullback.{u, v} f κ) := by
  have : (coefficientProEtaleFixedModulePullback.{u, v} f κ).IsLeftAdjoint :=
    (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
      (coefficientProEtaleModelBaseChange.{u, v} f) (ModuleCat.{max v (u + 1)} κ)
      _ _).isLeftAdjoint
  infer_instance

private local instance pullbackAdditive {X Y : Scheme.{u}} (f : X ⟶ Y)
    (κ : Type (max v (u + 1))) [Field κ] :
    (coefficientProEtaleFixedModulePullback.{u, v} f κ).Additive :=
  Functor.additive_of_preserves_binary_products _

private theorem commonStrata (X : Scheme.{u}) [IsNoetherian X]
    (κ : Type (max v (u + 1))) [Field κ] (F G : Modules.{u, v} X κ)
    (hF : IsCoefficientAffineLocallyConstructibleProEtaleModuleSheaf X κ F)
    (hG : IsCoefficientAffineLocallyConstructibleProEtaleModuleSheaf X κ G) :
    ∃ S : Stratification X, ∀ i : Fin S.n,
      IsCoefficientModelLocallyConstantFinite _ κ
        ((coefficientProEtaleFixedModulePullback (S.immersion i) κ).obj
          ((coefficientModelFixedScalars _ κ).obj F)) ∧
      IsCoefficientModelLocallyConstantFinite _ κ
        ((coefficientProEtaleFixedModulePullback (S.immersion i) κ).obj
          ((coefficientModelFixedScalars _ κ).obj G)) := by
  obtain ⟨S, _, hs⟩ := (proEtale_noetherian_global_constructibility X κ F).mp hF
  obtain ⟨T, _, ht⟩ := (proEtale_noetherian_global_constructibility X κ G).mp hG
  refine ⟨S.inter T, fun a ↦ ?_⟩
  let i := (finProdFinEquiv.symm a).1
  let j := (finProdFinEquiv.symm a).2
  have hF' := ProEtale.coefficientProEtale_finite_comp
    (pullback.fst (S.immersion i) (T.immersion j)) (S.immersion i) κ _
    ((finiteLocalModels_iff_presentation _ κ _).mpr (hs i))
  have hG' := ProEtale.coefficientProEtale_finite_comp
    (pullback.snd (S.immersion i) (T.immersion j)) (T.immersion j) κ _
    ((finiteLocalModels_iff_presentation _ κ _).mpr (ht j))
  rw [← pullback.condition] at hG'
  exact ⟨hF', hG'⟩

private theorem constructibleZero (X : Scheme.{u}) [IsNoetherian X]
    (κ : Type (max v (u + 1))) [Field κ] (F : Modules.{u, v} X κ) (hF : IsZero F) :
    IsCoefficientAffineLocallyConstructibleProEtaleModuleSheaf X κ F := by
  have := coefficientModelFixedScalars_isEquivalence
    (coefficientProEtaleModelTopology.{u, v} X) κ
  apply (proEtale_noetherian_global_constructibility X κ F).mpr
  refine ⟨Stratification.trivial X, (Stratification.trivial X).isConstructible_stratum,
    fun i ↦ (finiteLocalModels_iff_presentation _ κ _).mp ?_⟩
  exact finiteZero _ κ _
    ((coefficientProEtaleFixedModulePullback _ κ).map_isZero
      ((coefficientModelFixedScalars _ κ).map_isZero hF))

private theorem constructibleSerre (X : Scheme.{u}) [IsNoetherian X]
    (κ : Type (max v (u + 1))) [Field κ] :
    (∀ (F G : Modules.{u, v} X κ) (f : F ⟶ G),
      IsCoefficientAffineLocallyConstructibleProEtaleModuleSheaf.{u, v} X κ F →
      IsCoefficientAffineLocallyConstructibleProEtaleModuleSheaf.{u, v} X κ G →
      IsCoefficientAffineLocallyConstructibleProEtaleModuleSheaf.{u, v} X κ (kernel f) ∧
      IsCoefficientAffineLocallyConstructibleProEtaleModuleSheaf.{u, v} X κ (cokernel f)) ∧
    (∀ S : ShortComplex (Modules.{u, v} X κ), S.ShortExact →
      IsCoefficientAffineLocallyConstructibleProEtaleModuleSheaf.{u, v} X κ S.X₁ →
      IsCoefficientAffineLocallyConstructibleProEtaleModuleSheaf.{u, v} X κ S.X₃ →
      IsCoefficientAffineLocallyConstructibleProEtaleModuleSheaf.{u, v} X κ S.X₂) := by
  let E := coefficientModelFixedScalars (coefficientProEtaleModelTopology.{u, v} X) κ
  have : E.IsEquivalence := coefficientModelFixedScalars_isEquivalence _ κ
  have : E.Additive := Functor.additive_of_preserves_binary_products E
  constructor
  · intro F G f hF hG
    obtain ⟨S, hs⟩ := commonStrata X κ F G hF hG
    constructor
    all_goals
      apply (proEtale_noetherian_global_constructibility X κ _).mpr
      refine ⟨S, S.isConstructible_stratum, fun i ↦ ?_⟩
      apply (finiteLocalModels_iff_presentation _ κ _).mp
      let L := E ⋙ coefficientProEtaleFixedModulePullback.{u, v} (S.immersion i) κ
      obtain ⟨hK, hC⟩ := (finiteSerre _ κ).1 _ _ (L.map f) (hs i).1 (hs i).2
      first
      | exact ProEtale.coefficientProEtale_finite_iso κ
          (PreservesKernel.iso L f).symm hK
      | exact ProEtale.coefficientProEtale_finite_iso κ
          (PreservesCokernel.iso L f).symm hC
  · intro S hS h₁ h₃
    obtain ⟨T, ht⟩ := commonStrata X κ S.X₁ S.X₃ h₁ h₃
    apply (proEtale_noetherian_global_constructibility X κ _).mpr
    refine ⟨T, T.isConstructible_stratum, fun i ↦ ?_⟩
    apply (finiteLocalModels_iff_presentation _ κ _).mp
    let L := E ⋙ coefficientProEtaleFixedModulePullback.{u, v} (T.immersion i) κ
    exact (finiteSerre _ κ).2 (S.map L) (hS.map_of_exact L) (ht i).1 (ht i).2

open CategoryTheory.Pretriangulated in
private theorem postnikovInduction
    {M : Type w} [Category M] [Abelian M] [HasDerivedCategory M]
    (P : ObjectProperty (DerivedCategory M))
    [P.IsClosedUnderIsomorphisms] [P.ContainsZero] [P.IsTriangulatedClosed₂]
    (K : DerivedCategory M) (a b : ℤ)
    (ha : K.IsGE a) (hb : K.IsLE b) (hab : a ≤ b)
    (hlayer : ∀ q : ℤ, a ≤ q → q ≤ b →
      P (((DerivedCategory.singleFunctor M 0).obj
        ((DerivedCategory.homologyFunctor M q).obj K))⟦-q⟧)) : P K := by
  let n := (b - a + 1).toNat
  have hn : a + (n : ℤ) - 1 = b := by dsimp [n]; omega
  have : K.IsLE (a + (n : ℤ) - 1) := hn ▸ hb
  obtain ⟨_, L, ⟨e₀⟩, ⟨en⟩, _, f, g, δ, hT⟩ :=
    CategoryTheory.Triangulated.TStructure.exists_bounded_postnikov_tower
      (DerivedCategory.TStructure.t (C := M)) a n K
  have hL : ∀ j : Fin (n + 1), P (L j) := by
    intro j
    induction j using Fin.induction with
    | zero => exact P.prop_of_isZero ((isZero_zero _).of_iso e₀)
    | succ j ih =>
      apply P.ext_of_isTriangulatedClosed₂ _ (hT j) ih
      obtain ⟨e⟩ := DerivedCategory.bounded_postnikov_cohomology_iso K (a + (j : ℤ))
      apply P.prop_of_iso ((shiftFunctor _ (-(a + (j : ℤ)))).mapIso e).symm
      apply hlayer
      · omega
      · have := j.isLt; omega
  exact P.prop_of_iso en (hL (Fin.last n))

private def homologyWindow {M : Type w} [Category M] [Abelian M]
    [HasDerivedCategory M] (P : ObjectProperty M) (a b : ℤ) :
    ObjectProperty (DerivedCategory M) :=
  fun K ↦ DerivedCategory.homologyProperty P K ∧
    ∀ n : ℤ, n < a ∨ b < n → IsZero ((DerivedCategory.homologyFunctor M n).obj K)

private local instance windowIso {M : Type w} [Category M] [Abelian M]
    [HasDerivedCategory M] (P : ObjectProperty M) [P.IsClosedUnderIsomorphisms] (a b : ℤ) :
    (homologyWindow P a b).IsClosedUnderIsomorphisms where
  of_iso e h := ⟨(DerivedCategory.homologyProperty P).prop_of_iso e h.1,
    fun n hn ↦ (h.2 n hn).of_iso ((DerivedCategory.homologyFunctor M n).mapIso e).symm⟩

private local instance windowZero {M : Type w} [Category M] [Abelian M]
    [HasDerivedCategory M] (P : ObjectProperty M) [P.IsClosedUnderIsomorphisms]
    [P.ContainsZero] (a b : ℤ) : (homologyWindow P a b).ContainsZero where
  exists_zero := ⟨0, isZero_zero _,
    (DerivedCategory.homologyProperty P).prop_of_isZero (isZero_zero _),
    fun n _ ↦ (DerivedCategory.homologyFunctor M n).map_isZero (isZero_zero _)⟩

private local instance windowExtensions {M : Type w} [Category M] [Abelian M]
    [HasDerivedCategory M] (P : ObjectProperty M) [P.IsClosedUnderIsomorphisms]
    [P.IsClosedUnderKernels] [P.IsClosedUnderCokernels] [P.IsClosedUnderExtensions]
    (a b : ℤ) : (homologyWindow P a b).IsTriangulatedClosed₂ :=
  .mk' (fun T hT h₁ h₃ ↦
    ⟨(DerivedCategory.homologyProperty P).ext_of_isTriangulatedClosed₂ T hT h₁.1 h₃.1,
      fun n hn ↦
        ((DerivedCategory.homologyFunctor M 0).homologySequence_exact₂ T hT n).isZero_of_both_isZero
          (h₁.2 n hn) (h₃.2 n hn)⟩)

private theorem windowShift {M : Type w} [Category M] [Abelian M]
    [HasDerivedCategory M] (P : ObjectProperty M) [P.IsClosedUnderIsomorphisms]
    {K : DerivedCategory M} {a b c d q : ℤ}
    (hK : homologyWindow P a b K) (hc : c ≤ a + q) (hd : b + q ≤ d) :
    homologyWindow P c d (K⟦-q⟧) := by
  refine ⟨(DerivedCategory.homologyProperty P).le_shift _ _ hK.1, ?_⟩
  intro n hn
  let e := ((DerivedCategory.homologyFunctor M 0).shiftIso (-q) n (-q + n) rfl).app K
  exact (hK.2 (-q + n) (by omega)).of_iso e

private theorem tensorFromSingles {M : Type w} [Category M] [Abelian M]
    [HasDerivedCategory M] (P : ObjectProperty M)
    [P.IsClosedUnderIsomorphisms] [P.ContainsZero]
    [P.IsClosedUnderKernels] [P.IsClosedUnderCokernels] [P.IsClosedUnderExtensions]
    (T : DerivedCategory M ⥤ DerivedCategory M ⥤ DerivedCategory M)
    [T.CommShift₂Int]
    (A B : DerivedCategory M) (a b c d : ℤ) (hc : c ≤ d)
    [((T.obj A)).IsTriangulated]
    (hB : homologyWindow P c d B)
    (hsingle : ∀ L : M, P L →
      homologyWindow P a b ((T.obj A).obj ((DerivedCategory.singleFunctor M 0).obj L))) :
    homologyWindow P (a + c) (b + d) ((T.obj A).obj B) := by
  let F := T.obj A
  let Q := (homologyWindow P (a + c) (b + d)).inverseImage F
  have : Q.IsClosedUnderIsomorphisms := inferInstance
  have : Q.ContainsZero := inferInstance
  have : Q.IsTriangulatedClosed₂ := .mk' (fun E hE h₁ h₃ ↦
    (homologyWindow P (a + c) (b + d)).ext_of_isTriangulatedClosed₂
      (F.mapTriangle.obj E) (F.map_distinguished E hE) h₁ h₃)
  apply postnikovInduction Q B c d
    ((DerivedCategory.isGE_iff B c).mpr (fun n hn ↦ hB.2 n (Or.inl hn)))
    ((DerivedCategory.isLE_iff B d).mpr (fun n hn ↦ hB.2 n (Or.inr hn))) hc
  intro q hq₁ hq₂
  change homologyWindow P (a + c) (b + d) (F.obj _)
  apply (homologyWindow P (a + c) (b + d)).prop_of_iso
    ((F.commShiftIso (-q)).app _).symm
  exact windowShift P (hsingle _ (hB.1 q)) (by omega) (by omega)

private local instance standardDerived {C : Type w} [SmallCategory C]
    (J : GrothendieckTopology C) (κ : Type w) [Field κ] :
    HasDerivedCategory (ConstantCompletion.Mod (ConstantCompletion.constant J κ)) :=
  HasDerivedCategory.standard _

private theorem fieldTensorWindow {C : Type w} [SmallCategory C]
    (J : GrothendieckTopology C) (κ : Type w) [Field κ]
    (P : ObjectProperty (ConstantCompletion.Mod (ConstantCompletion.constant J κ)))
    [P.IsClosedUnderIsomorphisms] [P.ContainsZero]
    [P.IsClosedUnderKernels] [P.IsClosedUnderCokernels] [P.IsClosedUnderExtensions]
    (hprod : ∀ F G, P F → P G →
      P (((SheafOfModules.KFlatFixedTensor.ordinaryTensor
        (ConstantCompletion.constant J κ)).obj F).obj G))
    (A B : ConstantCompletion.D (ConstantCompletion.constant J κ)) (a b c d : ℤ)
    (hA : homologyWindow P a b A) (hB : homologyWindow P c d B) :
    homologyWindow P (a + c) (b + d)
      (((tensor (ConstantCompletion.constant J κ)).obj A).obj B) := by
  let R := ConstantCompletion.constant J κ
  let M := ConstantCompletion.Mod R
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.symmetricCategory R
  let := HasDerivedCategory.standard M
  let T : DerivedCategory M ⥤ DerivedCategory M ⥤ DerivedCategory M :=
    SheafOfModules.KFlatFixedTensor.derivedTensor R
  obtain ⟨s, hs⟩ := SheafOfModules.KFlatFixedTensor.kFlat_fixed_tensor_triangulated R
  let : T.CommShift₂Int := s
  have htri (K : DerivedCategory M) : (T.obj K).IsTriangulated := by
    obtain ⟨E, p, hk, hf, hp, _⟩ :=
      CochainComplex.exists_isKFlatResolutionIndependentCoefficients
        (DerivedCategory.Q.objPreimage K)
    have := hp
    let e : DerivedCategory.Q.obj E ≅ K :=
      asIso (DerivedCategory.Q.map p) ≪≫ DerivedCategory.Q.objObjPreimageIso K
    have : (T.obj (DerivedCategory.Q.obj E)).IsTriangulated :=
      (hs E hk (fun n ↦ (CategoryTheory.exactFunctor _ _).prop_of_iso
        (SheafOfModules.siteSheafTensorRightIso R _).symm (hf n))).2.2.1.1
    have : NatTrans.CommShift (T.mapIso e).hom ℤ := by
      change NatTrans.CommShift (T.map e.hom) ℤ
      exact Functor.CommShift₂.commShift_map e.hom
    exact Functor.isTriangulated_of_iso (T.mapIso e)
  have : (T.obj A).IsTriangulated := htri A
  by_cases hcd : c ≤ d
  · apply tensorFromSingles P T A B a b c d hcd hB
    intro L hL
    obtain ⟨_, _, _, gamma, _⟩ :=
      SheafOfModules.FlatSingleTensor.ringed_flat_single_tensor_cohomology R
    have flat := SheafOfModules.isFlat_constantFieldModule J κ L
    have e (n : ℤ) := (gamma L flat n).app A
    refine ⟨fun n ↦ P.prop_of_iso (e n).symm (hprod _ L (hA.1 n) hL), ?_⟩
    intro n hn
    exact ((MonoidalCategory.tensorRight L).map_isZero (hA.2 n hn)).of_iso (e n)
  · have hz : IsZero B := (DerivedCategory.isZero_iff B).mpr (fun n ↦
      hB.2 n (by omega))
    exact (homologyWindow P (a + c) (b + d)).prop_of_isZero
      ((T.obj A).map_isZero hz)

private theorem mainDerived (X : Scheme.{u}) [CompactSpace X] [IsLocallyNoetherian X]
    (κ : Type (max v (u + 1))) [Field κ]
    (A B : D.{u, v} X κ)
    (hA : ProEtale.coefficientBoundedConstructibleProEtale X κ A)
    (hB : ProEtale.coefficientBoundedConstructibleProEtale X κ B) :
    ProEtale.coefficientBoundedConstructibleProEtale X κ
      (((tensor (ring X κ)).obj A).obj B) ∧
    ∀ a b c d : ℤ,
      (∀ n : ℤ, n < a ∨ b < n →
        IsZero ((coefficientModelCohomology (ring X κ) n).obj A)) →
      (∀ n : ℤ, n < c ∨ d < n →
        IsZero ((coefficientModelCohomology (ring X κ) n).obj B)) →
      ∀ n : ℤ, n < a + c ∨ b + d < n →
        IsZero ((coefficientModelCohomology (ring X κ) n).obj
          (((tensor (ring X κ)).obj A).obj B)) := by
  have : IsNoetherian X := ⟨⟩
  let := HasDerivedCategory.standard (Modules X κ)
  let P : ObjectProperty (Modules X κ) :=
    IsCoefficientAffineLocallyConstructibleProEtaleModuleSheaf.{u, v} X κ
  have : P.IsClosedUnderIsomorphisms := ⟨fun e h ↦
    ProEtale.coefficientProEtale_constructible_of_iso X κ e h⟩
  have : P.ContainsZero := ⟨⟨0, isZero_zero _, constructibleZero X κ _ (isZero_zero _)⟩⟩
  obtain ⟨hk, hx⟩ := constructibleSerre X κ
  have : P.IsClosedUnderKernels := ⟨by
    rintro _ ⟨f, k, h, hfg⟩
    exact P.prop_of_iso (h.conePointUniqueUpToIso (kernelIsKernel f)).symm
      (hk _ _ f hfg.1 hfg.2).1⟩
  have : P.IsClosedUnderCokernels := ⟨by
    rintro _ ⟨f, k, h, hfg⟩
    exact P.prop_of_iso (h.coconePointUniqueUpToIso (cokernelIsCokernel f)).symm
      (hk _ _ f hfg.1 hfg.2).2⟩
  have : P.IsClosedUnderExtensions := ⟨fun h h₁ h₃ ↦ hx _ h h₁ h₃⟩
  have ht (a b c d : ℤ)
      (ha : ∀ n : ℤ, n < a ∨ b < n →
        IsZero ((coefficientModelCohomology (ring X κ) n).obj A))
      (hb : ∀ n : ℤ, n < c ∨ d < n →
        IsZero ((coefficientModelCohomology (ring X κ) n).obj B)) :=
    fieldTensorWindow (coefficientProEtaleModelTopology.{u, v} X) κ P
      (ordinaryClosure X κ) A B a b c d ⟨hA.1, ha⟩ ⟨hB.1, hb⟩
  constructor
  · obtain ⟨a, b, hab, ha⟩ := hA.2
    obtain ⟨c, d, hcd, hb⟩ := hB.2
    exact ⟨(ht a b c d ha hb).1, a + c, b + d, by omega, (ht a b c d ha hb).2⟩
  · intro a b c d ha hb
    exact (ht a b c d ha hb).2

end TensorProof

/-- Tensor closure, the canonical degree-zero comparison, the chart rank product and the
sum of cohomological support intervals, for an arbitrary constant field on a Noetherian
scheme. The rank implication tests every pro-etale chart over every stratum, hence every
member of every common trivializing cover of every common refinement.

Source: blueprint main-20261015, det-lem-int-tensor-product.proof.md, third paragraph;
Stacks Tags 03ET and 06YU (blueprint: lem-sfb-field-bounded-constructible-tensor).

Proof:
1. Intersect the global stratifications and their local constant trivializing covers.
Constant scalar restriction, fixed-coefficient pullback and slice restriction commute
with tensor. The tensor-product basis gives the asserted rank product on every chart.
2. The existing singleComparison computes degree-zero derived tensor, using field
flatness, bounded-flat K-flatness and the normalized single-tensor comparison.
3. Transport finite locally constant weak Serre closure through the constant-ring module
equivalence on the coefficient-sized site. Exact stratum pullback and common refinement
then give weak Serre closure for the global constructibility predicate.
4. Flat-single tensor cohomology identifies H^n(A tensor L[0]) with H^n(A) tensor L.
A flat-term K-flat resolution gives exactness and shifts for tensor by arbitrary A.
5. Induct along B's finite Postnikov tower. Its q-th tensor layer is supported in
[a+q,b+q], hence [a+c,b+d]. Homology exactness propagates constructibility and these bounds.
An empty interval for B makes B zero; the argument also allows an empty interval for A.
No finiteness of the field, nonempty-stratum hypothesis or characteristic condition is used.
-/
theorem field_bounded_constructible_tensor (X : Scheme.{u})
    [CompactSpace X] [IsLocallyNoetherian X]
    (κ : Type (max v (u + 1))) [Field κ] :
    (∀ F G : Modules.{u, v} X κ,
      IsCoefficientAffineLocallyConstructibleProEtaleModuleSheaf.{u, v} X κ F →
      IsCoefficientAffineLocallyConstructibleProEtaleModuleSheaf.{u, v} X κ G →
      IsCoefficientAffineLocallyConstructibleProEtaleModuleSheaf.{u, v} X κ
        (((ordinary.{u, v} X κ).obj F).obj G) ∧
      ∀ (S : Stratification X) (i : Fin S.n)
        (T : Scheme.{u}) (f : T ⟶ S.domain i) [WeaklyEtale f] (r s : ℕ),
        Nonempty ((coefficientProEtaleFixedModulePullback.{u, v} (f ≫ S.immersion i) κ).obj
            ((coefficientModelFixedScalars _ κ).obj F) ≅
          (constantSheaf (coefficientProEtaleModelTopology.{u, v} T) (ModuleCat κ)).obj
            (ModuleCat.of κ (Fin r → κ))) →
        Nonempty ((coefficientProEtaleFixedModulePullback.{u, v} (f ≫ S.immersion i) κ).obj
            ((coefficientModelFixedScalars _ κ).obj G) ≅
          (constantSheaf (coefficientProEtaleModelTopology.{u, v} T) (ModuleCat κ)).obj
            (ModuleCat.of κ (Fin s → κ))) →
        Nonempty ((coefficientProEtaleFixedModulePullback.{u, v} (f ≫ S.immersion i) κ).obj
            ((coefficientModelFixedScalars _ κ).obj (((ordinary.{u, v} X κ).obj F).obj G)) ≅
          (constantSheaf (coefficientProEtaleModelTopology.{u, v} T) (ModuleCat κ)).obj
            (ModuleCat.of κ (Fin (r * s) → κ)))) ∧
    (∀ A B : D.{u, v} X κ,
      ProEtale.coefficientBoundedConstructibleProEtale.{u, v} X κ A →
      ProEtale.coefficientBoundedConstructibleProEtale.{u, v} X κ B →
      ProEtale.coefficientBoundedConstructibleProEtale.{u, v} X κ
        (((tensor (ring.{u, v} X κ)).obj A).obj B) ∧
      ∀ a b c d : ℤ,
        (∀ n : ℤ, n < a ∨ b < n →
          IsZero ((coefficientModelCohomology (ring.{u, v} X κ) n).obj A)) →
        (∀ n : ℤ, n < c ∨ d < n →
          IsZero ((coefficientModelCohomology (ring.{u, v} X κ) n).obj B)) →
        ∀ n : ℤ, n < a + c ∨ b + d < n →
          IsZero ((coefficientModelCohomology (ring.{u, v} X κ) n).obj
            (((tensor (ring.{u, v} X κ)).obj A).obj B))) := by
  constructor
  · intro F G hF hG
    refine ⟨ordinaryClosure X κ F G hF hG, ?_⟩
    intro S i T f _ r s hF' hG'
    exact chartTensor (f ≫ S.immersion i) κ F G r s hF' hG'
  · exact mainDerived X κ

end AlgebraicGeometry.Scheme.FieldConstructibleTensor
