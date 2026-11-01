/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.TraceFormula.PointFiberFunctor
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.MonoidalModule
public import WeilConjectures.AlgebraicGeometry.Finite.Constant.FiniteConstantLocalModel
public import WeilConjectures.CategoryTheory.DerivedCategory.Point.PointFdComplexes
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.ProfiniteFiniteConstantLocalModel
public import WeilConjectures.AlgebraicGeometry.CoefficientBoundedConstructibleProEtale
public import WeilConjectures.Algebra.Homology.ModuleHomComplex
public import Mathlib.Algebra.Module.Projective
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import WeilConjectures.CategoryTheory.Abelian.Flat.ModuleCat
public import WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategory
public import Mathlib.Algebra.Homology.DerivedCategory.KProjective
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
public import Mathlib.Algebra.Category.Grp.EpiMono
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.DualizableCriterion
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.ModuleEmbedding.GabrielPopescu
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import WeilConjectures.CategoryTheory.DerivedCategory.Adjunction

import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficients
import WeilConjectures.SixFunctors.Supporting.ProjectiveCohomologySplitModel
import Mathlib.Algebra.Homology.BifunctorShift
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.CategoryTheory.Ringed.Site.RingedSiteDualityMaps
import WeilConjectures.Algebra.Homology.DerivedInternalHom
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
import Mathlib.Data.Int.Interval
import WeilConjectures.CategoryTheory.Ringed.Site.RingedSiteBoundedFreeRHomMapQuasiIso
import WeilConjectures.Algebra.Homology.HomComplex
import WeilConjectures.Algebra.Homology.HomComplexProjections
import Mathlib.CategoryTheory.Preadditive.Biproducts
import WeilConjectures.AlgebraicGeometry.GeometricFieldProEtaleEvaluation
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import WeilConjectures.AlgebraicGeometry.ProEtale.Clopen.ProEtaleClopenRingedModuleGluing
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Mathlib.Algebra.Module.Projective
import Mathlib.CategoryTheory.Sites.LocallySurjective
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedPointDualComparisonAssertions
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedPointDualComparisonCanonical
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedPointDualComparisonData
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedPointDualComparisonDuality

/-! # Condensed point evaluation and derived dual comparison

Source: blueprint, lem-a1-local-boundary-duality.proof.md, Step 5
(blueprint: lem-a1-condensed-point-dual-comparison).

Main definitions: `condensedBoundaryFiber`, `condensedPointScalarExtension`,
`condensedBoundaryDualComparison`, and `condensedBoundaryReparametrization`.
Main statement: `condensed_point_dual_comparison`.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj TensorProduct

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k] [IsAlgClosed k]
  (I : Type w) [Finite I]

/-- The finite geometric boundary. Source: blueprint Step 5
(blueprint: lem-a1-condensed-point-dual-comparison). -/
def condensedPointBoundary : Scheme.{u} := ∐ fun _ : I ↦ (point k).left

/-- Its ordinary coefficient-module category. Source: blueprint Step 5
(blueprint: lem-a1-condensed-point-dual-comparison). -/
abbrev CondensedBoundaryMod :=
  Mod (Sheaf (Scheme.ProEt.topology (condensedPointBoundary k I)) Ab.{u + 1})
    (condensedRingObj (Profinite.padicAlgClRingObj ℓ) (condensedPointBoundary k I))

/-- The actual exact component restriction, with its point-module target made explicit.
Source: blueprint Step 5, restriction to a geometric component
(blueprint: lem-a1-condensed-point-dual-comparison). -/
def condensedBoundaryRestriction (t : I) : CondensedBoundaryMod ℓ k I ⥤ PointMod ℓ k :=
  upperStar (Profinite.padicAlgClRingObj ℓ) (Sigma.ι (fun _ : I ↦ (point k).left) t)

/-- Restriction followed by sections at a component. Source: blueprint Step 5
(blueprint: lem-a1-condensed-point-dual-comparison). -/
def condensedBoundarySections (t : I) :
    CondensedBoundaryMod ℓ k I ⥤ ModuleCat.{u + 1} (ULift.{u + 1} (PadicAlgCl ℓ)) :=
  condensedBoundaryRestriction ℓ k I t ⋙
    pointSections ℓ k

/-- Termwise derived component evaluation. Source: blueprint Step 5
(blueprint: lem-a1-condensed-point-dual-comparison). -/
def condensedBoundaryFiber (t : I) :
    DerivedCategory (CondensedBoundaryMod ℓ k I) ⥤
      DerivedCategory (ModuleCat.{u + 1} (ULift.{u + 1} (PadicAlgCl ℓ))) :=
  (condensedBoundarySections ℓ k I t).mapDerivedCategory

/-- The scalar-extension functor V ↦ R_s ⊗_Λ V. It is the usual copower tensor
construction: extend the scalars acting on the regular module, then tensor with that
module using the tensor--coyoneda adjunction. Source: blueprint Step 5, scalar extension
(blueprint: lem-a1-condensed-point-dual-comparison). -/
abbrev condensedPointScalarExtension :
    ModuleCat.{u + 1} (ULift.{u + 1} (PadicAlgCl ℓ)) ⥤ PointMod ℓ k :=
  ModuleCat.extendScalars (pointScalarsOp ℓ k) ⋙
    IsGrothendieckAbelian.tensorObj (𝟙_ (PointMod ℓ k))

/-- The scalar-extension/sections adjunction, with its actual copower construction.
Source: blueprint Step 5, scalar extension
(blueprint: lem-a1-condensed-point-dual-comparison). -/
def condensedPointScalarAdjunction :
    condensedPointScalarExtension ℓ k ⊣ pointSections ℓ k :=
  (ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u + 1} (pointScalarsOp ℓ k)).comp
    (IsGrothendieckAbelian.tensorObjPreadditiveCoyonedaObjAdjunction
      (𝟙_ (PointMod ℓ k)))

/-- The tensor data of restriction and evaluation; the theorem below requires their
section and complex normalizations, so these are not unspecified comparison maps.
Source: blueprint Step 5, evaluation comparison
(blueprint: lem-a1-condensed-point-dual-comparison). -/
class CondensedBoundaryEvaluationTensor where
  sections : ∀ t : I, (condensedBoundarySections ℓ k I t).LaxMonoidal
  fiber : ∀ t : I, (condensedBoundaryFiber ℓ k I t).LaxMonoidal
  unit : ∀ t : I, (condensedBoundaryFiber ℓ k I t).obj (𝟙_ _) ≅ 𝟙_ _

/-- The degree-zero unit map used to normalize derived evaluation.
Source: blueprint Step 5, sections of the coefficient ring
(blueprint: lem-a1-condensed-point-dual-comparison). -/
def condensedBoundaryComplexUnit [CondensedBoundaryEvaluationTensor ℓ k I] (t : I) :
    𝟙_ (CochainComplex (ModuleCat.{u + 1} (ULift.{u + 1} (PadicAlgCl ℓ))) ℤ) ⟶
      ((condensedBoundarySections ℓ k I t).mapHomologicalComplex (.up ℤ)).obj
        (𝟙_ (CochainComplex (CondensedBoundaryMod ℓ k I) ℤ)) :=
  (CochainComplex.singleFunctor _ 0).map
      (Functor.LaxMonoidal.ε (condensedBoundarySections ℓ k I t)) ≫
    (HomologicalComplex.singleMapHomologicalComplex
      (condensedBoundarySections ℓ k I t) (.up ℤ) 0).inv.app (𝟙_ _)

/- The tensor data are precisely section tensor and its termwise descent through the
ordinary derived localization. The formula on every total-tensor summand fixes the
normalization, including all shifts and their Koszul signs.
Source: blueprint Step 5, canonical comparison
(blueprint: lem-a1-condensed-point-dual-comparison). -/
/-- A point section, viewed as the corresponding morphism from the regular module.
This is the identity on the Hom set defining the published point sections functor.
Source: blueprint Step 5, section evaluation
(blueprint: lem-a1-condensed-point-dual-comparison). -/
def condensedPointSectionHom (M : PointMod ℓ k) (x : (pointSections ℓ k).obj M) :
    𝟙_ (PointMod ℓ k) ⟶ M := x

/-- A component section, viewed as the corresponding morphism from the regular module.
This is the identity on the underlying Hom set in the published sections functor.
Source: blueprint Step 5, section evaluation
(blueprint: lem-a1-condensed-point-dual-comparison). -/
def condensedBoundarySectionHom (t : I) (M : CondensedBoundaryMod ℓ k I)
    (x : (condensedBoundarySections ℓ k I t).obj M) :
    𝟙_ (PointMod ℓ k) ⟶
      (condensedBoundaryRestriction ℓ k I t).obj M :=
  condensedPointSectionHom ℓ k ((condensedBoundaryRestriction ℓ k I t).obj M) x

/-- The section of the coefficient ring obtained by applying the tensor unit map to 1.
Source: blueprint Step 5, unit normalization
(blueprint: lem-a1-condensed-point-dual-comparison). -/
def condensedBoundaryUnitSection [CondensedBoundaryEvaluationTensor ℓ k I] (t : I) :
    𝟙_ (PointMod ℓ k) ⟶
      (condensedBoundaryRestriction ℓ k I t).obj (𝟙_ _) :=
  condensedBoundarySectionHom ℓ k I t (𝟙_ _)
    ((Functor.LaxMonoidal.ε (condensedBoundarySections ℓ k I t)).hom
      (1 : ULift.{u + 1} (PadicAlgCl ℓ)))

/-- The sections unit clause of the canonical finite-boundary comparison.
Source: blueprint Step 5 and its Frobenius paragraph
(blueprint: lem-a1-condensed-point-dual-comparison). -/
def CondensedBoundarySectionsUnitNormalization
    [s : CondensedBoundaryEvaluationTensor ℓ k I] : Prop :=
  ∀ t : I, condensedBoundaryUnitSection ℓ k I t =
    Functor.LaxMonoidal.ε (condensedBoundaryRestriction ℓ k I t)

/-- The sections tensor clause of the canonical finite-boundary comparison.
Source: blueprint Step 5 and its Frobenius paragraph
(blueprint: lem-a1-condensed-point-dual-comparison). -/
def CondensedBoundarySectionsTensorNormalization
    [s : CondensedBoundaryEvaluationTensor ℓ k I] : Prop :=
  ∀ (t : I) (A B : CondensedBoundaryMod ℓ k I)
    (x : (condensedBoundarySections ℓ k I t).obj A)
    (y : (condensedBoundarySections ℓ k I t).obj B),
    condensedBoundarySectionHom ℓ k I t (A ⊗ B)
        ((Functor.LaxMonoidal.μ (condensedBoundarySections ℓ k I t) A B).hom
          (x ⊗ₜ[ULift.{u + 1} (PadicAlgCl ℓ)] y)) =
      (λ_ (𝟙_ (PointMod ℓ k))).inv ≫
        (condensedBoundarySectionHom ℓ k I t A x ⊗ₘ
          condensedBoundarySectionHom ℓ k I t B y) ≫
        Functor.LaxMonoidal.μ (condensedBoundaryRestriction ℓ k I t) A B

/-- The fiber unit clause of the canonical finite-boundary comparison.
Source: blueprint Step 5 and its Frobenius paragraph
(blueprint: lem-a1-condensed-point-dual-comparison). -/
def CondensedBoundaryFiberUnitNormalization
    [s : CondensedBoundaryEvaluationTensor ℓ k I] : Prop :=
  ∀ t : I, Functor.LaxMonoidal.ε (condensedBoundaryFiber ℓ k I t) = (s.unit t).inv

/-- The complex unit clause of the canonical finite-boundary comparison.
Source: blueprint Step 5 and its Frobenius paragraph
(blueprint: lem-a1-condensed-point-dual-comparison). -/
def CondensedBoundaryComplexUnitNormalization
    [s : CondensedBoundaryEvaluationTensor ℓ k I] : Prop :=
  ∀ t : I, (s.unit t).inv ≫
      (condensedBoundaryFiber ℓ k I t).map (Functor.LaxMonoidal.ε DerivedCategory.Q) ≫
      (condensedBoundarySections ℓ k I t).mapDerivedCategoryFactors.hom.app (𝟙_ _) =
    Functor.LaxMonoidal.ε DerivedCategory.Q ≫
      DerivedCategory.Q.map (condensedBoundaryComplexUnit ℓ k I t)

/-- The complex tensor clause of the canonical finite-boundary comparison.
Source: blueprint Step 5 and its Frobenius paragraph
(blueprint: lem-a1-condensed-point-dual-comparison). -/
def CondensedBoundaryComplexTensorNormalization
    [s : CondensedBoundaryEvaluationTensor ℓ k I] : Prop :=
  ∀ (t : I) (P Q : CochainComplex (CondensedBoundaryMod ℓ k I) ℤ),
    ∃ b : ((condensedBoundarySections ℓ k I t).mapHomologicalComplex (.up ℤ)).obj P ⊗
        ((condensedBoundarySections ℓ k I t).mapHomologicalComplex (.up ℤ)).obj Q ⟶
          ((condensedBoundarySections ℓ k I t).mapHomologicalComplex (.up ℤ)).obj (P ⊗ Q),
      (∀ p q : ℤ,
        HomologicalComplex.ιTensorObj
          (((condensedBoundarySections ℓ k I t).mapHomologicalComplex (.up ℤ)).obj P)
          (((condensedBoundarySections ℓ k I t).mapHomologicalComplex (.up ℤ)).obj Q)
          p q (p + q) rfl ≫ b.f (p + q) =
        Functor.LaxMonoidal.μ (condensedBoundarySections ℓ k I t) (P.X p) (Q.X q) ≫
          (condensedBoundarySections ℓ k I t).map
            (HomologicalComplex.ιTensorObj P Q p q (p + q) rfl)) ∧
      ((condensedBoundarySections ℓ k I t).mapDerivedCategoryFactors.inv.app P ⊗ₘ
        (condensedBoundarySections ℓ k I t).mapDerivedCategoryFactors.inv.app Q) ≫
        Functor.LaxMonoidal.μ (condensedBoundaryFiber ℓ k I t)
          (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj Q) ≫
        (condensedBoundaryFiber ℓ k I t).map (Functor.LaxMonoidal.μ DerivedCategory.Q P Q) ≫
        (condensedBoundarySections ℓ k I t).mapDerivedCategoryFactors.hom.app (P ⊗ Q) =
      Functor.LaxMonoidal.μ DerivedCategory.Q _ _ ≫ DerivedCategory.Q.map b

/-- The collected named clauses of the canonical finite-boundary comparison.
Source: blueprint Step 5 and its Frobenius paragraph
(blueprint: lem-a1-condensed-point-dual-comparison). -/
structure IsCanonicalCondensedBoundaryEvaluationTensor
    [s : CondensedBoundaryEvaluationTensor ℓ k I] : Prop where
  sections_unit : CondensedBoundarySectionsUnitNormalization ℓ k I
  sections_tensor : CondensedBoundarySectionsTensorNormalization ℓ k I
  fiber_unit : CondensedBoundaryFiberUnitNormalization ℓ k I
  complex_unit : CondensedBoundaryComplexUnitNormalization ℓ k I
  complex_tensor : CondensedBoundaryComplexTensorNormalization ℓ k I

/-- The actual canonical dual comparison: transpose evaluated sheaf evaluation and
identify the evaluated coefficient unit with Λ[0]. Source: blueprint Step 5
(blueprint: lem-a1-condensed-point-dual-comparison). -/
def condensedBoundaryDualComparison [s : CondensedBoundaryEvaluationTensor ℓ k I]
    (t : I) (K : DerivedCategory (CondensedBoundaryMod ℓ k I)) :=
  (Functor.LaxMonoidal.ihomComparison (condensedBoundaryFiber ℓ k I t) K).natTrans.app
      (𝟙_ _) ≫
    (ihom ((condensedBoundaryFiber ℓ k I t).obj K)).map (s.unit t).hom

/-- Reparametrization by a component permutation and a field automorphism; coefficients
are pulled back, not acted on by the field automorphism. Source: blueprint Step 5
(blueprint: lem-a1-condensed-point-dual-comparison). -/
def condensedBoundaryReparametrization (e : Equiv.Perm I) (σ : k ≃+* k) :
    condensedPointBoundary k I ⟶ condensedPointBoundary k I :=
  Sigma.desc fun t : I ↦
    Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ Sigma.ι (fun _ : I ↦ (point k).left) (e t)

/-- The canonical component pullback composition isomorphism for a reparametrization.
Source: blueprint Step 5, equivariance
(blueprint: lem-a1-condensed-point-dual-comparison). -/
def condensedBoundaryReparametrizationRestriction (e : Equiv.Perm I) (σ : k ≃+* k) (t : I) :
    upperStar (Profinite.padicAlgClRingObj ℓ) (condensedBoundaryReparametrization k I e σ) ⋙
        condensedBoundaryRestriction ℓ k I t ≅
      condensedBoundaryRestriction ℓ k I (e t) ⋙
        upperStar (Profinite.padicAlgClRingObj ℓ) (Spec.map (CommRingCat.ofHom σ.toRingHom)) :=
  (upperStarComp (Profinite.padicAlgClRingObj ℓ)
      (Sigma.ι (fun _ : I ↦ (point k).left) t)
      (condensedBoundaryReparametrization k I e σ)).symm ≪≫
    eqToIso (congrArg (upperStar (Profinite.padicAlgClRingObj ℓ))
      (Sigma.ι_desc
        (fun t : I ↦ Spec.map (CommRingCat.ofHom σ.toRingHom) ≫
          Sigma.ι (fun _ : I ↦ (point k).left) (e t)) t)) ≪≫
    upperStarComp (Profinite.padicAlgClRingObj ℓ)
      (Spec.map (CommRingCat.ofHom σ.toRingHom))
      (Sigma.ι (fun _ : I ↦ (point k).left) (e t))

/-- Derived reparametrization, using the published monoidal derived pullback.
Source: blueprint Step 5 (blueprint: lem-a1-condensed-point-dual-comparison). -/
abbrev condensedBoundaryReparametrizationPullback (e : Equiv.Perm I) (σ : k ≃+* k) :=
  (upperStar (Profinite.padicAlgClRingObj ℓ)
    (condensedBoundaryReparametrization k I e σ)).leftDerivedFunctor

/-- Derivation of the specified section reindexing, including the exact-pullback comparison.
Source: blueprint Step 5 (blueprint: lem-a1-condensed-point-dual-comparison). -/
def condensedBoundaryReindexIso (e : Equiv.Perm I) (σ : k ≃+* k) (t : I)
    (a : condensedBoundarySections ℓ k I (e t) ≅
      upperStar (Profinite.padicAlgClRingObj ℓ) (condensedBoundaryReparametrization k I e σ) ⋙
        condensedBoundarySections ℓ k I t) :
    condensedBoundaryFiber ℓ k I (e t) ≅
      condensedBoundaryReparametrizationPullback ℓ k I e σ ⋙ condensedBoundaryFiber ℓ k I t :=
  Functor.mapDerivedCategoryNatIso a ≪≫ Functor.mapDerivedCategoryCompIso _ _ ≪≫
    Functor.isoWhiskerRight
      (leftDerivedUpperStarIsoMapDerivedCategory (Profinite.padicAlgClRingObj ℓ)
        (condensedBoundaryReparametrization k I e σ)).symm _

/-- The derived pullback's canonical comparison with coefficient duality.
Source: blueprint Step 5 (blueprint: lem-a1-condensed-point-dual-comparison). -/
def condensedBoundaryPullbackDualComparison (e : Equiv.Perm I) (σ : k ≃+* k)
    (K : DerivedCategory (CondensedBoundaryMod ℓ k I)) :=
  (Functor.LaxMonoidal.ihomComparison
    (condensedBoundaryReparametrizationPullback ℓ k I e σ) K).natTrans.app (𝟙_ _) ≫
    (ihom ((condensedBoundaryReparametrizationPullback ℓ k I e σ).obj K)).map
      (Functor.Monoidal.εIso (condensedBoundaryReparametrizationPullback ℓ k I e σ)).inv

/- The clauses of the finite-boundary equivalence and dual comparison, using the
specified normalized evaluation tensor. All categories and functors are the existing
ordinary derived constructions. Source: blueprint Step 5 and Frobenius paragraph
(blueprint: lem-a1-condensed-point-dual-comparison). -/
/-- The equivalence clause of the canonical finite-boundary comparison.
Source: blueprint Step 5 and its Frobenius paragraph
(blueprint: lem-a1-condensed-point-dual-comparison). -/
def CondensedBoundaryEquivalenceAssertion : Prop :=
  ∃ E : ConstantModelBoundedConstructible (Profinite.padicAlgClRingObj ℓ)
    (condensedPointBoundary k I) ≌
      (I → (DerivedCategory.pointFiniteDimensional
        (ULift.{u + 1} (PadicAlgCl ℓ))).FullSubcategory),
  (∀ t : I, Nonempty
    (E.functor ⋙ Pi.eval (fun _ : I ↦
        (DerivedCategory.pointFiniteDimensional
          (ULift.{u + 1} (PadicAlgCl ℓ))).FullSubcategory) t ⋙
          (DerivedCategory.pointFiniteDimensional
            (ULift.{u + 1} (PadicAlgCl ℓ))).ι ≅
      (constantModelBoundedConstructible (Profinite.padicAlgClRingObj ℓ)
        (condensedPointBoundary k I)).ι ⋙ condensedBoundaryFiber ℓ k I t)) ∧
  (∀ t : I, Nonempty
    (E.inverse ⋙ (constantModelBoundedConstructible (Profinite.padicAlgClRingObj ℓ)
        (condensedPointBoundary k I)).ι ⋙
          (condensedBoundaryRestriction ℓ k I t).mapDerivedCategory ≅
      Pi.eval (fun _ : I ↦ (DerivedCategory.pointFiniteDimensional
          (ULift.{u + 1} (PadicAlgCl ℓ))).FullSubcategory) t ⋙
        (DerivedCategory.pointFiniteDimensional
          (ULift.{u + 1} (PadicAlgCl ℓ))).ι ⋙
            (condensedPointScalarExtension ℓ k).mapDerivedCategory))

/-- The scalar extension presentation clause of the canonical finite-boundary comparison.
Source: blueprint Step 5 and its Frobenius paragraph
(blueprint: lem-a1-condensed-point-dual-comparison). -/
def CondensedBoundaryScalarExtensionPresentation : Prop :=
  ∃ C : ModuleCat.{u + 1} (ULift.{u + 1} (PadicAlgCl ℓ)) ≌
    Mod Ab.{u + 1} (scalarRingObj (Profinite.padicAlgClRingObj ℓ)),
  Nonempty (condensedPointScalarExtension ℓ k ≅
    C.functor ⋙ finiteConstantScalarExtension (Profinite.padicAlgClRingObj ℓ)
      (point k).left)

/-- The exact clause of the canonical finite-boundary comparison.
Source: blueprint Step 5 and its Frobenius paragraph
(blueprint: lem-a1-condensed-point-dual-comparison). -/
def CondensedBoundaryExactAssertion : Prop :=
  ∀ t : I, (condensedBoundaryFiber ℓ k I t).IsTriangulated

/-- The dual constructible clause of the canonical finite-boundary comparison.
Source: blueprint Step 5 and its Frobenius paragraph
(blueprint: lem-a1-condensed-point-dual-comparison). -/
def CondensedBoundaryDualConstructibleAssertion : Prop :=
  ∀ K : DerivedCategory (CondensedBoundaryMod ℓ k I),
  constantModelBoundedConstructible (Profinite.padicAlgClRingObj ℓ)
    (condensedPointBoundary k I) K →
  constantModelBoundedConstructible (Profinite.padicAlgClRingObj ℓ)
    (condensedPointBoundary k I) ((ihom K).obj (𝟙_ _))

/-- The comparison isIso clause of the canonical finite-boundary comparison.
Source: blueprint Step 5 and its Frobenius paragraph
(blueprint: lem-a1-condensed-point-dual-comparison). -/
def CondensedBoundaryDualIsIsoAssertion
    [s : CondensedBoundaryEvaluationTensor ℓ k I] : Prop :=
  ∀ (t : I) (K : DerivedCategory (CondensedBoundaryMod ℓ k I)),
    constantModelBoundedConstructible (Profinite.padicAlgClRingObj ℓ)
      (condensedPointBoundary k I) K →
    IsIso (condensedBoundaryDualComparison ℓ k I t K)

/-- The evaluation clause of the canonical finite-boundary comparison.
Source: blueprint Step 5 and its Frobenius paragraph
(blueprint: lem-a1-condensed-point-dual-comparison). -/
def CondensedBoundaryEvaluationAssertion
    [s : CondensedBoundaryEvaluationTensor ℓ k I] : Prop :=
  ∀ (t : I) (K : DerivedCategory (CondensedBoundaryMod ℓ k I)),
    constantModelBoundedConstructible (Profinite.padicAlgClRingObj ℓ)
      (condensedPointBoundary k I) K →
    (condensedBoundaryFiber ℓ k I t).obj K ◁
        condensedBoundaryDualComparison ℓ k I t K ≫
      (ihom.ev ((condensedBoundaryFiber ℓ k I t).obj K)).app (𝟙_ _) =
    Functor.LaxMonoidal.μ (condensedBoundaryFiber ℓ k I t) K ((ihom K).obj (𝟙_ _)) ≫
      (condensedBoundaryFiber ℓ k I t).map ((ihom.ev K).app (𝟙_ _)) ≫ (s.unit t).hom

/-- The naturality clause of the canonical finite-boundary comparison.
Source: blueprint Step 5 and its Frobenius paragraph
(blueprint: lem-a1-condensed-point-dual-comparison). -/
def CondensedBoundaryDualNaturalityAssertion
    [s : CondensedBoundaryEvaluationTensor ℓ k I] : Prop :=
  ∀ (t : I) (K L : DerivedCategory (CondensedBoundaryMod ℓ k I))
    (f : K ⟶ L),
    constantModelBoundedConstructible (Profinite.padicAlgClRingObj ℓ)
      (condensedPointBoundary k I) K →
    constantModelBoundedConstructible (Profinite.padicAlgClRingObj ℓ)
      (condensedPointBoundary k I) L →
    (condensedBoundaryFiber ℓ k I t).map ((MonoidalClosed.pre f).app (𝟙_ _)) ≫
        condensedBoundaryDualComparison ℓ k I t K =
      condensedBoundaryDualComparison ℓ k I t L ≫
        (MonoidalClosed.pre ((condensedBoundaryFiber ℓ k I t).map f)).app (𝟙_ _)

/-- Pullback along the field automorphism used in reparametrization formulas.
Source: blueprint Step 5 and its Frobenius paragraph
(blueprint: lem-a1-condensed-point-dual-comparison). -/
def condensedBoundarySigmaPullback (σ : k ≃+* k) : PointMod ℓ k ⥤ PointMod ℓ k :=
  upperStar (Profinite.padicAlgClRingObj ℓ) (Spec.map (CommRingCat.ofHom σ.toRingHom))

/-- Pullback along the full component reparametrization.
Source: blueprint Step 5 and its Frobenius paragraph
(blueprint: lem-a1-condensed-point-dual-comparison). -/
def condensedBoundaryPermutationPullback (e : Equiv.Perm I) (σ : k ≃+* k) :
    CondensedBoundaryMod ℓ k I ⥤ CondensedBoundaryMod ℓ k I :=
  upperStar (Profinite.padicAlgClRingObj ℓ) (condensedBoundaryReparametrization k I e σ)

/-- The section formula for component reparametrization.
Source: blueprint Step 5 and its Frobenius paragraph
(blueprint: lem-a1-condensed-point-dual-comparison). -/
def CondensedBoundaryReindexSectionNormalization
    (e : Equiv.Perm I) (σ : k ≃+* k) (t : I)
    (a : condensedBoundarySections ℓ k I (e t) ≅
      condensedBoundaryPermutationPullback ℓ k I e σ ⋙
        condensedBoundarySections ℓ k I t) : Prop :=
  ∀ (M : CondensedBoundaryMod ℓ k I)
    (x : (condensedBoundarySections ℓ k I (e t)).obj M),
    condensedBoundarySectionHom ℓ k I t
        ((condensedBoundaryPermutationPullback ℓ k I e σ).obj M)
        ((a.hom.app M).hom x) =
      Functor.LaxMonoidal.ε
          (condensedBoundarySigmaPullback ℓ k σ) ≫
        (condensedBoundarySigmaPullback ℓ k σ).map
            (condensedBoundarySectionHom ℓ k I (e t) M x) ≫
        (condensedBoundaryReparametrizationRestriction ℓ k I e σ t).inv.app M

/-- Monoidality of the derived component reindexing.
Source: blueprint Step 5 and its Frobenius paragraph
(blueprint: lem-a1-condensed-point-dual-comparison). -/
def CondensedBoundaryReindexMonoidal
    [s : CondensedBoundaryEvaluationTensor ℓ k I]
    (e : Equiv.Perm I) (σ : k ≃+* k) (t : I)
    (a : condensedBoundarySections ℓ k I (e t) ≅
      condensedBoundaryPermutationPullback ℓ k I e σ ⋙
        condensedBoundarySections ℓ k I t) : Prop :=
  NatTrans.IsMonoidal (condensedBoundaryReindexIso ℓ k I e σ t a).hom

/-- Compatibility of reindexing with the canonical derived dual comparison.
Source: blueprint Step 5 and its Frobenius paragraph
(blueprint: lem-a1-condensed-point-dual-comparison). -/
def CondensedBoundaryReindexDualNormalization
    [s : CondensedBoundaryEvaluationTensor ℓ k I]
    (e : Equiv.Perm I) (σ : k ≃+* k) (t : I)
    (a : condensedBoundarySections ℓ k I (e t) ≅
      condensedBoundaryPermutationPullback ℓ k I e σ ⋙
        condensedBoundarySections ℓ k I t) : Prop :=
  ∀ K : DerivedCategory (CondensedBoundaryMod ℓ k I),
    constantModelBoundedConstructible (Profinite.padicAlgClRingObj ℓ)
      (condensedPointBoundary k I) K →
    (condensedBoundaryReindexIso ℓ k I e σ t a).hom.app ((ihom K).obj (𝟙_ _)) ≫
        (condensedBoundaryFiber ℓ k I t).map
          (condensedBoundaryPullbackDualComparison ℓ k I e σ K) ≫
        condensedBoundaryDualComparison ℓ k I t
          ((condensedBoundaryReparametrizationPullback ℓ k I e σ).obj K) =
      condensedBoundaryDualComparison ℓ k I (e t) K ≫
        (MonoidalClosed.pre
          ((condensedBoundaryReindexIso ℓ k I e σ t a).inv.app K)).app (𝟙_ _)

/-- The reparametrization clause of the canonical finite-boundary comparison.
Source: blueprint Step 5 and its Frobenius paragraph
(blueprint: lem-a1-condensed-point-dual-comparison). -/
def CondensedBoundaryReparametrizationAssertion
    [s : CondensedBoundaryEvaluationTensor ℓ k I] : Prop :=
  ∀ (e : Equiv.Perm I) (σ : k ≃+* k) (t : I),
    ∃ a : condensedBoundarySections ℓ k I (e t) ≅
        condensedBoundaryPermutationPullback ℓ k I e σ ⋙
          condensedBoundarySections ℓ k I t,
      CondensedBoundaryReindexSectionNormalization ℓ k I e σ t a ∧
      CondensedBoundaryReindexMonoidal ℓ k I e σ t a ∧
      CondensedBoundaryReindexDualNormalization ℓ k I e σ t a

/-- The collected named clauses of the canonical finite-boundary comparison.
Source: blueprint Step 5 and its Frobenius paragraph
(blueprint: lem-a1-condensed-point-dual-comparison). -/
structure CondensedBoundaryDualComparisonAssertions
    [s : CondensedBoundaryEvaluationTensor ℓ k I] : Prop where
  equivalence : CondensedBoundaryEquivalenceAssertion ℓ k I
  scalar_extension_presentation : CondensedBoundaryScalarExtensionPresentation ℓ k
  exact : CondensedBoundaryExactAssertion ℓ k I
  dual_constructible : CondensedBoundaryDualConstructibleAssertion ℓ k I
  comparison_isIso : CondensedBoundaryDualIsIsoAssertion ℓ k I
  evaluation : CondensedBoundaryEvaluationAssertion ℓ k I
  naturality : CondensedBoundaryDualNaturalityAssertion ℓ k I
  reparametrization : CondensedBoundaryReparametrizationAssertion ℓ k I

end AlgebraicGeometry.ProEtale.CondensedRing

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- Condensed point evaluation is the exact finite-boundary equivalence, with its
specified scalar-extension inverse and canonical, evaluation-preserving derived dual
comparison, natural both in complexes and in reparametrizations of the geometric points.

Source: blueprint lem-a1-local-boundary-duality.proof.md, Step 5 and the Frobenius paragraph
(blueprint: lem-a1-condensed-point-dual-comparison).

Proof, following the node's nine steps:
1. The geometric-point/profinite-site identification and split covers make sections exact.
   Singleton evaluation identifies the coefficient ring with Λ. Local lifting of sections
   of epimorphisms of sheaves of sets also gives global lifting on this point.
2. Pull a finite constant local model back along a section of one covering member. Over
   Λ a finite presentation has a finite basis, so constructible modules on the point are
   finite powers of the coefficient unit. Their morphisms are exactly scalar matrices.
3. The copower tensor/sections adjunction has unit v ↦ 1 tensor v and counit
   a tensor m ↦ a m. Scalar extension is exact because vector-space sequences split.
   Its unit and counit are isomorphisms on finite-dimensional and constructible objects.
4. Derive these exact functors termwise. The unit and counit induce the corresponding
   maps on cohomology, so their restrictions to the stated full subcategories are inverse
   isomorphisms. All morphisms remain ambient ordinary derived morphisms.
5. Apply finite clopen module gluing to the component inclusions. Restriction and gluing
   are exact and derive termwise. Constructibility is local on the cover, and finitely
   many cohomological bounds have a common minimum and maximum. This includes I empty.
6. Lift cohomology generators using projectivity of the finite free modules. The
   projective-cohomology splitting lemma gives bounded zero-differential finite free
   models on each component. Glue them, padding ranks so the global terms are retracts
   of finite free modules. These models verify the canonical maps without defining them.
7. The bounded-free ringed-site Hom model computes the sheaf dual. Restricting and taking
   sections gives the ordinary finite free scalar dual complex, which computes scalar
   derived Hom by the projective Hom evaluation model. The dual is again constructible.
8. Section tensor has the displayed pure-tensor formula; its totalization has the
   displayed summand formula. The finite free models are K-flat. Transpose the evaluated
   sheaf evaluation using tensor--Hom adjunction. The signed ringed-site duality and
   projective scalar Hom models identify the two evaluation formulas, including the
   Koszul sign when the arguments are interchanged. This proves invertibility and the
   evaluation square for the specified comparison.
9. Precomposition is scalar matrix multiplication and commutes with sections and chain
   homotopies, proving naturality and independence of the models. A field automorphism
   reindexes the terminal point and fixes constant coefficient sections; a component
   permutation reindexes the factors. The displayed pullback composition and section
   formulas therefore give the final duality square, compatibly with composition.

The proof dependencies, in this order, are
`lem-weil-pbc-geometric-field-proetale-evaluation`,
`lem-weil-pbc-site-sheaf-sets-epi-locally-surjective`,
`sk-def-sfb-constructible`, `sk-prop-sfb-cartesian-coefficients`,
`det-def-sfb-constructible-local-model`, `lem-weil-pbc-vector-space-projective`,
`lem-weil-pbc-exact-functor-derived-factorization`,
`lem-sp-exact-functor-preserves-homology`, `lem-weil-pbc-unbounded-derived-iso-cohomology`,
`lem-pur-clopen-ringed-module-gluing`, `lem-sf-projective-cohomology-split-model`,
`lem-weil-pbc-ringed-site-bounded-free-rhom-model`, `def-pur-sheaf-hom`,
`lem-pod-projective-hom-evaluation-model`, `def-pc-tensor-complex-sheaves`,
`def-pc-kflat-complex`, `def-weil-derived-pullback-tensor-hom`, and
`lem-sfb-ringed-site-duality-maps`. -/
theorem condensed_point_dual_comparison
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)] :
    PreservesFiniteLimits (pointSections ℓ k) ∧
    PreservesFiniteColimits (pointSections ℓ k) ∧
    Exists fun [s : CondensedBoundaryEvaluationTensor ℓ k I] ↦
      IsCanonicalCondensedBoundaryEvaluationTensor ℓ k I ∧
      CondensedBoundaryDualComparisonAssertions ℓ k I := by
  refine ⟨inferInstance, inferInstance, ?_⟩
  obtain ⟨s, hs⟩ := condensed_point_canonical_tensor ℓ k I
  obtain ⟨he, hp⟩ := condensed_point_component_equivalence ℓ k I
  obtain ⟨hc, hi, _, _, hr⟩ := condensed_point_normalized_duality ℓ k I hs
  refine ⟨s, hs, ?_⟩
  exact
    { equivalence := he
      scalar_extension_presentation := hp
      exact := fun t ↦ by
        dsimp [condensedBoundaryFiber]
        infer_instance
      dual_constructible := hc
      comparison_isIso := hi
      evaluation := fun t K _hK ↦ by
        unfold condensedBoundaryDualComparison
        rw [← uncurry_eq, uncurry_natural_right, uncurry_eq,
          Functor.LaxMonoidal.ihomComparison_ev, Category.assoc]
      naturality := fun t K L f _hK _hL ↦ by
        unfold condensedBoundaryDualComparison
        rw [← Category.assoc, Functor.LaxMonoidal.map_pre_app_comp_ihomComparison_app,
          Category.assoc, pre_comm_ihom_map, Category.assoc]
      reparametrization := hr }

end AlgebraicGeometry.ProEtale.CondensedRing
