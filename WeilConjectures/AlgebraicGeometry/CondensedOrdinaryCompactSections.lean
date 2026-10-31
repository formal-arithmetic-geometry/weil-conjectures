/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CommonStageCompactWeilCohomology
public import WeilConjectures.AlgebraicGeometry.CondensedOrdinaryCompactCohomology
public import WeilConjectures.AlgebraicGeometry.CondensedQbarCoefficientConstruction
public import WeilConjectures.AlgebraicGeometry.PointLanAffineEvaluation
public import WeilConjectures.AlgebraicGeometry.ProEtalePointComponentsMaps
public import WeilConjectures.AlgebraicGeometry.ProfiniteTestObjectFunctor
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Topology.Category.Profinite.AsLimit
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.Topology.Category.Profinite.CofilteredLimit
public import WeilConjectures.RingTheory.Spectrum.Prime.LocallyConstant
public import Mathlib.Topology.Connected.TotallyDisconnected
public import WeilConjectures.Topology.SpectralSpace.ConnectedComponent
public import Mathlib.CategoryTheory.Functor.KanExtension.Pointwise
public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.Algebra.Category.Ring.Basic
public import WeilConjectures.AlgebraicGeometry.PointLanFiniteProducts
public import WeilConjectures.AlgebraicGeometry.CondensedFieldContinuousRealization
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
public import WeilConjectures.AlgebraicGeometry.ProEtaleModuleConstructiblePullback
public import WeilConjectures.CategoryTheory.Monoidal.Conjugate
public import WeilConjectures.ConstructibleSheaf.Pullback
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
public import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientUniverse
public import Mathlib.Topology.Category.Profinite.EffectiveEpi
public import WeilConjectures.CategoryTheory.RingObjects.ContinuousMap
public import Mathlib.Condensed.TopComparison
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.Topology.NoetherianSpace
public import WeilConjectures.AlgebraicGeometry.ProEtaleSheafificationWcontractibleSections
public import WeilConjectures.AlgebraicGeometry.Sites.ProEtaleFiniteCoproductEvaluation
public import Mathlib.AlgebraicGeometry.Limits
public import WeilConjectures.AlgebraicGeometry.FiniteCoproductLfpQcqs
public import WeilConjectures.AlgebraicGeometry.Sites.ProEtaleFiniteCoproductSections
public import WeilConjectures.AlgebraicGeometry.ProEtaleAffineContractibleExtension
public import WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
public import WeilConjectures.CategoryTheory.Sites.MonObj
public import WeilConjectures.AlgebraicGeometry.ProEtaleAffineWeaklyContractibleCover
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension
public import Mathlib.Algebra.Field.ULift
public import WeilConjectures.AlgebraicGeometry.GeometricFieldProEtaleEvaluation
public import WeilConjectures.AlgebraicGeometry.ProfinitePointPullback
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import Mathlib.CategoryTheory.Sites.Equivalence
public import WeilConjectures.CategoryTheory.SiteInverseImageTensor
public import WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
public import Mathlib.CategoryTheory.Monoidal.CommGrp_
public import Mathlib.CategoryTheory.Monoidal.Ring
public import Mathlib.CategoryTheory.Adjunction.Limits
public import WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
public import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Reflective
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.AlgebraicGeometry.GeometricFieldProfiniteDenseSubsite
public import WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.Affine
public import WeilConjectures.CategoryTheory.DenseSubsiteModuleRestriction
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.CategoryTheory.Sites.CartesianMonoidal
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek

/-! # Ordinary derived sections for native condensed Qbar coefficients

Source: latest blueprint, sec-six-functors-basics/sk-thm-existence/
def-weil-ordinary-compact-cohomology.md, the displayed RΓ and RΓ_c formulas
(blueprint: def-weil-ordinary-compact-cohomology).

The existing general condensed-ring and older coefficient interfaces remain public.
## Main definitions

`condensedQbarDerivedPointSections` is exact derived geometric evaluation.
`condensedQbarOrdinarySections` and `condensedQbarCompactSections` give the
ordinary and compact-support coefficient complexes in fixed Qbar coordinates.

This specialization accepts every native condensed-module complex, rather than
requiring an object to descend from the finite-stage adic encoding.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.Obj
namespace WeilConjectures

/-- The standard ordinary derived category of coefficient modules.
Source: the node's ordinary derived coefficient convention
(blueprint: def-weil-ordinary-compact-cohomology). -/
instance condensedQbarCoefficientDerived (ell : ℕ) [Fact ell.Prime] :
    HasDerivedCategory.{u + 2} (ModuleCat.{u + 1} (PadicAlgCl ell)) :=
  HasDerivedCategory.standard _

/-- Exactness on the left is computed after the faithful ordinary-module forgetful functor.
Source: exact geometric-point sections
(blueprint: def-weil-ordinary-compact-cohomology). -/
instance condensedQbarFieldFiberLimits (ell : ℕ) [Fact ell.Prime]
    (k : Type u) [Field k] [IsAlgClosed k] :
    PreservesFiniteLimits (ProEtale.CondensedQbarGeometricEvaluation.fieldFiber k ell) := by
  let J := Scheme.ProEt.topology (Spec (.of k))
  let A := ProEtale.condensedRingObj (Profinite.padicAlgClRingObj ell) (Spec (.of k))
  let S := sheafToPresheaf J Ab.{u + 1}
  let E := (evaluation (Spec (.of k)).ProEtᵒᵖ Ab.{u + 1}).obj
    (Opposite.op (Scheme.ProEt.mk (𝟙 (Spec (.of k)))))
  have : PreservesFiniteLimits (S ⋙ E) := inferInstance
  have : PreservesFiniteLimits ((S ⋙ E).mapMod A) := inferInstance
  have : PreservesFiniteLimits (Mod.comap (D := Ab.{u + 1})
    (inv (ProEtale.CondensedQbarGeometricEvaluation.fieldCoefficientIso k ell).hom.hom)) :=
    inferInstance
  have : PreservesFiniteLimits
      (ProEtale.CondensedQbarGeometricEvaluation.ordinary
        (ULift.{u + 1} (PadicAlgCl ell))) := inferInstance
  have : PreservesFiniteLimits (ModuleCat.restrictScalars.{u + 1}
      (ULift.ringEquiv.symm.toRingHom :
        PadicAlgCl ell →+* ULift.{u + 1} (PadicAlgCl ell))) := by
    refine ⟨fun I _ _ ↦ ?_⟩
    have : PreservesLimitsOfShape I
        (ModuleCat.restrictScalars.{u + 1}
          (ULift.ringEquiv.symm.toRingHom :
            PadicAlgCl ell →+* ULift.{u + 1} (PadicAlgCl ell)) ⋙
            forget₂ (ModuleCat.{u + 1} (PadicAlgCl ell)) Ab.{u + 1}) :=
      inferInstanceAs (PreservesLimitsOfShape I
        (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} (PadicAlgCl ell))) Ab.{u + 1}))
    exact preservesLimitsOfShape_of_reflects_of_preserves _
      (forget₂ (ModuleCat.{u + 1} (PadicAlgCl ell)) Ab.{u + 1})
  unfold ProEtale.CondensedQbarGeometricEvaluation.fieldFiber
  infer_instance

/-- Derived geometric-point evaluation, with coefficient ring exactly Qbar_ell.
Source: the node's compact-cohomology convention
(blueprint: def-weil-ordinary-compact-cohomology). -/
abbrev condensedQbarDerivedPointSections (ell : ℕ) [Fact ell.Prime]
    (k : Type u) [Field k] [IsAlgClosed k] :=
  (ProEtale.CondensedQbarGeometricEvaluation.fieldFiber k ell).mapDerivedCategory

/-- Compact support is exact open extension, then proper derived image, then point sections.
Source: the node's displayed formula RΓ_c(Y,K) = Fib_s(Ra_! K)
(blueprint: def-weil-ordinary-compact-cohomology). -/
abbrev condensedQbarCompactSections (ell : ℕ) [Fact ell.Prime]
    (k : Type u) [Field k] [IsAlgClosed k]
    {X : Scheme.{u}} {a : X ⟶ Spec (.of k)} (c : Compactification a) :=
  ProEtale.CondensedRing.rightDerivedLowerShriekOfCompactification
    (Profinite.padicAlgClRingObj ell) c ⋙ condensedQbarDerivedPointSections ell k

/-- Ordinary sections are proper-free derived direct image followed by exact point sections.
Source: the ordinary RΓ formula
(blueprint: def-weil-ordinary-compact-cohomology). -/
abbrev condensedQbarOrdinarySections (ell : ℕ) [Fact ell.Prime]
    (k : Type u) [Field k] [IsAlgClosed k] {X : Scheme.{u}} (a : X ⟶ Spec (.of k)) :=
  (ProEtale.CondensedRing.lowerStar (Profinite.padicAlgClRingObj ell) a).rightDerivedFunctor ⋙
    condensedQbarDerivedPointSections ell k

end WeilConjectures
