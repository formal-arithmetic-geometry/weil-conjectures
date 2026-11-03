/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructible
public import WeilConjectures.SmoothPurity.Sf.SfDerivedComplete
public import WeilConjectures.CategoryTheory.InternalSectionTensorComparison
public import WeilConjectures.CategoryTheory.InternalAbelianSheafModuleEquivalence
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.CategoryTheory.Monoidal.Internal.FunctorCategory
public import WeilConjectures.CategoryTheory.RingObjects.Ab
public import WeilConjectures.CategoryTheory.Sites.MonObj
public import WeilConjectures.CategoryTheory.ModuleObjects.MapMod
public import WeilConjectures.CategoryTheory.SheafTensor
public import WeilConjectures.CategoryTheory.SheafTensorStructure
public import Mathlib.CategoryTheory.Sites.Monoidal
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import WeilConjectures.CategoryTheory.PresheafTensorInternalHom
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Preadditive
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Sites.Localization
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Monoidal.Braided.Reflection
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.ModuleObjects.Symmetric
public import WeilConjectures.CategoryTheory.ModuleObjects.Abelian
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
public import WeilConjectures.FromJoel.Algebra.Homology.TotalComplexMap
public import WeilConjectures.CategoryTheory.InternalSectionModuleFlat
public import WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.AlgebraicGeometry.AdicCompletion.DerivedCompletionSupplement
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
public import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.RingTheory.Flat.CategoryTheory
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
public import Mathlib.CategoryTheory.Limits.Final
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constructible.ProEtaleConstructibleSheaf
public import Mathlib.AlgebraicGeometry.Noetherian

import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafOver
import Mathlib.CategoryTheory.Limits.Types.Products
import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
public import WeilConjectures.AlgebraicGeometry.ProEtaleIntegralCoefficientLimit
public import WeilConjectures.AlgebraicGeometry.ProEtaleIntegralCoefficientData
public import Mathlib.Topology.Category.Profinite.AsLimit
public import WeilConjectures.AlgebraicGeometry.ProEtalePointPullback
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMapCondensedRingSupplement
public import WeilConjectures.NumberTheory.Padics.IntegersProfiniteTower
public import Mathlib.Algebra.Ring.Subring.Basic
public import Mathlib.Algebra.Ring.Pi
public import Mathlib.Topology.Homeomorph.Defs
public import Mathlib.Topology.Connected.TotallyDisconnected
public import Mathlib.Topology.Compactness.Compact
public import WeilConjectures.NumberTheory.Padics.IntegersCosetBasis
public import Mathlib.Topology.Bases
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.LocallyConstant.Basic
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.NumberTheory.Padics.ProperSpace
public import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvr
public import Mathlib.Algebra.Order.AbsoluteValue.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrCore
public import Mathlib.Analysis.Normed.Algebra.Ultra
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.Algebra.Valued.LocallyCompact
public import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorization
public import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorizationUnique
public import WeilConjectures.Mathlib.RingTheory.OrderOfVanishing.Noetherian
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
public import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientGerm
public import WeilConjectures.AlgebraicGeometry.ProfiniteTestObjectFunctor
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.Topology.Category.Profinite.CofilteredLimit
public import WeilConjectures.RingTheory.Spectrum.Prime.LocallyConstant
public import WeilConjectures.AlgebraicGeometry.ProfiniteLocallyConstantAdjunction
public import WeilConjectures.AlgebraicGeometry.ProEtaleFiniteConstantRepresentable
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.CategoryTheory.FintypeCat
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import WeilConjectures.AlgebraicGeometry.CoproductCopiesMorphismsClopen
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import WeilConjectures.CategoryTheory.SheafPullbackForgetComparison
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.CategoryTheory.Limits.Presheaf
public import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
public import WeilConjectures.AlgebraicGeometry.ProEtaleIntegralRingComparison
public import WeilConjectures.AlgebraicGeometry.ProEtaleIntegralPointRingMap
public import WeilConjectures.CategoryTheory.Sites.PushforwardMonoidal
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import Mathlib.CategoryTheory.Monoidal.Mon
public import Mathlib.Algebra.Field.ULift
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteReductionPullbackSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.PadicIntegersInvertEll
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
public import WeilConjectures.SixFunctors.ProEtale.GaloisEvaluation
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficientComparisonsPullback
import WeilConjectures.NumberTheory.Padics.IntegersCosetBasis
import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
import Mathlib.Topology.Bases
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Analysis.SpecificLimits.Basic
import all WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteCoefficientModelComparison
import all WeilConjectures.SixFunctors.ProEtale.IntegralCompletionPresentationSupplement
import WeilConjectures.SixFunctors.ProEtale.IntegralNormalizedSectionSquares
import WeilConjectures.AlgebraicGeometry.AdicCompletion.InternalRoosCompleteness
import WeilConjectures.AlgebraicGeometry.DerivedNakayamaResolution
import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
import Mathlib.RingTheory.Ideal.Quotient.Index
import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientCommRing
import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientUniverse
import Mathlib.Topology.Category.Profinite.EffectiveEpi
import WeilConjectures.CategoryTheory.RingObjects.ContinuousMap
import Mathlib.Condensed.TopComparison
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Tensor
import Mathlib.Topology.Algebra.Ring.Ideal
import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import WeilConjectures.CategoryTheory.Right.RightDerivedFunctorOfQuasiIsoResolutions
import WeilConjectures.SixFunctors.ProEtale.Adic.PadicIntSheafLinear
import WeilConjectures.CategoryTheory.Sites.MonObj
import Mathlib.Algebra.Homology.ShortComplex.Ab
import Mathlib.Topology.LocallyConstant.Basic
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.TensorMappingCone
import WeilConjectures.CategoryTheory.Monoidal.Closed.UnitEnd
import Mathlib.CategoryTheory.Center.Linear
import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Kernels
import WeilConjectures.NumberTheory.Padics.ContinuousUniformizerDivision
import Mathlib.Topology.Algebra.Order.Field
import WeilConjectures.Mathlib.CategoryTheory.Functor.Flat
import Mathlib.CategoryTheory.Abelian.DiagramLemmas.KernelCokernelComp
import Mathlib.CategoryTheory.Sites.Sheafification
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvr
import Mathlib.Algebra.Order.AbsoluteValue.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Localization.FractionRing
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrCore
import Mathlib.Analysis.Normed.Algebra.Ultra
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.Topology.Algebra.Valued.LocallyCompact
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorization
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorizationUnique
import WeilConjectures.Mathlib.RingTheory.OrderOfVanishing.Noetherian
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicFiniteTorsionConstructibility
import all WeilConjectures.Algebra.Homology.ProEtaleCoefficients.SuccessiveQuotientFlatTensorSequence
import all WeilConjectures.SixFunctors.Supporting.StrictDvrFlatTensorSequence
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import WeilConjectures.AlgebraicGeometry.Completed.CompletedCoefficientRegularQuotients
import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteScalarRestrictionConstructible
import WeilConjectures.AlgebraicGeometry.ProEtale.Bounded.ProEtaleBoundedConstructibleTriangulated
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.AlgebraicGeometry.IntegralCriterionReductions
public import Mathlib.CategoryTheory.EssentiallySmall
public import WeilConjectures.AlgebraicGeometry.AdicCompletion.InternalRoosCompleteness
public import WeilConjectures.AlgebraicGeometry.Morphisms.ProAffineEtale
public import WeilConjectures.CategoryTheory.Grothendieck.GrothendieckTopos
public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import WeilConjectures.AlgebraicGeometry.AdicCompletion.InternalRoosCompleteness
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.ProetaleSiteProperties
public import WeilConjectures.ProEtaleCoefficients.DerivedNakayamaResolution

/-!
# Constructibility of all integral reductions from the first

Source: blueprint main-20261015, sec-proetale-coefficients,
sk-prop-integral-criterion/sk-prop-integral-criterion-reductions.md
(blueprint: det-prop-integral-criterion-reductions).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

attribute [local irreducible] upperStarFromPoint

private theorem finiteConstantEndomorphism (X : Scheme.{u})
    (h : sfbFiniteConstantSets X ⟶ sfbFiniteConstantSets X) : h = 𝟙 _ := by
  let J := Scheme.ProEt.topology X
  let O := FintypeCat.of (ULift.{u} Unit)
  let F := sfbFiniteConstantSets X
  have ht : IsTerminal (ULift.{u + 1, u} (ULift.{u} Unit)) :=
    (Types.isTerminalEquivUnique _).symm inferInstance
  have ht' : IsTerminal (F.obj O) :=
    (ht.isTerminalObj (constantSheaf J (Type (u + 1))) _).isTerminalObj
      (sheafToPresheaf J (Type (u + 1))) _
  have hO : h.app O = 𝟙 _ := ht'.hom_ext _ _
  apply NatTrans.ext
  funext T
  apply sheafify_hom_ext J _ _
    (((constantSheaf J (Type (u + 1))).obj (ULift.{u + 1, u} T)).property)
  ext V x
  let k : O ⟶ T := FintypeCat.homMk fun _ ↦ x.down
  let z := (toSheafify J ((Functor.const X.ProEtᵒᵖ).obj
    (ULift.{u + 1, u} (ULift.{u} Unit)))).app V (ULift.up (ULift.up ()))
  have hn := congrArg (fun t ↦ t.app V) (h.naturality k)
  rw [hO, Category.id_comp] at hn
  have hc : (F.map k).app V z =
      (toSheafify J ((Functor.const X.ProEtᵒᵖ).obj (ULift.{u + 1, u} T))).app V x := by
    exact (congrArg (fun t ↦ t.app V
      (ULift.up (ULift.up () : ULift.{u} Unit))) (toSheafify_naturality J
      ((Functor.const X.ProEtᵒᵖ).map
        (uliftFunctor.{u + 1, u}.map ((forget FintypeCat).map k))))).symm
  change (h.app T).app V
      ((toSheafify J ((Functor.const X.ProEtᵒᵖ).obj (ULift.{u + 1, u} T))).app V x) =
    (toSheafify J ((Functor.const X.ProEtᵒᵖ).obj (ULift.{u + 1, u} T))).app V x
  rw [← hc]
  exact congrArg (fun t ↦ t z) hn

private theorem finiteRepresentation_unique (X : Scheme.{u})
    (a b : sfbFiniteConstantSets X ≅ sfbFiniteRepresentables X) : a = b := by
  apply Iso.ext
  have h := finiteConstantEndomorphism X (a.hom ≫ b.inv)
  have h' := congrArg (fun f ↦ f ≫ b.hom) h
  simpa using h'

private theorem continuousRingSheaf_topology_eq (T : Type u) [Ring T]
    (t₁ t₂ : TopologicalSpace T) (h : t₁ = t₂)
    (h₁ : @IsTopologicalRing T t₁ _) (h₂ : @IsTopologicalRing T t₂ _) :
    @Profinite.continuousMapRingSheafOfUniverse.{u, u} T t₁ _ h₁ =
      @Profinite.continuousMapRingSheafOfUniverse.{u, u} T t₂ _ h₂ := by
  subst t₂
  rfl

private theorem integralPointMon_eq (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] :
    Mon.mk (DerivedNakayama.integerRing l E) = sfbCondensedIntegers l E := by
  have hm : (spectralNorm.normedField (Padic l) E).toPseudoMetricSpace =
      (Padic.coefficientExtensionAbsoluteValue l E).toNormedField.toPseudoMetricSpace :=
    PseudoMetricSpace.ext (by
      ext x y
      change spectralNorm (Padic l) E (x - y) = spectralNorm (Padic l) E (-x + y)
      rw [neg_add_eq_sub, ← neg_sub x y,
        spectralNorm_neg (Algebra.IsAlgebraic.isAlgebraic _)])
  have ht := congrArg (fun m : PseudoMetricSpace E ↦
    m.toUniformSpace.toTopologicalSpace) hm.symm
  have hti := congrArg (fun t : TopologicalSpace E ↦
    TopologicalSpace.induced (fun x : Padic.coefficientExtensionIntegers l E ↦ (x : E)) t) ht
  have hs := continuousRingSheaf_topology_eq
    (Padic.coefficientExtensionIntegers l E) _ _ hti
    (by let := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField; infer_instance)
    (by let := spectralNorm.normedField (Padic l) E; infer_instance)
  let F : Sheaf (coherentTopology Profinite.{u}) RingCat.{u + 1} →
      Mon (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) := fun R ↦
    Mon.mk ((sheafCompose _ (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj R)
  exact congrArg F hs

private theorem ringPresheafMon_eq
    {C : Type*} [Category C] (J : GrothendieckTopology C)
    [HasWeakSheafify J Ab.{u + 1}] [(J.W (A := Ab.{u + 1})).IsMonoidal]
    (R : Sheaf J RingCat.{u + 1}) :
    (sheafToPresheaf J Ab.{u + 1}).monObjObj
      ((sheafCompose J (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj R) =
        R.obj.monObjCompForget₂ := by
  apply MonObj.ext
  let A := (sheafCompose J (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj R
  let : MonObj A.obj := R.obj.monObjCompForget₂
  exact Sheaf.μ_comp_map_mul A

private theorem liftSectionRingIso
    {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    [HasSheafify J Ab.{u + 1}] [(J.W (A := Ab.{u + 1})).IsMonoidal]
    (A : Sheaf J Ab.{u + 1}) [MonObj A] [IsCommMonObj A]
    (S : Sheaf J CommRingCat.{u + 1})
    (a : A ≅ (sheafCompose J (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj
      ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S))
    [IsMonHom a.hom] :
    ∃! e : InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u} J A ≅ S,
      (sheafCompose J
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙
          forget₂ RingCat.{u + 1} Ab.{u + 1})).map e.hom = a.hom := by
  let F := (Monoidal.monFunctorCategoryEquivalence Cᵒᵖ Ab.{u + 1}).functor
  let h := Functor.whiskerRight
    (F.map ((sheafToPresheaf J Ab.{u + 1}).mapMon.map (Mon.ofHom a.hom)))
    InternalAbelianSheafModule.monToRing
  let k := Functor.whiskerRight
    (F.map ((sheafToPresheaf J Ab.{u + 1}).mapMon.map (Mon.ofHom a.inv)))
    InternalAbelianSheafModule.monToRing
  let R := (sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S
  let B := (sheafCompose J (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj R
  have hmon : (sheafToPresheaf J Ab.{u + 1}).monObjObj B = R.obj.monObjCompForget₂ :=
    ringPresheafMon_eq J R
  let BP := F.obj ((sheafToPresheaf J Ab.{u + 1}).mapMon.obj (Mon.mk B)) ⋙
    InternalAbelianSheafModule.monToRing
  let b : BP ≅ R.obj := by
    refine NatIso.ofComponents (fun U ↦ ?_) (fun _ ↦ ?_)
    · refine @RingEquiv.toRingCatIso (BP.obj U) (R.obj.obj U)
        (RingCat.ring _) (RingCat.ring _) ?_
      refine { toEquiv := Equiv.refl _, map_add' := fun _ _ ↦ rfl, map_mul' := ?_ }
      intro x y
      change (((sheafToPresheaf J Ab.{u + 1}).monObjObj B).mul.app U).hom
        (TensorProduct.tmul ℤ x y) = _
      have hh := congrArg (fun m : MonObj B.obj ↦ m.mul) hmon
      rw [hh]
      rfl
    · ext x
      rfl
  let d : InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u} J A ≅ S :=
    { hom := ⟨{ app := fun U ↦
                  @CommRingCat.ofHom
                    ((InternalAbelianSheafModule.sectionRingSheaf J A).obj.obj U)
                    (S.obj.obj U) _ _ ((h ≫ b.hom).app U).hom
                naturality := fun U V f ↦ by
                  apply (forget₂ CommRingCat RingCat).map_injective
                  exact (h ≫ b.hom).naturality f }⟩
      inv := ⟨{ app := fun U ↦
                  @CommRingCat.ofHom (S.obj.obj U)
                    ((InternalAbelianSheafModule.sectionRingSheaf J A).obj.obj U)
                    _ _ ((b.inv ≫ k).app U).hom
                naturality := fun U V f ↦ by
                  apply (forget₂ CommRingCat RingCat).map_injective
                  exact (b.inv ≫ k).naturality f }⟩
      hom_inv_id := by
        ext U x
        have hh := congr_app (congrArg (fun f : A ⟶ A ↦ f.hom) a.hom_inv_id) U
        exact ConcreteCategory.congr_hom hh x
      inv_hom_id := by
        ext U x
        have hh := congr_app (congrArg (fun f : B ⟶ B ↦ f.hom) a.inv_hom_id) U
        exact ConcreteCategory.congr_hom hh x }
  have hd : (sheafCompose J
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙
        forget₂ RingCat.{u + 1} Ab.{u + 1})).map d.hom = a.hom := by
    ext U x
    rfl
  refine ⟨d, hd, ?_⟩
  intro e he
  apply Iso.ext
  apply (sheafCompose J
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙
      forget₂ RingCat.{u + 1} Ab.{u + 1})).map_injective
  exact he.trans hd.symm

private noncomputable def restrictionRoundTrip
    {C : Type (u + 1)} [Category.{u} C] {J : GrothendieckTopology C}
    {R S : Sheaf J RingCat.{u + 1}} (c : R ≅ S) :
    SheafOfModules.restrictScalars.{u + 1} c.hom ⋙
      SheafOfModules.restrictScalars c.inv ≅ 𝟭 (SheafOfModules.{u + 1} S) :=
  NatIso.ofComponents (fun M ↦ (SheafOfModules.fullyFaithfulForget S).preimageIso
    (PresheafOfModules.isoMk (fun U ↦
      (ModuleCat.restrictScalarsComp'App (c.inv.hom.app U).hom
        (c.hom.hom.app U).hom (RingHom.id _) (by
          have h := congr_app (congrArg (fun f : S ⟶ S ↦ f.hom) c.inv_hom_id) U
          exact (congrArg RingCat.Hom.hom h).symm) (M.val.obj U)).symm ≪≫
        ModuleCat.restrictScalarsId'App (RingHom.id _) rfl (M.val.obj U))
      (by intro U V f; ext x; rfl)))
    (by intro M N f; ext U x; rfl)

private theorem restrictionTriangle
    {C : Type (u + 1)} [Category.{u} C] {J : GrothendieckTopology C}
    {R S : Sheaf J RingCat.{u + 1}} (c : R ≅ S) (M : SheafOfModules.{u + 1} S) :
    (SheafOfModules.restrictScalars c.hom).map ((restrictionRoundTrip c).inv.app M) ≫
      (restrictionRoundTrip c.symm).hom.app
        ((SheafOfModules.restrictScalars c.hom).obj M) = 𝟙 _ := by
  ext U x
  rfl

private noncomputable def restrictionEquivalence
    {C : Type (u + 1)} [Category.{u} C] {J : GrothendieckTopology C}
    {R S : Sheaf J RingCat.{u + 1}} (c : R ≅ S) :
    SheafOfModules.{u + 1} S ≌ SheafOfModules.{u + 1} R where
  functor := SheafOfModules.restrictScalars c.hom
  inverse := SheafOfModules.restrictScalars c.inv
  unitIso := (restrictionRoundTrip c).symm
  counitIso := restrictionRoundTrip c.symm
  functor_unitIso_comp := restrictionTriangle c

private theorem restriction_isEquivalence
    {C : Type (u + 1)} [Category.{u} C] {J : GrothendieckTopology C}
    {R S : Sheaf J RingCat.{u + 1}} (c : R ≅ S) :
    (SheafOfModules.restrictScalars.{u + 1} c.hom).IsEquivalence :=
  (restrictionEquivalence c).isEquivalence_functor

/-- Localization of the fixed section-action equivalence on unbounded complexes.
Its forward functor is the localization of integralSectionFunctor, with Mathlib's
canonical localization comparison on every complex.
Source: Stacks 05RU; blueprint integral-criterion proof step 8
(blueprint: det-prop-integral-criterion-reductions). -/
def integralSectionDerivedEquivalence (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) :
    DerivedCategory (AdicCompletion.Modules l E X) ≌
      DerivedCategory (WeilConjectures.scalarReductionSource.{u, u} l E X) :=
  letI : (integralSectionFunctor l E X).asEquivalence.functor.Additive :=
    (integralSectionFunctor_properties l E X).1
  (integralSectionFunctor l E X).asEquivalence.mapDerivedCategory

private def integralEncoding (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) : IntegralPresentation.Encoding l E X where
  ringIso := integralSectionRingIso l E X
  modules := (integralSectionFunctor l E X).asEquivalence
  functor_eq := rfl
  additive := by
    change (integralSectionFunctor l E X).Additive
    infer_instance
  inverseAdditive := by
    let : (integralSectionFunctor l E X).asEquivalence.functor.Additive :=
      inferInstanceAs (integralSectionFunctor l E X).Additive
    infer_instance

private theorem finiteTopology_discrete (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (n : ℕ) :
    letI := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
    DiscreteTopology (Padic.coefficientExtensionRing l E (n + 1)) := by
  let := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  have hm : (spectralNorm.normedField (Padic l) E).toPseudoMetricSpace =
      (Padic.coefficientExtensionAbsoluteValue l E).toNormedField.toPseudoMetricSpace :=
    PseudoMetricSpace.ext (by
      ext x y
      change spectralNorm (Padic l) E (x - y) = spectralNorm (Padic l) E (-x + y)
      rw [neg_add_eq_sub, ← neg_sub x y,
        spectralNorm_neg (Algebra.IsAlgebraic.isAlgebraic _)])
  have ht := congrArg (fun m : PseudoMetricSpace E ↦
    m.toUniformSpace.toTopologicalSpace) hm
  have hti := congrArg (fun t : TopologicalSpace E ↦
    TopologicalSpace.induced (fun x : Padic.coefficientExtensionIntegers l E ↦ (x : E)) t) ht
  apply QuotientAddGroup.discreteTopology
  apply AddSubgroup.isOpen_of_mem_nhds (g := 0)
  have hb := (Padic.coefficientExtension_integers_coset_basis l E 0).mem_of_mem
    (i := n) trivial
  change @Membership.mem (Set (Padic.coefficientExtensionIntegers l E)) _ _
    (@nhds _ (TopologicalSpace.induced _ _) 0) _ at hb
  change @Membership.mem (Set (Padic.coefficientExtensionIntegers l E)) _ _
    (@nhds _ (TopologicalSpace.induced _ _) 0) _
  rw [← hti]
  have he : {y : Padic.coefficientExtensionIntegers l E |
      Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1)) y =
        Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1)) 0} =
      (Padic.coefficientExtensionIdeal l E (n + 1)).toAddSubgroup := by
    ext y
    change _ = _ ↔ y ∈ Padic.coefficientExtensionIdeal l E (n + 1)
    rw [map_zero, Ideal.Quotient.eq_zero_iff_mem]
  rw [he] at hb
  exact hb

private theorem finiteEncoding_ringIso_unique
    (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    (X : Scheme.{u}) (e f : FiniteDiscreteOrdinary.Encoding A X) :
    e.ringIso = f.ringIso := by
  apply Iso.ext
  apply Sheaf.hom_ext
  apply sheafify_hom_ext (Scheme.ProEt.topology X) _ _
    (FiniteDiscreteOrdinary.sectionRing A X).property
  ext U a
  exact (e.normalization U a).trans (f.normalization U a).symm

private theorem finiteEncoding_functor_eq
    (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    (X : Scheme.{u}) (e f : FiniteDiscreteOrdinary.Encoding A X) :
    e.ordinary.functor = f.ordinary.functor := by
  rw [e.ordinary_functor, f.ordinary_functor, finiteEncoding_ringIso_unique A X e f]

private theorem finiteBounded_iso
    (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [Finite A]
    (X : Scheme.{u}) {K L : Scheme.proEtaleDerivedCategory X A} (e : K ≅ L) :
    FiniteDiscreteOrdinary.ordinaryIntrinsicBoundedConstructible A X K ↔
      FiniteDiscreteOrdinary.ordinaryIntrinsicBoundedConstructible A X L := by
  constructor
  · intro h
    exact ⟨DerivedCategory.TStructure.t.bounded.prop_of_iso e h.1,
      fun q ↦ FiniteDiscreteOrdinary.constructible_of_iso A X
        ((DerivedCategory.homologyFunctor _ q).mapIso e) (h.2 q)⟩
  · intro h
    exact ⟨DerivedCategory.TStructure.t.bounded.prop_of_iso e.symm h.1,
      fun q ↦ FiniteDiscreteOrdinary.constructible_of_iso A X
        ((DerivedCategory.homologyFunctor _ q).mapIso e.symm) (h.2 q)⟩

private theorem finiteEncoding_constructible
    (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [Finite A] [DiscreteTopology A] (X : Scheme.{u}) [IsNoetherian X]
    (e : FiniteDiscreteOrdinary.Encoding A X)
    (K : DerivedCategory (FiniteDiscreteOrdinary.Internal A X)) :
    constantModelBoundedConstructible (FiniteDiscreteOrdinary.coefficient A) X K ↔
      FiniteDiscreteOrdinary.ordinaryIntrinsicBoundedConstructible A X
        (e.ordinaryDerived.functor.obj K) := by
  obtain ⟨f, hf⟩ := FiniteDiscreteOrdinary.finiteCoefficientModelComparison A X
  have h := finiteEncoding_functor_eq A X e f
  exact (hf.boundedConstructible K).trans
    (finiteBounded_iso A X
      ((Functor.mapDerivedCategoryNatIso (eqToIso h)).app K).symm)

private theorem reflect_roos_complete
    {C D : Type*} [Category C] [Category D] [HasZeroObject C] [HasZeroObject D]
    [HasShift C ℤ] [HasShift D ℤ] [Preadditive C] [Preadditive D]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [∀ n : ℤ, (shiftFunctor D n).Additive]
    [Pretriangulated C] [Pretriangulated D]
    (F : C ⥤ D) [F.Additive] [F.CommShift ℤ] [F.IsTriangulated] [F.IsEquivalence]
    {V : ℕ → C} {W : ℕ → D} [HasProduct V] [HasProduct W]
    (t : ∀ n, V (n + 1) ⟶ V n) (s : ∀ n, W (n + 1) ⟶ W n)
    (a : ∀ n, F.obj (V n) ≅ W n)
    (K : C) (p : ∀ n, K ⟶ V n) (q : ∀ n, F.obj K ⟶ W n)
    (ht : ∀ n, F.map (t n) ≫ (a n).hom = (a (n + 1)).hom ≫ s n)
    (hp : ∀ n, F.map (p n) ≫ (a n).hom = q n)
    (δ : (∏ᶜ W) ⟶ (F.obj K)⟦(1 : ℤ)⟧)
    (hT : IsDerivedLimitTriangle s (F.obj K) (Pi.lift q) δ) :
    ∃ δ' : (∏ᶜ V) ⟶ K⟦(1 : ℤ)⟧,
      IsDerivedLimitTriangle t K (Pi.lift p) δ' := by
  let : HasProduct (fun n ↦ F.obj (V n)) :=
    hasLimit_of_iso (Discrete.natIso (F := Discrete.functor W)
      (G := Discrete.functor (fun n ↦ F.obj (V n))) (fun n ↦ (a n.as).symm))
  let B : F.obj (∏ᶜ V) ≅ ∏ᶜ W := PreservesProduct.iso F V ≪≫
    { hom := Limits.Pi.map (fun n ↦ (a n).hom)
      inv := Limits.Pi.map (fun n ↦ (a n).inv)
      hom_inv_id := by apply Pi.hom_ext; intro n; simp [Category.assoc]
      inv_hom_id := by apply Pi.hom_ext; intro n; simp [Category.assoc] }
  have hB (n : ℕ) : B.hom ≫ Pi.π W n = F.map (Pi.π V n) ≫ (a n).hom := by
    simp [B]
  have hfirst : F.map (Pi.lift p) ≫ B.hom = Pi.lift q := by
    apply Pi.hom_ext
    intro n
    simp only [Category.assoc, hB, Pi.lift_π]
    rw [← Category.assoc, ← F.map_comp, Pi.lift_π, hp]
  have hmiddle : F.map (towerTransitionEndomorphism t) ≫ B.hom =
      B.hom ≫ towerTransitionEndomorphism s := by
    apply Pi.hom_ext
    intro n
    simp only [Category.assoc, hB, towerTransitionEndomorphism, towerProductShift,
      Preadditive.comp_sub, Preadditive.sub_comp, Category.comp_id,
      Pi.lift_π, Functor.map_sub]
    simp only [reassoc_of% hB]
    erw [F.map_id, Category.id_comp]
    congr 1
    rw [← F.map_comp_assoc, Pi.lift_π, Functor.map_comp, Category.assoc, ht]
  let δ' := F.preimage (B.hom ≫ δ ≫ (F.commShiftIso (1 : ℤ)).inv.app K)
  refine ⟨δ', (F.map_distinguished_iff _).mp ?_⟩
  apply Pretriangulated.isomorphic_distinguished _ hT _
  refine Pretriangulated.Triangle.isoMk _ _ (Iso.refl _) B B ?_ ?_ ?_
  · change F.map (Pi.lift p) ≫ B.hom = 𝟙 _ ≫ Pi.lift q
    simpa only [Category.id_comp] using hfirst
  · exact hmiddle
  · change (F.map δ' ≫ (F.commShiftIso (1 : ℤ)).hom.app K) ≫
      (shiftFunctor D (1 : ℤ)).map (𝟙 _) = B.hom ≫ δ
    erw [(shiftFunctor D (1 : ℤ)).map_id]
    simp only [δ', F.map_preimage, Category.assoc, Iso.inv_hom_id_app]
    simp only [Functor.comp_obj, Category.comp_id]

private theorem finiteSupport_of_interval
    {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    (K : DerivedCategory C) (a b : ℤ)
    (h : ∀ q : ℤ, q < a ∨ b < q → IsZero ((DerivedCategory.homologyFunctor C q).obj K)) :
    Set.Finite {q : ℤ | ¬ IsZero ((DerivedCategory.homologyFunctor C q).obj K)} := by
  apply (Set.finite_Icc a b).subset
  intro q hq
  by_contra hn
  exact hq (h q (by simpa only [Set.mem_Icc, not_and_or, not_le] using hn))

private theorem bounded_of_interval
    {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    (K : DerivedCategory C) (a b : ℤ)
    (h : ∀ q : ℤ, q < a ∨ b < q → IsZero ((DerivedCategory.homologyFunctor C q).obj K)) :
    DerivedCategory.TStructure.t.bounded K := by
  exact ⟨⟨a, (DerivedCategory.isGE_iff K a).mpr (fun q hq ↦ h q (Or.inl hq))⟩,
    ⟨b, (DerivedCategory.isLE_iff K b).mpr (fun q hq ↦ h q (Or.inr hq))⟩⟩

private theorem support_subset_iff_interval
    {X : Scheme.{u}} {A : Type u} [CommRing A]
    (K : Scheme.proEtaleDerivedCategory X A) (a b : ℤ) :
    Scheme.proEtaleCohomologicalSupport K ⊆ Set.Icc a b ↔
      ∀ q : ℤ, q < a ∨ b < q → IsZero ((DerivedCategory.homologyFunctor _ q).obj K) := by
  classical
  constructor
  · intro h q hq
    by_contra hz
    have hh := h hz
    rcases hq with hq | hq
    · exact (not_lt_of_ge hh.1) hq
    · exact (not_lt_of_ge hh.2) hq
  · intro h q hq
    by_contra hn
    exact hq (h q (by simpa only [Set.mem_Icc, not_and_or, not_le] using hn))

/-- The continuous predicate is the existing integral predicate under the canonical
coefficient and section-action comparison, rather than an unrelated new notion.
Source: blueprint integral-criterion final sentence, proof step 8
(blueprint: det-prop-integral-criterion-reductions).
Proof: the finite projections of integralSectionRingIso are the specified quotient
maps by its underlying integral-limit normalization. On a K-flat representative,
the section-action equivalence identifies tensoring with each quotient with the
recorded scalarReductionDerivedExtension; this also identifies the quotient units
and transitions. Exact equivalences preserve products and the augmented Roos
triangle, so IsDerivedComplete agrees with IsSfDerivedComplete. At each positive
finite level the continuous ring is constant. Finite constant local models agree
with locally constant finite modules: finite presentation over a finite ring gives
a finite module, and a finite module has a finite presentation. The Noetherian
finite stratifications agree. Finally homology is preserved by the exact
equivalence, and support in [r,s] means precisely vanishing outside [r,s]. These
identifications give both implications, including the same uniform interval. -/
theorem continuousIntegralConstructible_iff_sfIntegralConstructible (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) [IsNoetherian X] (K : DerivedCategory (AdicCompletion.Modules l E X)) :
    continuousIntegralConstructible l E X K ↔
      WeilConjectures.sfIntegralConstructible l E X
        ((integralSectionDerivedEquivalence l E X).functor.obj K) := by
  classical
  let := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  let A := integralEncoding l E X
  obtain ⟨e, a, ha⟩ := IntegralPresentation.fixed_integral_section_squares l E X A
    (integralLimitAbComparison l E X)
    (integralLimitAbComparison_existsUnique l E X).exists.choose_spec
    (integralSectionAbIdentifications l E X).1
    (integralSectionAbIdentifications l E X).2
    (integralSectionRingIso_existsUnique l E X).exists.choose_spec
  have hb (n : ℕ) := IntegralPresentation.finiteComparison_existsUnique l E X A n (e n) (a n)
  choose b hbu _ using hb
  have ht := IntegralPresentation.integral_completion_transition_comparison l E X A e a ha b hbu
  let : A.derived.functor.Additive :=
    by change A.modules.functor.mapDerivedCategory.Additive; infer_instance
  let : A.derived.functor.CommShift ℤ :=
    by change A.modules.functor.mapDerivedCategory.CommShift ℤ; infer_instance
  let : A.derived.functor.IsTriangulated :=
    by change A.modules.functor.mapDerivedCategory.IsTriangulated; infer_instance
  let : HasCountableProducts (DerivedCategory (WeilConjectures.scalarReductionSource l E X)) :=
    IntegralPresentation.completedProducts l E X
  let : HasCountableProducts (DerivedCategory (AdicCompletion.Modules l E X)) :=
    { out := fun I _ ↦ Adjunction.hasLimitsOfShape_of_equivalence A.derived.functor }
  have hcomplete : IsDerivedComplete l E X K ↔
      WeilConjectures.IsSfDerivedComplete l E X (A.derived.functor.obj K) := by
    constructor
    · intro hK
      exact (IntegralPresentation.integral_completion_presentation.{u, u} l E X A e a ha K hK).1
    · rintro ⟨hp, δ, hδ⟩
      let := hp
      have ht' (n : ℕ) :
          A.derived.functor.map (AdicCompletion.integralStep l E X K n) ≫
              (IntegralPresentation.restrictedComparison l E X A n (e n) (a n)
                (b n) K).inv =
            (IntegralPresentation.restrictedComparison l E X A (n + 1) (e (n + 1))
              (a (n + 1)) (b (n + 1)) K).inv ≫
                (WeilConjectures.sfDerivedReductionTransition l E X n).app
                  (A.derived.functor.obj K) := by
        have h := ht K n
        change (WeilConjectures.sfDerivedReductionTransition l E X n).app
            (A.derived.functor.obj K) ≫
              (IntegralPresentation.restrictedComparison l E X A n (e n) (a n)
                (b n) K).hom =
            (IntegralPresentation.restrictedComparison l E X A (n + 1) (e (n + 1))
              (a (n + 1)) (b (n + 1)) K).hom ≫
                A.derived.functor.map (AdicCompletion.integralStep l E X K n) at h
        apply (cancel_epi (IntegralPresentation.restrictedComparison l E X A (n + 1)
          (e (n + 1)) (a (n + 1)) (b (n + 1)) K).hom).mp
        simpa only [← Category.assoc, Iso.hom_inv_id, Category.id_comp,
          Category.assoc, Iso.hom_inv_id_assoc, Category.comp_id] using
          congrArg (fun f ↦ f ≫
            (IntegralPresentation.restrictedComparison l E X A n (e n) (a n) (b n) K).inv)
            h.symm
      have hu' (n : ℕ) :
          A.derived.functor.map ((Mod.derivedExtendMapDerivedCategoryAdjunction
            (AdicCompletion.quotient l E X n)).unit.app K) ≫
              (IntegralPresentation.restrictedComparison l E X A n (e n) (a n)
                (b n) K).inv =
            (WeilConjectures.sfDerivedReductionUnit l E X n).app
              (A.derived.functor.obj K) := by
        simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using
          congrArg (fun f ↦ f ≫
            (IntegralPresentation.restrictedComparison l E X A n (e n) (a n) (b n) K).inv)
            (hbu n K).symm
      obtain ⟨δ', hδ'⟩ := reflect_roos_complete
        (V := AdicCompletion.integralLevel l E X K)
        (W := fun n ↦ (WeilConjectures.sfDerivedReductionRestricted l E X n).obj
          (A.derived.functor.obj K)) A.derived.functor
        (AdicCompletion.integralStep l E X K)
        (fun n ↦ (WeilConjectures.sfDerivedReductionTransition l E X n).app
          (A.derived.functor.obj K))
        (fun n ↦ (IntegralPresentation.restrictedComparison l E X A n (e n) (a n)
          (b n) K).symm) K
        (fun n ↦ (Mod.derivedExtendMapDerivedCategoryAdjunction
          (AdicCompletion.quotient l E X n)).unit.app K)
        (fun n ↦ (WeilConjectures.sfDerivedReductionUnit l E X n).app
          (A.derived.functor.obj K))
        (by simpa only [Iso.symm_hom] using ht')
        (by simpa only [Iso.symm_hom] using hu') δ hδ
      exact AdicCompletion.isDerivedComplete_of_roos l E X K δ' hδ'
  let (n : ℕ) : Finite (Padic.coefficientExtensionRing l E (n + 1)) :=
    Padic.finite_coefficientExtensionRing l E (n + 1) (by omega)
  let (n : ℕ) : DiscreteTopology (Padic.coefficientExtensionRing l E (n + 1)) :=
    finiteTopology_discrete l E n
  have hmodel (n : ℕ) :
      constantModelBoundedConstructible (DerivedNakayama.quotientRing l E (n + 1)) X
          ((AdicCompletion.derivedReduction l E X n).obj K) ↔
        FiniteDiscreteOrdinary.ordinaryIntrinsicBoundedConstructible
          (Padic.coefficientExtensionRing l E (n + 1)) X
          ((WeilConjectures.scalarReductionDerivedExtension l E X n).obj
            (A.derived.functor.obj K)) := by
    let := Padic.finite_coefficientExtensionRing l E (n + 1) (by omega)
    exact (finiteEncoding_constructible (Padic.coefficientExtensionRing l E (n + 1)) X
      (e n) _).trans (finiteBounded_iso _ X ((b n).app K).symm)
  have hbounds (n : ℕ) (r s : ℤ) :
      (∀ q : ℤ, q < r ∨ s < q →
        IsZero ((DerivedCategory.homologyFunctor _ q).obj
          ((AdicCompletion.derivedReduction l E X n).obj K))) ↔
      (∀ q : ℤ, q < r ∨ s < q →
        IsZero ((DerivedCategory.homologyFunctor _ q).obj
          ((WeilConjectures.scalarReductionDerivedExtension l E X n).obj
            (A.derived.functor.obj K)))) := by
    apply forall_congr'
    intro q
    apply imp_congr_right
    intro _
    exact (show IsZero ((DerivedCategory.homologyFunctor _ q).obj
        ((AdicCompletion.derivedReduction l E X n).obj K)) ↔
      IsZero ((DerivedCategory.homologyFunctor _ q).obj
        ((e n).ordinaryDerived.functor.obj
          ((AdicCompletion.derivedReduction l E X n).obj K))) from
      ⟨(e n).ordinary.functor.isZero_homologyFunctor_mapDerivedCategory_obj,
        Functor.isZero_homologyFunctor_of_isZero_homologyFunctor_mapDerivedCategory_obj
          (e n).ordinary.functor⟩).trans
        ((DerivedCategory.homologyFunctor _ q).mapIso ((b n).app K)).isZero_iff.symm
  change _ ↔ WeilConjectures.sfIntegralConstructible l E X (A.derived.functor.obj K)
  constructor
  · rintro ⟨hK, hcons, r, s, hrs, hv⟩
    refine ⟨hcomplete.mp hK, r, s, hrs, fun n ↦ ?_⟩
    have hc := (hmodel n).mp (hcons n)
    have hz := (hbounds n r s).mp (hv n)
    exact ⟨⟨finiteSupport_of_interval _ r s hz, hc.2⟩,
      (support_subset_iff_interval _ r s).mpr hz⟩
  · rintro ⟨hK, r, s, hrs, h⟩
    have hv (n : ℕ) := (support_subset_iff_interval _ r s).mp (h n).2
    refine ⟨hcomplete.mpr hK, fun n ↦ ?_, r, s, hrs, fun n ↦ (hbounds n r s).mpr (hv n)⟩
    apply (hmodel n).mpr
    exact ⟨bounded_of_interval _ r s (hv n), (h n).1.2⟩

attribute [local irreducible] WeilConjectures.scalarReductionExistence
  WeilConjectures.scalarReductionDerivedExistence

private theorem reductionAbSheafify (X : Scheme.{u}) :
    HasSheafify (Scheme.ProEt.topology X) Ab.{u + 1} :=
  WeilConjectures.integralCoefficientAbSheafify.{u, u} X

private theorem reductionAbLocallyBijective (X : Scheme.{u}) :
    (Scheme.ProEt.topology X).WEqualsLocallyBijective Ab.{u + 1} :=
  WeilConjectures.integralCoefficientAbLocallyBijective.{u, u} X

private theorem reductionSiteSmall (X : Scheme.{u}) : EssentiallySmall.{u + 1} X.ProEt :=
  essentiallySmallSelf.{0, u, u + 1} _

private abbrev finiteScalarRestriction (X : Scheme.{u})
    {A B : Type u} [CommRing A] [CommRing B] (a : A →+* B) :=
  Scheme.proEtaleRingRestrictScalars
    ((constantSheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}).map
      (CommRingCat.ofHom (R := ULift.{u + 1, u} A)
        (S := ULift.{u + 1, u} B) a.ulift.{u + 1, u + 1}))

attribute [local instance] reductionSiteSmall

attribute [local instance] reductionAbSheafify reductionAbLocallyBijective reductionRingSheafify

attribute [local instance] WeilConjectures.scalarReductionExtensionAdditive
  WeilConjectures.scalarReductionRestrictionLimits
  WeilConjectures.scalarReductionRestrictionColimits
  Scheme.proEtaleRingRestrictScalars_preservesFiniteLimits
  Scheme.proEtaleRingRestrictScalars_preservesFiniteColimits

private def tensorCoefficientIso
    {C : Type (u + 1)} [Category.{u} C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})]
    [J.WEqualsLocallyBijective Ab.{u + 1}] [HasSheafify J Ab.{u + 1}]
    {B : Sheaf J CommRingCat.{u + 1}}
    {M N : SheafOfModules.{u + 1}
      ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj B)} (e : M ≅ N) :
    SheafOfModules.leftTensorSheaf M ≅ SheafOfModules.leftTensorSheaf N :=
  NatIso.ofComponents (fun P ↦ (SheafOfModules.siteSheafTensorRight P).mapIso e)
    (fun f ↦ (SheafOfModules.siteSheafTensorSecondMap_naturality e.hom f).symm)

end AlgebraicGeometry.ProEtale
