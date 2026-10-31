/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

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
public import WeilConjectures.AlgebraicGeometry.ProfiniteFiniteConstantLocalModel
public import WeilConjectures.AlgebraicGeometry.ProEtaleModuleObjects
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.CategoryTheory.Monoidal.Mon
public import WeilConjectures.AlgebraicGeometry.CoefficientHeartStratificationDefs
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMap

import WeilConjectures.AlgebraicGeometry.ProEtaleModuleStalkFunctor
import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImageStalk
import WeilConjectures.AlgebraicGeometry.ProEtaleClassicalStalk
import WeilConjectures.CategoryTheory.ModuleObjects.MapMod
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
import WeilConjectures.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.CategoryTheory.Sites.Over
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.CategoryTheory.Sites.CoverLifting
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
import WeilConjectures.AlgebraicGeometry.CoefficientSectionsLocalization
import WeilConjectures.AlgebraicGeometry.StrictHenselizationLocalStructure
import WeilConjectures.AlgebraicGeometry.StrictHenselizationExtension
import WeilConjectures.AlgebraicGeometry.Sites.StrictHenselizationLocal
import WeilConjectures.Mathlib.RingTheory.Henselian
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import WeilConjectures.AlgebraicGeometry.ScalarMatrixInverseImage
import WeilConjectures.AlgebraicGeometry.StrictHenselizationFunctoriality
import WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMap
import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.FieldTheory.IsSepClosed
import WeilConjectures.AlgebraicGeometry.StrictHenselizationPointedMap
import WeilConjectures.AlgebraicGeometry.StrictHenselizationPointEvaluationPointed
import WeilConjectures.AlgebraicGeometry.StrictHenselizationPointEvaluation
import WeilConjectures.AlgebraicGeometry.StrictHenselizationPointEvaluationProperties
import WeilConjectures.AlgebraicGeometry.StrictHenselizationPointEvaluationImage
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
import WeilConjectures.AlgebraicGeometry.StrictHenselizationPointEvaluationComparison
import WeilConjectures.AlgebraicGeometry.EtaleResidueTriples
import WeilConjectures.AlgebraicGeometry.EtaleLocalRingTriples
import WeilConjectures.RingTheory.StrictHenselizationTriples
import WeilConjectures.AlgebraicGeometry.EtalePointedMapRigidity
import WeilConjectures.AlgebraicGeometry.StrictHenselizationMapExists
import WeilConjectures.AlgebraicGeometry.CondensedPointCoefficients

/-! # Specialization of condensed geometric fibres

Source: Bhatt--Scholze, Proposition 6.8.4 and Stacks Project, Tag 0GJ2
(blueprint: lem-a1-condensed-fibre-specialization).
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u

open CategoryTheory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- Constructible condensed coefficient modules have natural specialization maps between
geometric fibres along the strict localization, and these maps are invertible for lisse modules.
Source: Bhatt--Scholze, Proposition 6.8.4 (1), (4), (6), Definition 6.8.6,
Proposition 6.8.14 and Remark 6.8.15; Stacks Project, Tag 0GJ2
(blueprint: lem-a1-condensed-fibre-specialization).

Proof: (1) By def-weil-proetale-geometric-stalk, the identity pointed neighbourhood
of an algebraically closed point is initial. Use lem-pur-proetale-inverse-image-stalk
and lem-cbc-proetale-classical-stalk to identify actual geometric inverse-image sections
with sections on the strict localization. det-def-sfb-change-of-scalars identifies
extension along the invertible coefficient comparison with restriction along its inverse;
all comparisons respect constant scalars by det-def-sfb-coefficient-morphisms.
(2) lem-weil-proetale-weakly-etale-localization and def-pur-localized-ringed-site identify
restriction to the strict localization with slice restriction. Use
lem-sfb-coefficient-sections-localization for coefficients and the unit and compositor of
det-def-sfb-module-pushforward-pullback to restrict further to the second geometric point.
(3) Compose these maps. Naturality of the first identification, the unit and the compositor
gives exactly the displayed naturality square; their scalar compatibility gives linearity.
(4) For a lisse module pull a trivializing cover to the strict localization using
lem-weil-pbc-weakly-etale-composition-base-change and lem-galois-fpqc-covering-base-change.
Its ring is strictly henselian local by lem-weil-pbc-strict-henselization-local-structure.
A cover member meeting the closed point admits a section: det-pe-wc-rings-local-iso
identifies its local ring there with the base, whose inverse gives a ring retraction.
Pull the trivialization back by this section; lem-sfb-scalar-matrix-inverse-image preserves
the resulting finite free model.
(5) lem-weil-pbc-strict-henselization-functoriality supplies the closed geometric lift.
The initial pointed-neighbourhood argument identifies sections of the coefficient ring
on the strict localization with sections at this lift. det-pe-condensed-point-coefficients
and det-def-sfb-qlbar-condensed identify the latter with the scalar field by constants.
Restriction to the second geometric point fixes every constant scalar, so is the identity.
(6) Finite sums of module sheaves have tuple-valued sections. By the scalar-matrix
inverse-image comparison the map on each finite free model is a finite product of the
identity of the scalar field, hence invertible, including rank zero. All other factors
in the construction are isomorphisms, which proves lisse invertibility. -/
theorem condensed_fibre_specialization
    (k : Type u) [Field k] [IsAlgClosed k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓp : ℓ ≠ p) (T : Scheme.{u})
    [T.Over (Spec (.of k))]
    [LocallyOfFiniteType (T ↘ Spec (.of k))]
    [QuasiCompact (T ↘ Spec (.of k))]
    [IsSeparated (T ↘ Spec (.of k))]
    (Ωs : Type u) [Field Ωs] [IsAlgClosed Ωs]
    (b : Spec (.of Ωs) ⟶ T)
    (Ωt : Type u) [Field Ωt] [IsAlgClosed Ωt]
    (a : Spec (.of Ωt) ⟶ Scheme.strictHenselizationScheme b) :
    ∃ sp :
        (ObjectProperty.ι (IsConstantModelConstructible (Profinite.padicAlgClRingObj ℓ) T)) ⋙
            (CondensedRing.upperStar (Profinite.padicAlgClRingObj ℓ) b) ⋙
              CondensedQbarGeometricEvaluation.fieldFiber Ωs ℓ ⟶
        (ObjectProperty.ι (IsConstantModelConstructible (Profinite.padicAlgClRingObj ℓ) T)) ⋙
            (CondensedRing.upperStar (Profinite.padicAlgClRingObj ℓ)
              (a ≫ Scheme.strictHenselizationStructuralMap b)) ⋙
              CondensedQbarGeometricEvaluation.fieldFiber Ωt ℓ,
      (∀ (N : ConstantModelConstructible (Profinite.padicAlgClRingObj ℓ) T),
        IsLisseCoefficientModule (Profinite.padicAlgClRingObj ℓ) N.obj →
          IsIso (sp.app N)) ∧
      ∀ (N N' : ConstantModelConstructible (Profinite.padicAlgClRingObj ℓ) T)
        (v : N ⟶ N'),
        sp.app N ≫
            (CondensedQbarGeometricEvaluation.fieldFiber Ωt ℓ).map
              ((CondensedRing.upperStar (Profinite.padicAlgClRingObj ℓ)
                (a ≫ Scheme.strictHenselizationStructuralMap b)).map v.hom) =
          (CondensedQbarGeometricEvaluation.fieldFiber Ωs ℓ).map
              ((CondensedRing.upperStar (Profinite.padicAlgClRingObj ℓ) b).map v.hom) ≫
            sp.app N' := by
  sorry

end AlgebraicGeometry.ProEtale
