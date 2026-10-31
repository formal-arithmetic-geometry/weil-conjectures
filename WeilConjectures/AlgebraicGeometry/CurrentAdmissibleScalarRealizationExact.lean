/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.LocalizingAdmissibleCoefficients
public import WeilConjectures.AlgebraicGeometry.FiniteConstantLocalModel
public import WeilConjectures.AlgebraicGeometry.CondensedScalarRealization
public import WeilConjectures.AlgebraicGeometry.AdmissibleScalarRealizationExactSupplement
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
import WeilConjectures.AlgebraicGeometry.InternalModuleAbEquivalence
import WeilConjectures.CategoryTheory.RingObjects.Ab
import Mathlib.CategoryTheory.Monoidal.Mod
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import WeilConjectures.SixFunctors.AdmissibleScalarHomologyData
import WeilConjectures.CategoryTheory.FiniteTypeConstantExact
import WeilConjectures.CategoryTheory.FiniteTypeLocallyConstantModuleSheaf
import WeilConjectures.AlgebraicGeometry.StrictPerfectCoefficientPackageSupplement
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Colimits
import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars
import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinaryEncodingSupplement
import WeilConjectures.AlgebraicGeometry.ProEtaleIntegralCoefficientLimit
import WeilConjectures.AlgebraicGeometry.ProEtaleIntegralCoefficientData
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import WeilConjectures.AlgebraicGeometry.ProEtalePointPullbackSupplement
import WeilConjectures.Topology.ContinuousMapCondensedRingSupplement
import WeilConjectures.NumberTheory.Padics.IntegersProfiniteTower
import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
import Mathlib.RingTheory.Ideal.Quotient.Index
import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.Algebra.Ring.Pi
import Mathlib.Topology.Homeomorph.Defs
import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Topology.Compactness.Compact
import WeilConjectures.NumberTheory.Padics.IntegersCosetBasis
import Mathlib.Topology.Bases
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Topology.Homeomorph.Lemmas
import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
import WeilConjectures.AlgebraicGeometry.CompletedIntegralCoefficientGerm
import WeilConjectures.AlgebraicGeometry.ProfiniteTestObjectFunctor
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.Topology.Category.Profinite.AsLimit
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.Topology.Category.Profinite.CofilteredLimit
import WeilConjectures.RingTheory.Spectrum.Prime.LocallyConstant
import WeilConjectures.AlgebraicGeometry.ProfiniteLocallyConstantAdjunction
import WeilConjectures.AlgebraicGeometry.ProEtaleFiniteConstantRepresentable
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.CategoryTheory.FintypeCat
import Mathlib.CategoryTheory.Sites.LocallyBijective
import WeilConjectures.AlgebraicGeometry.CoproductCopiesMorphismsClopen
import Mathlib.AlgebraicGeometry.OpenImmersion
import WeilConjectures.CategoryTheory.SheafPullbackForgetComparison
import Mathlib.CategoryTheory.Sites.Pullback
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.CategoryTheory.Limits.Presheaf
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
import WeilConjectures.AlgebraicGeometry.ProEtaleIntegralRingComparison
import WeilConjectures.AlgebraicGeometry.ProEtaleIntegralPointRingMap
import WeilConjectures.CategoryTheory.Sites.PushforwardMonoidal
import WeilConjectures.CategoryTheory.Sites.MonObj
import Mathlib.CategoryTheory.Sites.LocallySurjective
import Mathlib.CategoryTheory.Monoidal.Mon
import WeilConjectures.AlgebraicGeometry.IntegralConstantCompletion
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import WeilConjectures.CategoryTheory.RingedSiteModules
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
import WeilConjectures.AlgebraicGeometry.ConstantCompletionEquivalence
import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficientPullbackUniverses
import WeilConjectures.AlgebraicGeometry.ProEtaleRingInverseImage
import WeilConjectures.AlgebraicGeometry.CompletedIntegralCoefficientsSupplement
import WeilConjectures.SixFunctors.ProEtale.DerivedCompletionSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsCochainModel
import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import Mathlib.CategoryTheory.Limits.Final
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import WeilConjectures.Algebra.Homology.SheafRingDerivedCoefficientAdjunction
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctorialitySupplement
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import WeilConjectures.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction
import WeilConjectures.Algebra.Homology.SheafRingDerivedHomComparison
import WeilConjectures.CategoryTheory.DerivedCategory.ResolvingClassEssentialConstancy
import WeilConjectures.CategoryTheory.DerivedCategory.DerivedAdjunctionCompatibility
import Mathlib.CategoryTheory.MorphismProperty.Comma
import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import Mathlib.CategoryTheory.Functor.Derived.RightDerived
import WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantInd
import Mathlib.CategoryTheory.Filtered.Basic
import Mathlib.CategoryTheory.Limits.Cones
import WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantPro
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
import Mathlib.CategoryTheory.Functor.Derived.Adjunction
import Mathlib.CategoryTheory.Functor.KanExtension.Preserves
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedPointwiseKanBridge
import WeilConjectures.Algebra.Homology.QuasiIsoSaturatedTriangulated
import Mathlib.CategoryTheory.Functor.Derived.PointwiseRightDerived
import Mathlib.CategoryTheory.Adjunction.Restrict
import Mathlib.CategoryTheory.Adjunction.Unique
import WeilConjectures.AlgebraicGeometry.CoefficientSectionsLocalization

/-!
# Exact scalar realization for the current admissible coefficients

Source: current blueprint, det-thm-sf-ctf-stability-internal-hom, paragraphs 1--2;
det-prop-sfb-qlbar-colimit-x-integral-limit (3), and
det-prop-integral-criterion-constant-coefficients (1)
(blueprint: lem-sfb-admissible-scalar-realization-exact).

The algebraic-closure case is the finite-subextension-valued coefficient in
`IsLocalizingAdmissibleCoefficient`. The old module is imported only for its unchanged
integral comparison and flatness predicates, not its invalidated theorem.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CurrentAdmissibleScalarRealization

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- The existing scalar local-model functor restricted to the actual slice site.
Source: current internal-Hom stability proof, locality of scalar models;
Stacks 00Y0 (blueprint: lem-sfb-admissible-scalar-realization-exact). -/
def localizedScalarRealization (T : Scheme.{u}) (U : T.ProEt) :=
  finiteConstantScalarExtension Λ T ⋙
    InternalAbelianSheafModule.sectionModuleFunctor (Scheme.ProEt.topology T)
      (condensedRingObj Λ T) ⋙ SheafOfModules.overFunctor _ U

/-- Noetherian scalars and additive exact scalar realization, on T and each actual slice.
The domain of finiteConstantScalarExtension is all scalar modules, with no finiteness
condition. Source: current internal-Hom stability proof, paragraphs 1--2
(blueprint: lem-sfb-admissible-scalar-realization-exact). -/
def ScalarAssertions (T : Scheme.{u}) : Prop :=
  IsNoetherianRing (condensedScalarRing Λ) ∧
    (finiteConstantScalarExtension Λ T).Additive ∧
    PreservesFiniteLimits (finiteConstantScalarExtension Λ T) ∧
    PreservesFiniteColimits (finiteConstantScalarExtension Λ T) ∧
    ∀ U : T.ProEt, (localizedScalarRealization Λ T U).Additive ∧
      PreservesFiniteLimits (localizedScalarRealization Λ T U) ∧
      PreservesFiniteColimits (localizedScalarRealization Λ T U)

/-- Exact scalar realization for the six current admissible coefficients, together with
finite constant-function identification and the normalized integral limit and flatness
assertions, including flatness on all constant-ring sheaf modules on slices.

Source: current blueprint det-thm-sf-ctf-stability-internal-hom, paragraphs 1--2;
det-prop-sfb-qlbar-colimit-x-integral-limit (3), and
det-prop-integral-criterion-constant-coefficients (1)
(blueprint: lem-sfb-admissible-scalar-realization-exact).

Proof:
1. Singleton evaluation gives the usual scalar rings. Finite rings and fields are
Noetherian; the integral rings are DVRs, hence principal ideal rings and Noetherian.
For the algebraic closure a singleton value always lies in a finite subextension.
2. The second assertion of lem-sfb-admissible-scalar-homology-data supplies finite
limits for the existing finiteConstantScalarExtension, for every admissible coefficient.
Its internal scalar modules are ordinary modules by the internal-module equivalence.
3. Constant sheafification preserves finite colimits (Stacks 093J), as does scalar
extension, its left adjoint. On pure tensors the extension preserves addition and zero.
Preserving kernels and cokernels gives preservation of all short exact sequences.
4. For finite discrete A the canonical constant-function map is locally bijective:
use the clopen fibres of each function, including the empty cover and the zero ring.
Sheafification and inverse image therefore make the specified scalar map invertible.
5. The current integral coefficient limit theorem identifies the actual coefficient
with the positive constant quotient tower. Its projections send constants to residues;
this is exactly CompletedIdentification. Every uniformizer generates the same ideal.
The case E = Q_l gives Z_l with uniformizer l.
6. The current integral criterion (1) makes the canonical constant-scalar map flat
on all sheaf modules. This gives the finite-limit and finite-colimit assertions for
Mod.extendScalars in CompletedAssertions, not merely its constant-module restriction.
7. Coefficient-sections localization identifies the restricted coefficients with those
on the pro-etale object scheme. Constants, scalar maps, tensor products and quotient
projections restrict to the same constructions; repeat steps 1--6 there. This supplies
all localized assertions and the restricted integral flatness.
-/
theorem admissible_scalar_realization_exact (ℓ : ℕ) [Fact ℓ.Prime] (T : Scheme.{u}) :
    (∀ (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
      [MonObj Λ] [IsCommMonObj Λ], IsLocalizingAdmissibleCoefficient ℓ Λ →
        ScalarAssertions Λ T) ∧
    (∀ (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
      [Finite A] [DiscreteTopology A],
      (∃ n : ℕ, ∀ a : A, (ℓ ^ n) • a = 0) →
        IsIso (FiniteDiscreteOrdinary.canonicalAbelianMap A T)) ∧
    AdmissibleScalarRealization.CompletedAssertions (ULift.{u} ℤ_[ℓ]) T
      (ℓ : ULift.{u} ℤ_[ℓ]) ∧
    (∀ (E : Type u) [Field E] [Algebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E],
      AdmissibleScalarRealization.IntegralAssertions ℓ E T) := by
  sorry

end AlgebraicGeometry.ProEtale.CurrentAdmissibleScalarRealization
