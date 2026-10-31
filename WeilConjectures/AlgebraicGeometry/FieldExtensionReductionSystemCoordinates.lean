/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.PurityFiniteSetting
public import WeilConjectures.AlgebraicGeometry.FieldShriekSystemModels
public import WeilConjectures.AlgebraicGeometry.ProjectionReductionPresentation
public import WeilConjectures.AlgebraicGeometry.FieldScalarSystemData
public import WeilConjectures.AlgebraicGeometry.FieldExtensionIntegralCoordinates
public import WeilConjectures.AlgebraicGeometry.FieldScalarNormalizedData
public import WeilConjectures.AlgebraicGeometry.FieldExtensionSystemCoordinates
public import WeilConjectures.AlgebraicGeometry.FieldExtensionIntegralModels
import WeilConjectures.AlgebraicGeometry.SemilinearDerivedCalculusSupplement
import WeilConjectures.AlgebraicGeometry.SemilinearSystemModels
import WeilConjectures.AlgebraicGeometry.CoefficientRingedSequenceSiteSupplement
import WeilConjectures.AlgebraicGeometry.CoefficientRingedTensorHomModelSupplement
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.KFlatSupplement
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
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.AlgebraicGeometry.CoefficientHomRepresentativeEvaluation
import WeilConjectures.Algebra.Homology.DerivedInternalHomOfUniverses
import WeilConjectures.Algebra.Homology.DerivedInternalHom
import WeilConjectures.SixFunctors.Etale.Derived.Hom
import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import Mathlib.CategoryTheory.Yoneda
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.CategoryTheory.Generator.Basic
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMapOfUniverses
import WeilConjectures.Algebra.Homology.HomComplex
import WeilConjectures.Algebra.Homology.HomComplexSectionsQuasiIsoOfUniverses
import WeilConjectures.CategoryTheory.Sites.RGammaDerivedLimitSupplement
import Mathlib.Algebra.Category.Grp.Abelian
import WeilConjectures.Algebra.Homology.HomComplexSectionsDerivedNaturalityOfUniverses
import WeilConjectures.Algebra.Homology.RhomIntoKInjectiveLocal
import WeilConjectures.Algebra.Homology.KInjectiveRestrictLocalizedOfUniverses
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import WeilConjectures.Algebra.Homology.LocalizedRestrictionAdjunctionOfUniverses
import WeilConjectures.Algebra.Homology.LocalizedRestrictionExtensionExistsOfUniverses
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import WeilConjectures.Algebra.Homology.HomComplexSectionsHomotopyNaturalityOfUniverses
import WeilConjectures.Algebra.Homology.HomComplexProjections
import WeilConjectures.Algebra.Homology.HomComplexSectionsCanonicalComparisonOfUniverses
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexShift
import WeilConjectures.Algebra.Homology.HomComplexSectionsCochainsOfUniverses
import WeilConjectures.Algebra.Homology.HomComplexSectionsCochainsCommOfUniverses
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
import Mathlib.Algebra.Category.Grp.EpiMono
import WeilConjectures.Algebra.Homology.LocalizedModuleRestrictionQuasiIsoOfUniverses
import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
import WeilConjectures.Algebra.Homology.QuasiIsoOfSectionsOfUniverses
import Mathlib.CategoryTheory.Sites.Abelian
import Mathlib.Algebra.Homology.Functor
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
import WeilConjectures.Algebra.Homology.HomComplexComponents
import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMap
import WeilConjectures.Algebra.Homology.HomTensorDegreewiseEquation
import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsCochainModel
import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.CategoryTheory.Limits.Final
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.CategoryTheory.Sites.CoverPreserving
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedTotalTensor
import WeilConjectures.AlgebraicGeometry.FiniteSupportCoordinates
import WeilConjectures.CategoryTheory.SystemRingedSequenceSite
import WeilConjectures.CategoryTheory.SequenceModulePullbackEvaluation

/-! # Section-preserving system coordinates from integral coordinates

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/
sk-lem-sp-field-extension/sk-lem-sp-field-extension-towers.proof.md,
paragraph (1), middle sentence
(blueprint: lem-route-field-extension-reduction-system-coordinates).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genInjectivity false
set_option genCtorIdx false

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures

namespace AlgebraicGeometry.ProEtale.FieldExtensionTowers

/-- Every integral scalar coordinate datum admits section-preserving whole-system
coordinates, including the ordinary, derived, and tower-scalar comparisons.

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/
sk-lem-sp-field-extension/sk-lem-sp-field-extension-towers.proof.md,
paragraph (1), middle sentence; the construction is detailed in the docstring of
`field_extension_reduction_descent`
(blueprint: lem-route-field-extension-reduction-system-coordinates).

Proof.
1. Write `R_E` and `R_F` for the section-preserving realizations in
   `FieldShriekSystem.Models` and `SpTowerCalculus.Coordinates`, using the strict-system
   sequence-site equivalence of `lem-pur-system-ringed-sequence-site`. The coefficient
   maps in `A.data` and `D` are the same quotient inclusions by their `quotient_mk` and
   `tower_app` equations (`def-sp-field-scalar-system-data`). Let `S` be `D`'s ordinary
   scalar model, left adjoint to restriction (`def-coef-semilinear-system-models`).
   For each tower `M`, define a map from `R_E M` to the restriction of
   `R_F (A.data.extension.ordinary.obj M)` by sending a section `x` at `(n,U)` to
   the inverse level identification applied to `1` tensor `x`, read through the
   ordinary evaluation coordinates. The transition equation in `ExactExtension`,
   with scalar `1`, proves horizontal compatibility because each quotient sends
   `1` to `1`. Linearity and naturality therefore give a sequence-site module map.
   Its adjoint transpose `theta` sends `s` tensor `x` to the inverse level
   identification applied to `s` tensor `x`. For every level, the inverse mate of
   the identity-on-sections restriction/evaluation comparison is an isomorphism
   by `lem-sf-sequence-module-pullback-evaluation`, with identity site functor.
   The ordinary unit normalization and multiplication counit show that this mate
   sends `s` tensor `x` to itself. Composing it with the evaluation of `theta`
   agrees with the inverse level identification on local pure tensors, hence
   everywhere by tensor generation (`def-coef-semilinear-derived-calculus`).
   Each evaluation of `theta` is therefore an isomorphism. The vertical slices
   cover every sequence-site object `(n,U)`, so `theta` is an isomorphism.
   Its inverse is `systemOrdinary`, with exactly `systemOrdinary_sections`.
2. The universal localization counit of `A.data.extension.derived` is invertible
   on every complex (`def-sp-field-scalar-system-data`). The derived scalar model
   of `D` has its universal counit and K-flat computation
   (`def-sfb-derived-change-of-rings-cochain-model`). The exact realization
   equivalences have their induced derived equivalences and localization factor
   isomorphisms (`def-sp-coefficient-tower-shriek-interfaces`). Postcomposition by
   the derived `R_F` preserves the first universal property. Precomposition by
   the equivalence on complexes induced by `R_E`, which preserves and reflects
   quasi-isomorphisms, transports the second universal property. Thus both sides
   of `systemDerived` are total left derived functors of the ordinary functors
   identified in step 1. The universal property of `def-sfb-left-derived-functor`
   gives a unique transformation whose counit equation is `systemDerived_rep`
   on every complex. Applying the same construction to the inverse of step 1
   gives an inverse: uniqueness makes both composites identities.
3. Define `system` by the unit of the derived `R_F` equivalence followed by its
   inverse functor applied to `systemDerived`. Its target is exactly `towerScalar`
   (`def-sp-field-extension-integral-models`). The triangle identity supplies
   the inverse and its displayed component formula is `system_normalized`.
   All three comparisons are natural maps of whole sequence-site or strict
   systems, so they commute with every quotient transition. For `E = F` the
   construction specializes to the unit identification.
-/
theorem field_extension_reduction_system_coordinates
    (P : PurityFiniteSetting.{u}) (D : FieldShriekSystem.Models P)
    (E F : FieldShriekSystem.Index P) (h : E ≤ F) (T : Scheme.{u})
    (RA : SpReductionTower P.coefficients.l E.val T ((D.coordinates E).abelian T))
    (RB : SpReductionTower P.coefficients.l F.val T ((D.coordinates F).abelian T))
    (A : IntegralCoordinates P D E F h T RA RB) :
    Nonempty (SystemCoordinates P D E F h T RA RB A) := by
  sorry

end AlgebraicGeometry.ProEtale.FieldExtensionTowers
