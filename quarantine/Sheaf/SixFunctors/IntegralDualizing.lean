/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q48
-/
module

public import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
public import Sheaf.Paper.SfIntegralConstructible
public import Sheaf.Paper.SfDerivedComplete
public import Sheaf.Paper.NormalizedDVREffectivity
public import Sheaf.AlgebraicGeometry.CompactifiableOverField
public import Sheaf.AlgebraicGeometry.SfFiniteExceptionalInverseImage
public import Sheaf.Paper.FiniteTorAmplitude
public import Sheaf.AlgebraicGeometry.ProEtaleTorAmplitude
public import Sheaf.Paper.IntrinsicFiniteTorsionConstructibility
public import Sheaf.Paper.CompletedIntegralConstantMapOfUniverses
public import Sheaf.Paper.CompactSupportReductionTower
public import Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitOfUniverses
public import Sheaf.Paper.CoefficientDuality
public import Sheaf.Paper.IntegralRationalQbarCompactSupport
public import Sheaf.Paper.FiniteCoefficientPoint
public import Sheaf.Paper.DirectImagesConstructible
public import WeilConjectures.Mathlib.Topology.KrullDimension

import Sheaf.Paper.NormalizedDVRTower
public import Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses
import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
import Sheaf.Paper.IntegralCompactSupportPrescribedReductions
import Sheaf.Paper.IntegralResidueTor
import Sheaf.AlgebraicGeometry.ProEtaleCohomologicalSupport
import Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction
import Sheaf.Paper.FiniteFieldFiber
import Sheaf.CategoryTheory.Sites.RGammaDerivedLimit
import Sheaf.CategoryTheory.PreDerivedAdjointFunctorsGeneral
import Sheaf.Paper.CoefTowerCoaugmentation
import Sheaf.Paper.PointSectionsDerivedReduction
public import Sheaf.SixFunctors.FiniteDualizing
import Sheaf.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
import Sheaf.Algebra.Homology.RhomGlobalSectionsOfUniverses
import Sheaf.Paper.ConstantCoefficientObjectsConstructible
import Sheaf.NumberTheory.Padics.ExtensionIntegersDvr
import Sheaf.Algebra.Homology.RingedInternalHomSignedCalculus
import Sheaf.Algebra.Homology.RingedInternalHomExactRestriction
import Sheaf.Paper.CoefficientRingedTensorHomModel
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Paper.CoefficientHomRepresentativeEvaluation
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
import WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory
import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategory
import Sheaf.CategoryTheory.SequentialTowerEvaluationFull
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
import Sheaf.Paper.PointFibreEquivalence
import Sheaf.Paper.WeilVerdierPreservationStrata
import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
import Sheaf.Algebra.Homology.RingedInternalHomShiftOfUniverses
import Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients
import Sheaf.Paper.ConstantCoefficientScalarNormalization
import Sheaf.SixFunctors.CoefTowerEvaluationPairing
import Sheaf.SixFunctors.CoefTowerTraceRectification
import Sheaf.SixFunctors.FiniteDualitySiteComparison
import Sheaf.SixFunctors.CoefTowerNaturalCurrying
import Sheaf.SixFunctors.FiniteMappingAdjunction

/- Stage-2 statement delivery metadata: Q117, 2026-10-18. -/
/-!
# The integral dualizing object and its adjunction

Source: blueprint `sec-six-functors/sk-prop-sf-biduality-general`, order 2145
(blueprint: prop-coef-integral-dualizing).

All coefficients are ordinary module sheaves over the completed coefficient sheaf.
The mapping complexes retain the coefficient-module action. Compact support is the
actual strict reduction-tower functor followed by total right derived inverse limit.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open SheafOfModules
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The published sheafification instance with both universes specified.
Source: blueprint order 1455, ordinary coefficient sheaves
(blueprint: prop-coef-integral-dualizing). -/
instance integralDualizingRingSheafify (Y : Scheme.{u}) :
    HasSheafify (ProEt.topology Y) CommRingCat.{u + 1} :=
  integralCoefficientRingSheafify.{u, u} Y

/-- The coefficient ring in the section universe, with only a carrier lift.
Source: blueprint order 2145, D(R) (blueprint: prop-coef-integral-dualizing). -/
abbrev integralDualizingCoefficients := ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E)

/-- The actual constant scalar map to sections of the completion.
Source: blueprint order 2145, global derived mapping complexes
(blueprint: prop-coef-integral-dualizing). -/
def integralDualizingScalar (Y : Scheme.{u}) (U : Y.ProEtᵒᵖ) :
    integralDualizingCoefficients l E →+*
      (completedIntegralCoefficientSheafUnrestricted l E Y).obj.obj U :=
  (((integralConstantToCompletionOfUniverses.{u, u} l E Y).hom.app U).hom).comp
    (((forget₂ CommRingCat.{u + 1} RingCat.{u + 1}).map
      ((toSheafify (D := CommRingCat.{u + 1}) (ProEt.topology Y)
        ((Functor.const Y.ProEtᵒᵖ).obj
          (CommRingCat.of (integralDualizingCoefficients l E)))).app U)).hom)

/-- Ordinary global sections with their actual R action, evaluated at the final object.
Source: blueprint order 2145, global derived mapping complexes
(blueprint: prop-coef-integral-dualizing). -/
def integralDualizingSections (Y : Scheme.{u}) :
    scalarReductionSource l E Y ⥤ ModuleCat.{u + 1} (integralDualizingCoefficients l E) :=
  SheafOfModules.evaluation _ (op (ProEt.mk (𝟙 Y))) ⋙
    ModuleCat.restrictScalars (integralDualizingScalar l E Y (op (ProEt.mk (𝟙 Y))))

/-- Evaluation and scalar restriction are additive, with the existing module structures.
Source: blueprint order 2145 (blueprint: prop-coef-integral-dualizing). -/
instance integralDualizingSections_additive (Y : Scheme.{u}) :
    (integralDualizingSections l E Y).Additive :=
  inferInstanceAs (SheafOfModules.forget _ ⋙
    PresheafOfModules.evaluation _ (op (ProEt.mk (𝟙 Y))) ⋙
    ModuleCat.restrictScalars (integralDualizingScalar l E Y (op (ProEt.mk (𝟙 Y))))).Additive

/-- Derived sections computed on the published K-injective replacements.
Source: blueprint order 2145, global derived mapping complexes
(blueprint: prop-coef-integral-dualizing). -/
def integralDualizingDerivedSections (Y : Scheme.{u}) :
    DerivedCategory (scalarReductionSource l E Y) ⥤
      DerivedCategory.{u + 1} (ModuleCat.{u + 1} (integralDualizingCoefficients l E)) :=
  letI := (grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{u + 1, u, u}
    (ProEt.topology Y) (completedIntegralCommRingSheafUnrestricted l E Y)).1
  (integralDualizingSections l E Y).rightDerivedFunctor

/-- Global derived Hom is RΓ of the recorded internal derived Hom.
Source: blueprint order 2145, definition of RHom_X
(blueprint: prop-coef-integral-dualizing). -/
def integralDualizingGlobalHom (Y : Scheme.{u})
    (M : DerivedCategory (scalarReductionSource l E Y)) :
    (sfIntegralConstructibleCategory l E Y)ᵒᵖ ⥤
      DerivedCategory.{u + 1} (ModuleCat.{u + 1} (integralDualizingCoefficients l E)) :=
  (sfIntegralConstructible l E Y).ι.op ⋙
    (Functor.curry.obj (derivedInternalHomOfUniverses.{u + 1, u, u}
      (ProEt.topology Y) (completedIntegralCommRingSheafUnrestricted l E Y))).flip.obj M ⋙
      integralDualizingDerivedSections l E Y

/-- Total right derived inverse limit on strict completed-coefficient towers.
The chosen functor has the right-derived universal property, so is unique up to the
unique comparison compatible with its derived unit. Its data is not an arbitrary cone.
Source: blueprint order 2145 and Stacks 0940--0941
(blueprint: prop-coef-integral-dualizing). -/
def integralDualizingLimit (Y : Scheme.{u}) :
    DerivedCategory (ℕᵒᵖ ⥤ scalarReductionSource l E Y) ⥤
      DerivedCategory (scalarReductionSource l E Y) :=
  (ringedStrictTowerHomotopyLimitOfUniverses.{u + 2, u + 1, u, u}
    (ProEt.topology Y) (completedIntegralCoefficientSheafUnrestricted l E Y)
    (completedIntegralCoefficient_mul_commUnrestricted l E Y)).choose

variable (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
  (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]

/-- The compactification supplied by Nagata over the given field.
Source: blueprint order 2145, a:X→s (blueprint: prop-coef-integral-dualizing). -/
def integralDualizingCompactification : Compactification (X ↘ Spec (.of D.k)) :=
  letI := hasCompactification_of_finiteType_over_field D.k X (Spec (.of D.k))
    (X ↘ Spec (.of D.k))
  HasCompactification.compactification (X ↘ Spec (.of D.k))

/-- The published coherent compact-support reduction functor, including all transitions
and all derived morphisms. Its evaluation and transition characterizations determine its
coherent tower up to isomorphism. Only normalized scalar structures from that construction
are used to extract the functor.
Source: blueprint order 2145 and Bhatt--Scholze 6.7.6
(blueprint: prop-coef-integral-dualizing). -/
def integralDualizingCompactTower :
    DerivedCategory (scalarReductionSource l E X) ⥤
      DerivedCategory (ℕᵒᵖ ⥤ scalarReductionSource l E (Spec (.of D.k))) := by
  let h := exists_compactSupportReductionTower l E D.k X (Spec (.of D.k))
    (X ↘ Spec (.of D.k)) (finiteFieldDatumPrimeUnit D l hl)
      (integralDualizingCompactification D X)
  letI := h.choose
  letI := h.choose_spec.choose
  exact h.choose_spec.choose_spec.2.2.choose

/-- Integral compact support followed by coefficient-point sections, with its map action.
Source: blueprint order 2145, C=Γ(s,Ra_!K)
(blueprint: prop-coef-integral-dualizing). -/
def integralDualizingCompactSections : sfIntegralConstructibleCategory l E X ⥤
    DerivedCategory.{u + 1} (ModuleCat.{u + 1} (integralDualizingCoefficients l E)) :=
  (sfIntegralConstructible l E X).ι ⋙ integralDualizingCompactTower l E D hl X ⋙
    integralDualizingLimit l E (Spec (.of D.k)) ⋙
      integralDualizingDerivedSections l E (Spec (.of D.k))

/-- A Roos limit presentation of the coherent normalized tower, with the actual counit
reductions and their compatibility with every quotient transition. This is a predicate on
real objects and maps, using the published countable products and effectivity comparisons.
Source: blueprint order 2145, first display and transition paragraph
(blueprint: prop-coef-integral-dualizing). -/
def IntegralDualizingLimitPresentation (T : NormalizedDVRTower l E X D hl)
    (M : DerivedCategory (scalarReductionSource l E X)) : Prop :=
  letI : HasCountableProducts (completedIntegralDerivedCategory l E X D hl) :=
    integralOperationsDerivedCountableProducts l E X
  ∃ (p : M ⟶ ∏ᶜ fun n : ℕ ↦ (normalizedDVRTowerEvaluation l E X D hl n).obj T.tower)
    (δ : (∏ᶜ fun n : ℕ ↦ (normalizedDVRTowerEvaluation l E X D hl n).obj T.tower) ⟶
      M⟦(1 : ℤ)⟧),
    IsDerivedLimitTriangle
      (fun n : ℕ ↦ (normalizedDVRTowerTransition l E X D hl n.le_succ).app T.tower)
        M p δ ∧
    (∀ n : ℕ, IsIso (normalizedDVRCounitComparison l E X D hl T M p n)) ∧
    ∀ (m n : ℕ) (h : n ≤ m),
      normalizedDVRCounitComparison l E X D hl T M p m ≫ T.tau h =
        normalizedDVRReductionTransition l E X D hl h M ≫
          (normalizedDVRRes l E X h).map
            (normalizedDVRCounitComparison l E X D hl T M p n)

/--
Fix the finite-field datum, a prime different from its characteristic, a finite coefficient
extension, and a separated finite-type scheme over the algebraic closure. There is a bounded
constructible derived-complete integral object `ω`, presented by a normalized DVR tower whose
finite terms are the exceptional inverse images of the coefficient units. Every reduction is
identified with the corresponding finite term and has Tor amplitude `[-2d,0]`. For every
constructible integral `K`, the value `C` of integral compact support at the coefficient point
has the asserted adjunction bijection with `ω` and the coefficient unit.

Source: blueprint node `prop-coef-integral-dualizing`, order 2145
(blueprint: prop-coef-integral-dualizing).

Proof plan from the node.  Finite dualizing comparisons give coherent quotient transitions,
and strictification produces a normalized DVR tower.  Derived-limit effectivity identifies
each reduction with the corresponding finite term and gives derived completeness.  Constant
coefficient objects are constructible; Verdier preservation of strata and finite site
comparison give the uniform Tor interval `[-2d,0]`.  For bounded constructible `K`, residue
Tor invariance and compact-support reduction identify its finite compact-support values with
the reductions of the integral value `C`.  Scalar extension--restriction adjunction gives
the finite mapping-complex comparisons, and the finite counit transitions make them a map
of towers.  The ringed-site derived-limit comparison identifies mapping out of the limit
with the limit of the finite mapping complexes.  The tower pairing, coaugmentation and
currying identify that tower with the coefficient-point Hom tower.  Completeness of the
DVR identifies the derived limit of its coefficient quotients with `R`; composing these
natural isomorphisms gives the stated coefficient-point adjunction.  The plan uses
`lem-coef-finite-dualizing`, `def-coef-normalized-dvr-tower`,
`lem-coef-normalized-dvr-effectivity`, `lem-coef-integral-compact-support`,
`lem-coef-integral-residue-tor`, `lem-pod-point-sections-derived-reduction`,
`lem-weil-pbc-ringed-strict-tower-homotopy-limit`,
`lem-coef-finite-mapping-adjunction`, `lem-coef-finite-adjunction-transition`,
`lem-coef-tower-trace-rectification`, `lem-coef-tower-evaluation-pairing`,
`lem-coef-tower-coaugmentation`, and `lem-coef-tower-natural-currying`, together with
the recorded internal-Hom, global-sections, finite-duality, and point-fibre comparisons.
-/
theorem prop_coef_integral_dualizing
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]
    (d : ℕ) (hd : topologicalKrullDim X ≤ (d : WithBot ℕ∞)) :
    ∃ (ω : sfIntegralConstructibleCategory l E X)
      (T : NormalizedDVRTower l E X D hl),
      (∀ n : ℕ, Nonempty (T.M n ≅ integralDualizingFiniteTerm (l := l) (E := E)
        (D := D) (X := X) n)) ∧
      (∃ (e : ∀ n : ℕ, T.M n ≅ integralDualizingFiniteTerm (l := l) (E := E)
        (D := D) (X := X) n),
        (∀ {m n : ℕ} (h : n ≤ m),
          T.tau h ≫ (normalizedDVRRes l E X h).map (e n).hom =
            (e m).hom ≫
              (Adjunction.ofIsRightAdjoint (normalizedDVRRes l E X h)).homEquiv _ _
                (integralDualizingFiniteComparison l E D X hl h))) ∧
      Nonempty (ω.obj ≅ (integralDualizingLimit l E X).obj T.tower) ∧
      IntegralDualizingLimitPresentation l E D hl X T ω.obj ∧
      (∀ n : ℕ, HasProEtaleTorAmplitude X (Padic.coefficientExtensionRing l E (n + 1))
        ((scalarReductionDerivedExtension l E X n).obj ω.obj) (-(2 * (d : ℤ))) 0) ∧
      Nonempty (integralDualizingGlobalHom l E X ω.obj ≅
        (integralDualizingCompactSections l E D hl X).op ⋙
          coefficientDerivedDual (integralDualizingCoefficients l E)) ∧
      ∀ K : sfIntegralConstructibleCategory l E X,
        Nonempty ((K.obj ⟶ ω.obj) ≃
          ((integralDualizingLimit l E (Spec (.of D.k))).obj
            ((integralDualizingCompactTower l E D hl X).obj K.obj) ⟶
              (DerivedCategory.singleFunctor (scalarReductionSource l E (Spec (.of D.k))) 0).obj
                (SheafOfModules.unit
                  (completedIntegralCoefficientSheafUnrestricted l E (Spec (.of D.k)))))) := by
  sorry

end WeilConjectures
