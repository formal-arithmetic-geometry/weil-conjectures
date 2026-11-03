/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ProfiniteCondensedRing
public import WeilConjectures.AlgebraicGeometry.Cohomological.CohomologicalDimension
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.ProfiniteFiniteConstantLocalModel
public import WeilConjectures.CategoryTheory.Right.RightDerivedFunctorOfQuasiIsoResolutions
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Hom
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ExceptionalInverseImageExistence
public import WeilConjectures.AlgebraicGeometry.BaseFieldFiniteCD.FiniteCohomologicalDimensionHypothesis
public import WeilConjectures.AlgebraicGeometry.LocallyConstantPerfectComplex
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.LocalizingExceptionalAdjoint
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.AdmissibleBoundedConstructibleTriangulated
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CtfLocallyClosedPerfectGeneration
public import WeilConjectures.CategoryTheory.ProEtaleCoefficients.LocalizingAdmissibleCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.IntTensorProjection
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedLocalizingPullback
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Compactification.CompactificationLocalizing
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.AdmissibleTensorConstructibility
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedCoefficientIsoConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralOpenImageProperFormulas
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.LocalizingClosureCtfEqualsBc
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Proper.ProperLocalizingAdmissibleCoefficients
public import WeilConjectures.AlgebraicGeometry.Rational.RationalOpenDirectImageConstructible
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.BaseCoefficientCondensedIdentification
public import WeilConjectures.AlgebraicGeometry.Compactification.CompactificationOverField
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteOpenDirectImageCtf
public import WeilConjectures.Compactification.Over
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerStarComp
public import WeilConjectures.CategoryTheory.DerivedCategory.SixFunctors.NativeInternalHomExact
public import Mathlib.CategoryTheory.Triangulated.Opposite.Subcategory
public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.AlgebraicGeometry.IntegralModelsEmbedded.IntegralModelsEmbedded
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Braided
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Braided
public import Mathlib.CategoryTheory.Triangulated.Opposite.Pretriangulated
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SmoothPurity.AdmissibleCondensedCoefficients
public import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvr
public import WeilConjectures.AlgebraicGeometry.SixFunctors.DualityPairing
public import WeilConjectures.Compactification.Dense
public import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedSiteComparison
public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteDiscreteOrdinaryEquivalence
public import WeilConjectures.SixFunctors.Etale.Derived.GeometricBidualityInduction
public import WeilConjectures.CategoryTheory.Monoidal.Closed.EvaluationBidualComparisonTransport
public import WeilConjectures.AlgebraicGeometry.Base.BaseFieldCohomologicalDimension
public import WeilConjectures.AlgebraicGeometry.Integral.IntegralModels
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SfNativeDerivedMonoidal
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SfActualIntegralReduction
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedFiniteTorConstructible
public import WeilConjectures.AlgebraicGeometry.Completed.CompletedCondensedCoefficients
public import Mathlib.Topology.KrullDimension

/-! # Actual integral reductions of the dualizing object and its duals
Source: current blueprint thm-sf-biduality-class.proof.md, integral scalar-comparison paragraph.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096
set_option maxRecDepth 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Scheme Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor MonoidalCategory
namespace AlgebraicGeometry.ProEtale.CondensedRing

-- Use the existing derived structure with the coefficient proof already supplied.
attribute [local instance 50000] sfNativeDerivedMonoidal sfNativeCoefficientComm
  sfNativeTensorFour sfNativeGoodTensor12 sfNativeGoodTensor23
  sfNativeTensorLeftInt sfNativeTensorRightInt sfNativeFlatResolution sfNativeScalarsKFlat
  sfNativeModuleClosed sfNativeModuleBraided

-- Keep the derived localization folded while elaborating the scalar functors.
attribute [local irreducible] _root_.DerivedCategory upperStarFromPoint
  derivedHom condensedVerdierAmbientSupport condensedVerdierBiduality
  condensedConstructibleFiniteTor Mod.extendScalars Functor.leftDerivedFunctor
  monoidal_upperStarFromPoint monoidal_pointUpperStar oplaxMonoidal_pointUpperStar
  instCategoryDerivedCategory DerivedCategory.instPretriangulated DerivedCategory.Qh

set_option synthInstance.maxHeartbeats 200000 in
-- The statement includes scalar-derived functors at both coefficient stages.
/-- The two scalar-six comparison isomorphisms for the specified integral quotient
maps and the actual constructible exceptional adjunction. No Tor estimate is assumed
or concluded here.

Source: thm-sf-biduality-class.proof.md, integral paragraph, and sk-prop-scalar-six,
exceptional inverse image and internal Hom comparisons
(blueprint: lem-sf-integral-dual-reduction-comparison).

Proof: the continuous quotient modulo pi^(m+1) is a listed coefficient map; change
its source by the given integral coefficient isomorphism. The scalar-six theorem
preserves the constructible finite-Tor domains and gives the compact-support
comparison through the specified compactification. Take its mate under the two
constructible exceptional adjunctions. It is invertible by the independently
proved exceptional scalar comparison. Scalar extension of the unit is the unit;
applying the mate to it gives the displayed comparison for omega. The internal
Hom comparison is the transpose of scalar extension of evaluation through the
canonical tensorator. It is invertible on the constructible finite-Tor arguments.
Compose with internal Hom applied to the omega comparison. These are the actual
comparison maps, so their evaluations and counits have the scalar-six normalization;
there is no use of biduality to construct either comparison. Uniqueness of right
adjoints transports from the canonical chosen adjoints to the adjunctions in the
statement, and proof irrelevance identifies membership certificates. -/
theorem sfIntegralDualReductionComparison
    (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    (hk : Finite k ∨ IsAlgClosed k)
    (E : PadicAlgCl.FiniteIntermediateField ℓ) (π : PadicAlgCl.integers ℓ E.1)
    (hπ : Ideal.span {π} = IsLocalRing.maximalIdeal (PadicAlgCl.integers ℓ E.1))
    (n : ℕ+)
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (e : Mon.mk Λ ≅ Mon.mk (Profinite.padicIntegersRingObj ℓ E.1))
    (T : Over (Spec (.of k))) [LocallyOfFiniteType T.hom]
    [QuasiCompact T.hom] [IsSeparated T.hom]
    (h : ∀ K : moduleDerived Λ T.left, condensedConstructibleFiniteTor Λ T.left K →
      condensedConstructibleFiniteTor Λ (Spec (.of k))
        ((condensedVerdierAmbientSupport Λ T).obj K))
    (G : CondensedConstructibleFiniteTor Λ (Spec (.of k)) ⥤
      CondensedConstructibleFiniteTor Λ T.left)
    (adj : (condensedConstructibleFiniteTor Λ (Spec (.of k))).lift
      ((condensedConstructibleFiniteTor Λ T.left).ι ⋙ condensedVerdierAmbientSupport Λ T)
      (fun K ↦ h K.obj K.property) ⊣ G)
    (N : CondensedConstructibleFiniteTor Λ (Spec (.of k)))
    (hN : N.obj = 𝟙_ (moduleDerived Λ (Spec (.of k)))) :
    let R (m : ℕ) : moduleDerived Λ T.left ⥤
        moduleDerived (Profinite.continuousMapRingObj (completedResidue ℓ E π m)) T.left :=
      sfActualIntegralReduction ℓ E π Λ e T.left m
    ∀ m : ℕ,
      ∃ (hm : ∀ K : moduleDerived
            (Profinite.continuousMapRingObj (completedResidue ℓ E π m)) T.left,
          condensedConstructibleFiniteTor _ T.left K →
          condensedConstructibleFiniteTor _ (Spec (.of k))
            ((condensedVerdierAmbientSupport _ T).obj K))
        (Gm : CondensedConstructibleFiniteTor
            (Profinite.continuousMapRingObj (completedResidue ℓ E π m))
            (Spec (.of k)) ⥤ CondensedConstructibleFiniteTor _ T.left)
        (adjm : (condensedConstructibleFiniteTor _ (Spec (.of k))).lift
          ((condensedConstructibleFiniteTor _ T.left).ι ⋙ condensedVerdierAmbientSupport _ T)
          (fun K ↦ hm K.obj K.property) ⊣ Gm)
        (Nm : CondensedConstructibleFiniteTor
            (Profinite.continuousMapRingObj (completedResidue ℓ E π m)) (Spec (.of k))),
        Nm.obj = 𝟙_ (moduleDerived _ (Spec (.of k))) ∧
        Nonempty ((R m).obj (G.obj N).obj ≅ (Gm.obj Nm).obj) ∧
        ∀ K : CondensedConstructibleFiniteTor Λ T.left,
          Nonempty ((R m).obj
              (((derivedHom Λ T.left).flip.obj (G.obj N).obj).obj (op K.obj)) ≅
            ((derivedHom _ T.left).flip.obj (Gm.obj Nm).obj).obj
              (op ((R m).obj K.obj))) := by sorry

end AlgebraicGeometry.ProEtale.CondensedRing

-- The generic premise-index export scans the large coefficient instances repeatedly.
-- Keep this module's index bounded without exporting a deny-list entry.
run_cmd do
  Lean.modifyEnv fun env =>
    Lean.LibrarySuggestions.nameDenyListExt.modifyState env
      ("sfIntegralDualReductionComparison" :: ·)
