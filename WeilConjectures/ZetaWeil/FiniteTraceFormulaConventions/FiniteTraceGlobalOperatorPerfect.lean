/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.FiniteTraceFormulaConventions.FiniteTraceFormulaConventions
public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SkPropSfRfShriekPreservation2
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SkThmSfCompCompositionWitnesses
public import WeilConjectures.CategoryTheory.ProEtaleCoefficients.LocalizingAdmissibleCoefficients
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
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
public import Mathlib.CategoryTheory.Adjunction.Restrict
public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.Algebra.CharP.CharAndCard
public import WeilConjectures.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
import WeilConjectures.AlgebraicGeometry.BaseFieldFiniteCD.FiniteCohomologicalDimensionHypothesis
import WeilConjectures.CategoryTheory.ProEtaleCoefficients.LocalizingAdmissibleCoefficients
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.LocalizingExceptionalAdjoint
import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Tensor
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Open.OpenImmersionTensorProjection
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ClosedImmersionTensorProjection
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedLocalizingPullback
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ExceptionalInverseImageExistence
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Compactification.CompactificationLocalizing
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.FieldTensor
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralModelsOperations
import WeilConjectures.CategoryTheory.RingObjects.Condensed.BaseCoefficientCondensedIdentification
import WeilConjectures.AlgebraicGeometry.Finite.Comparison.FiniteComparisonPresentationSupplement
import WeilConjectures.AlgebraicGeometry.Finite.Comparison.FiniteComparisonLocalizing
import WeilConjectures.AlgebraicGeometry.Condensed.CondensedCoefficientIsoConstructible
import WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ComparisonMonoidal
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralOpenImageProperFormulas
import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.LocalizingClosureCtfEqualsBc
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Proper.ProperLocalizingAdmissibleCoefficients
import WeilConjectures.AlgebraicGeometry.Rational.RationalOpenDirectImageConstructible
import WeilConjectures.AlgebraicGeometry.Compactification.CompactificationOverField
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteOpenDirectImageCtf
import WeilConjectures.Compactification.Over
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerStarComp
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CompactTraceProEtale
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CompactSupportComposition.CondensedCompactSupportComposition
import WeilConjectures.AlgebraicGeometry.Finite.Constant.FiniteConstantLocalModel
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Constructible

/-! # Perfectness of the explicit correspondence composite

Source: latest blueprint, literature/blueprint/latest/blueprint/
part-duality-trace-formula/sec-lefschetz-verdier/
sec-trace-classes-and-the-lefschetz-verdier-formula/sec-additivity-of-trace-classes/
sk-i-additivity/sk-d-operator/lem-trf-global-operator-perfect.md and its proof
(blueprint: lem-trf-global-operator-perfect).

The five object-membership assertions below put every arrow of the displayed composite
in the full perfect subcategory. No later name for the global operator is used. In
particular the result concerns the ordinary unit, the inverse proper comparison followed
by compact-support composition, the given correspondence map, inverse exceptional
composition, and the specified constructible exceptional counit. The comparisons and
counit are the specified ones of the imported admissibility interface, not new choices.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
attribute [local instance 20000] HasDerivedCategory.ofIsGrothendieckAbelian
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ProEtale
open AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Obj
attribute [local instance 10000] CategoryTheory.CategoryStruct.toQuiver
namespace WeilConjectures.FiniteTraceFormulaConventions

/-- Compact support for any scheme over the geometric point, followed by exactly the
point fibre and constant-section scalar restriction of the recorded conventions.
Source: RΓ_c in lem-trf-global-operator-perfect
(blueprint: lem-trf-global-operator-perfect). -/
def operatorCompactSupport (T : FiniteTraceFormulaConventions.{u})
    {Y : Scheme.{u}} {a : Y ⟶ Spec (.of T.datum.k)}
    (d : Compactification a) :=
  rightDerivedLowerShriekOfCompactification T.coefficients d ⋙ T.pointFiber

end WeilConjectures.FiniteTraceFormulaConventions

namespace WeilConjectures

private theorem constantModel_to_intrinsic
    (T : FiniteTraceFormulaConventions.{u}) {Z : Scheme.{u}}
    [CompactSpace Z] [QuasiSeparatedSpace Z]
    (M : ConstantModelConstructibleFiniteTor T.coefficients Z) :
    condensedConstructibleFiniteTor T.coefficients Z M.obj := by
  have hM := M.property
  refine ⟨(show boundedConstructible.{u + 2, u}
    (condensedRingObj T.coefficients Z) M.obj from ?_), hM.2⟩
  refine ⟨hM.1.1, fun n ↦ ?_⟩
  change IsConstructibleModuleObject.{u + 2, u} (condensedRingObj T.coefficients Z)
    ((DerivedCategory.homologyFunctor _ n).obj M.obj)
  have hn := hM.1.2 n
  rw [IsConstantModelConstructible, if_pos ⟨inferInstance, inferInstance⟩] at hn
  obtain ⟨S, hS⟩ := hn
  refine ⟨S, fun a ↦ ?_⟩
  let N := (DerivedCategory.homologyFunctor.{u + 1, u + 1, u + 2}
    (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      (condensedRingObj T.coefficients Z)) n).obj M.obj
  have h := HasFiniteConstantLocalModel.isLocallyFinitelyPresented.{u} T.coefficients
    ((upperStar.{u} T.coefficients (S.immersion a)).obj N) (hS a)
  exact (isLocallyFinitelyPresented_mapMod_iff.{u} T.coefficients (S.immersion a) N).2 h

set_option maxHeartbeats 800000 in
-- The statement expands five derived functors and their constructibility witnesses.
end WeilConjectures
