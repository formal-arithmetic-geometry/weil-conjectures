/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q26
-/
module

public import Sheaf.Paper.CondensedConstantConstructibility
public import Sheaf.Paper.CondensedModuleDerivedPushpull
public import Sheaf.Paper.LocalizingAdmissibleCoefficients
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Sheaf.Paper.KFlatScalarComparisonNormalization
public import Sheaf.AlgebraicGeometry.InternalModuleOperationsTransport
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import Sheaf.Paper.CartesianCoefficientsFiniteFree
public import Sheaf.Paper.PadicIntegersInvertEll
import Sheaf.Paper.SectionDerivedPushpullNormalization
import Sheaf.CategoryTheory.FiniteFreeScalarCoordinates
import Sheaf.CategoryTheory.InternalSectionScalarAdjunction
import Sheaf.NumberTheory.Padics.LocalFieldIntegralBasis
import Sheaf.Paper.LocalizedDirectImageComparison
import Sheaf.CategoryTheory.PastedMatesCounitNormalization
import Sheaf.AlgebraicGeometry.ProEtaleRingSheafChangeAdjunction
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
import WeilConjectures.AlgebraicGeometry.ProperBasic

/-! # Proper integral-to-rational coefficient comparison

Source: blueprint main-20261015, det-sf-comp-coherence-refinement (2), finite-field
coefficient calculation; Hemo--Richarz--Scholbach Lemmas 5.3(1), 5.6
(blueprint: lem-sfb-qcqs-proper-integral-rational-scalar-comparison).

The comparison is defined by the geometric adjunction and its specified counit.
The pullback/scalar isomorphism is the canonical conjugate, with the balanced-tensor
normalization of the imported K-flat and section-module transport statements.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- The actual inclusion O_F → E on condensed rings, factored through F. All topologies
are induced from the fixed norm-topological algebraic closure.
Source: blueprint det-sf-comp-coherence-refinement (2), finite coefficient case
(blueprint: lem-sfb-qcqs-proper-integral-rational-scalar-comparison). -/
abbrev integralRationalCoefficientMap (ℓ : ℕ) [Fact ℓ.Prime]
    {F E : PadicAlgCl.FiniteIntermediateField ℓ} (i : F ≤ E) :=
  padicIntegersRingObjToContinuousMapRingObj.{u} ℓ F ≫
    Profinite.padicSubfieldRingObjMap ℓ i

/-- The existing total derived scalar extension along O_F → E on the indicated scheme.
Source: blueprint det-sf-comp-coherence-refinement (2), definition of T_W
(blueprint: lem-sfb-qcqs-proper-integral-rational-scalar-comparison). -/
abbrev integralRationalScalarExtension (ℓ : ℕ) [Fact ℓ.Prime]
    {F E : PadicAlgCl.FiniteIntermediateField ℓ} (i : F ≤ E) (X : Scheme.{u}) :=
  (Mod.extendScalars
    (coefficientMap (integralRationalCoefficientMap ℓ i) X)).leftDerivedFunctor

/-- The specified scalar/pullback comparison T_U h_A^* ≅ h_E^* T_V. The existing
conjugate construction uses the canonical restriction/direct-image identification.
Its inverse is the balanced comparison of kflat_scalar_comparison_normalization,
transported by internal_module_operations_transport and the section adjunction
normalizations. Exactness needed by this published interface is obtained from
localization O_F → F and finite free extension F → E, without an extra hypothesis.
Source: blueprint det-sf-comp-coherence-refinement (2); Stacks 03EL, 07A6
(blueprint: lem-sfb-qcqs-proper-integral-rational-scalar-comparison). -/
def integralRationalScalarPullIso (ℓ : ℕ) [Fact ℓ.Prime]
    {F E : PadicAlgCl.FiniteIntermediateField ℓ} (i : F ≤ E)
    {U V : Scheme.{u}} (h : U ⟶ V) :
    moduleObjectDerivedPullback (Profinite.padicIntegersRingObj ℓ F.1) h ⋙
        (integralRationalScalarExtension ℓ i U) ≅
      (integralRationalScalarExtension ℓ i V) ⋙
        moduleObjectDerivedPullback (Profinite.continuousMapRingObj E.1) h :=
  letI : ∀ X : Scheme.{u}, PreservesFiniteLimits
      (Mod.extendScalars (coefficientMap (integralRationalCoefficientMap ℓ i) X)) :=
    fun X ↦
      letI : PreservesFiniteLimits (Mod.extendScalars (padicIntegersToPadicSubfield X ℓ F)) :=
        (padicIntegers_invertEll X ℓ F).choose_spec.2.choose_spec.2.2.choose_spec.2.2.2
      letI : PreservesFiniteLimits (Mod.extendScalars (padicSubfieldRingObjMap X ℓ i)) :=
        (cartesianCoefficients_finiteFree ℓ i).2.2 X |>.2
      letI := comp_preservesFiniteLimits
        (Mod.extendScalars (padicIntegersToPadicSubfield X ℓ F))
        (Mod.extendScalars (padicSubfieldRingObjMap X ℓ i))
      preservesFiniteLimits_of_natIso
        ((Mod.extendScalarsComp (padicIntegersToPadicSubfield X ℓ F)
          (padicSubfieldRingObjMap X ℓ i)).symm ≪≫
            Mod.extendScalarsIsoOfEq (coefficientMap_comp
              (padicIntegersRingObjToContinuousMapRingObj ℓ F)
              (Profinite.padicSubfieldRingObjMap ℓ i) X).symm)
  derivedPullIso (integralRationalCoefficientMap ℓ i) h

/-- The coefficient projection arrow, defined as the transpose of the inverse
scalar/pullback comparison followed by scalar extension of the A-counit.
Source: blueprint det-sf-comp-coherence-refinement (2), displayed definition of rho
(blueprint: lem-sfb-qcqs-proper-integral-rational-scalar-comparison). -/
def properIntegralRationalScalarComparison (ℓ : ℕ) [Fact ℓ.Prime]
    {F E : PadicAlgCl.FiniteIntermediateField ℓ} (i : F ≤ E)
    {U V : Scheme.{u}} (h : U ⟶ V)
    (J : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ F.1) U))) :
    (integralRationalScalarExtension ℓ i V).obj
          ((moduleObjectDerivedPushforward (Profinite.padicIntegersRingObj ℓ F.1) h).obj J) ⟶
      (moduleObjectDerivedPushforward (Profinite.continuousMapRingObj E.1) h).obj
        ((integralRationalScalarExtension ℓ i U).obj J) :=
  (derivedUpperStarLowerStarAdjunction (Profinite.continuousMapRingObj E.1) h).homEquiv _ _
    ((integralRationalScalarPullIso ℓ i h).inv.app
        ((moduleObjectDerivedPushforward (Profinite.padicIntegersRingObj ℓ F.1) h).obj J) ≫
      (integralRationalScalarExtension ℓ i U).map
          ((derivedUpperStarLowerStarAdjunction
            (Profinite.padicIntegersRingObj ℓ F.1) h).counit.app J))

/-- For a proper morphism between qcqs schemes, the specified coefficient projection
is invertible on bounded constructible complexes of finite Tor amplitude. The
coefficient fields are finite subextensions, with no characteristic, dimension,
Noetherian or invertibility-of-ell assumption on the schemes.
Source: blueprint det-sf-comp-coherence-refinement (2), finite coefficient case;
Hemo--Richarz--Scholbach Lemmas 5.3(1), 5.6
(blueprint: lem-sfb-qcqs-proper-integral-rational-scalar-comparison).

Proof:
1. SectionDerivedPushpullNormalization and internal_section_scalar_adjunction
identify the ordinary unbounded derived categories, scalar extensions and specified
adjunctions, including counits. proper_basic gives that h is qcqs. The definition
ConstantModelConstructibleFiniteTor supplies boundedness, hence boundedness below.
2. Factor O_F → E through F. Apply localizedDirectImageComparison_isIso to J for
O_F → F: the required hypotheses are exactly qcqs and boundedness below. This
comparison is the counit mate, and gives K = F_U tensor^L_{A_U} J.
3. exists_integral_basis and cartesianCoefficients_finiteFree give F_W^d ≅ E_W,
using the same basis after inverse image. sheaf_finiteFreeScalarCoordinates gives
E_W tensor_{F_W} M ≅ M^d, with coefficient-coordinate and sum-of-basis-tensors
formulas. Apply these termwise: finite sums preserve quasi-isomorphisms, so they
compute the derived extension for every unbounded complex K.
4. proEtaleRingSheafChangeAdjunction preserves adjoint transposes after scalar
restriction. In those coordinates the F → E counit mate is the canonical map
(Rh_* K)^d → Rh_*(K^d). Additivity makes it invertible by the finite biproduct
identities. Scalar restriction reflects isomorphisms, giving invertibility before
restriction as well.
5. ringedTopoiCanonicalDerivedTensorPullback identifies iterated extension with
E tensor^L_{A} -, on K-flat representatives by e tensor f tensor p ↦ ef tensor p,
with inverse e tensor p ↦ e tensor 1 tensor p. Paste the two invertible mates.
pasted_mates_counit_normalization identifies its transpose with the composite
pullback/scalar comparison followed by T_U of the A-counit. The pure-tensor unit
normalization of kflat_scalar_comparison_normalization identifies that composite
with integralRationalScalarPullIso. Uniqueness of adjuncts identifies the pasted
isomorphism with precisely properIntegralRationalScalarComparison. -/
theorem properIntegralRationalScalarComparison_isIso (ℓ : ℕ) [Fact ℓ.Prime]
    {F E : PadicAlgCl.FiniteIntermediateField ℓ} (i : F ≤ E)
    {U V : Scheme.{u}} (h : U ⟶ V) [IsProper h]
    [CompactSpace U] [QuasiSeparatedSpace U] [CompactSpace V] [QuasiSeparatedSpace V]
    (J : ConstantModelConstructibleFiniteTor (Profinite.padicIntegersRingObj ℓ F.1) U) :
    IsIso (properIntegralRationalScalarComparison ℓ i h J.obj) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
