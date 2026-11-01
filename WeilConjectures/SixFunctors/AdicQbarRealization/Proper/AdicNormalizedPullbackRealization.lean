/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.AdicQbarRealization.Proper.NativeProperTensorComparison
import WeilConjectures.SixFunctors.AdicQbarRealization.Proper.NativePullbackOperations
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import WeilConjectures.SixFunctors.AdicQbarRealization.Proper.NativePullbackIntegralComparison
import WeilConjectures.SixFunctors.AdicQbarRealization.Proper.NativePullbackScalarCoherence
import WeilConjectures.SixFunctors.AdicQbarRealization.Proper.NativePullbackTensorComparison
import WeilConjectures.SixFunctors.AdicQbarRealization.Proper.NativePullbackFiniteTensorCoherence
import WeilConjectures.SixFunctors.AdicQbarRealization.Proper.NativePullbackUnitDescent
import WeilConjectures.SmoothPurity.Pullback.PullbackTensorCommonStageUnitCoherence

/-! # Normalized inverse-image realization for native continuous coefficients

Source: Bhatt--Scholze, Proposition 6.8.14 and Remark 6.8.15;
agent assembly of the normalized common-stage inverse-image comparison
(blueprint: lem-sf-adic-normalized-pullback-realization).

All functors below take values in ordinary module derived categories. The comparison
is fixed before rationalization by balanced tensor multiplication. The realization
family is an input; its existence theorem is not a dependency of these definitions.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option cleanup.letToHave false
set_option linter.all false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
attribute [local irreducible] HasDerivedCategory.standard
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme
namespace WeilConjectures.AdicQbarRealization.Proper
open AdicQbarRealization
attribute [local irreducible] ContinuousRational.modulePull ContinuousRational.derivedPull
  ordinaryIntegralModulePull ordinaryIntegralDerivedPull
variable (l : ℕ) [Fact l.Prime] {X Y : Scheme.{u}} (p : X ⟶ Y)
  (R : LocallyFiniteAdicRealization.Realization l X)
  (S : LocallyFiniteAdicRealization.Realization l Y)

variable [∀ x : X, Invertible (l : X.residueField x)]
  [∀ y : Y, Invertible (l : Y.residueField y)]
attribute [local irreducible] ordinary commonStageDerivedPullback
  commonStageDerivedTensor

/-- The normalized inverse-image data, without any direct-image assertion.
Source: BS Proposition 6.8.14 and Remark 6.8.15; Steps 1--4 of the proper
adjunction comparison (blueprint: lem-sf-adic-normalized-pullback-realization). -/
structure PullbackComparison (A : At l X R) (C : At l Y S) where
  operations : Operations l p R S
  integral : ∀ E, IntegralComparison l p R S operations E
  tensor : TensorComparison l p R S operations A C
  a : commonStageDerivedPullback l (PadicAlgCl l) p ⋙ ordinary l X R ≅
    ordinary l Y S ⋙ ContinuousRational.derivedPull p operations.coefficient
  integral_normalization : ∀ E, IntegralAgreement l p R S operations E (integral E) a
  sourceUnit : canonicalCommonStagePullbackTensor_unit l (PadicAlgCl l) p
  tensor_compatibility : ∀ M N,
    (ContinuousRational.derivedPull p operations.coefficient).map
        (C.tensor.hom.app (M, N)) ≫
      a.inv.app ((commonStageDerivedTensor l (PadicAlgCl l) Y).obj (M, N)) ≫
      (ordinary l X R).map (canonicalCommonStagePullbackTensor l (PadicAlgCl l) p M N).hom =
    tensor.tensor.hom.app ((ordinary l Y S).obj M, (ordinary l Y S).obj N) ≫
      A.closed.tensor.map (Prod.mkHom (a.inv.app M) (a.inv.app N)) ≫
      A.tensor.hom.app ((commonStageDerivedPullback l (PadicAlgCl l) p).obj M,
        (commonStageDerivedPullback l (PadicAlgCl l) p).obj N)
  unit_compatibility :
    (ContinuousRational.derivedPull p operations.coefficient).map C.unit.hom ≫
      a.inv.app (pullbackTensorCommonUnit l (PadicAlgCl l) Y) ≫
      (ordinary l X R).map sourceUnit.exists.choose.hom = tensor.unit.hom ≫ A.unit.hom

/-- The balanced finite-integral pullback comparisons descend to the raw common-stage
category, with the specified tensor and coefficient-unit normalizations.
Source: Bhatt--Scholze, Proposition 6.8.14 and Remark 6.8.15, pp. 61--62;
agent assembly of Steps 1--4 of lem-sf-adic-proper-adjunction-realization
(blueprint: lem-sf-adic-normalized-pullback-realization).

Proof: identify the native coefficient sheaf with the locally finite condensed
coefficient sheaf using locallyFiniteCoefficientRing_realization. Its scheme-map
square identifies the coefficient map with precomposition by adjunction. The
ordinary module pullback adjunction, its insertion-of-one unit and the derived
computation counits give Operations. Balanced tensor associativity gives each
IntegralComparison, including its section and cochain equations. Noetherianity,
finite dimension and invertibility of l follow from finite type over D.k and hl.
ordinaryCompletedIntegralPullback makes the actual quotient-tower completion unit
invertible on constructible integral inputs. Invert it before applying balanced
scalar extension. rationalRealizationPullbackComparison identifies the result with
the completed finite-stage pullback. rationalRealizationScalarCoherence identifies
these maps after extension to every common finite field, so the fraction formula
in Realization descends them to a natural isomorphism a. This also proves the
IntegralAgreement equation, retaining its literal localization transports.
For tensors, retain the whole quotient tower of constructibleTensorCompletion:
the unshifted coordinate of the comparison is the quotient map, and the shifted
coordinate is zero. CochainPullback.cochainPullbackTensorCoherence commutes with
all transitions. Apply derived limit and completedPrimitiveCounitComparison,
then invert the completion units. Thus the ordinary comparison agrees with the
completed one. Ringed derived monoidal composition and the tensor structure of
the fixed Family give tensor_compatibility. On generators both routes send
b tensor (x tensor y) to (b tensor x) tensor (1 tensor y); coefficients have
degree zero, so the signed symmetry agrees. At the coefficient unit the same
maps send one to one and give sourceUnit and unit_compatibility. The Family's
finite normalizations ensure these equations use its given tensor data. Empty
schemes, zero complexes and identity coefficient extensions use the same maps. -/
theorem adic_normalized_pullback_realization (D : FiniteFieldDatum.{u})
    (hl : l ≠ D.p) (F : Family l D) (Z T : GeometricSpace D)
    (p : Z.base ⟶ T.base) :
    letI := (F.data Z).units
    letI := (F.data T).units
    Nonempty (PullbackComparison l p.left (F.data Z).realization
      (F.data T).realization (F.data Z).tensor (F.data T).tensor) := by
  letI := (F.data Z).units
  letI := (F.data T).units
  let := Z.finiteType
  let := Z.quasiCompact
  let := T.finiteType
  let := T.quasiCompact
  let : CompactSpace Z.base.left := QuasiCompact.compactSpace_of_compactSpace Z.base.hom
  let : CompactSpace T.base.left := QuasiCompact.compactSpace_of_compactSpace T.base.hom
  let : IsLocallyNoetherian Z.base.left :=
    LocallyOfFiniteType.isLocallyNoetherian Z.base.hom
  let : IsLocallyNoetherian T.base.left :=
    LocallyOfFiniteType.isLocallyNoetherian T.base.hom
  have : IsNoetherian Z.base.left := ⟨⟩
  have : IsNoetherian T.base.left := ⟨⟩
  let R := (F.data Z).realization
  let S := (F.data T).realization
  obtain ⟨O⟩ := nativePullbackOperations l p.left R S
  let I : ∀ E, IntegralComparison l p.left R S O E :=
    fun E ↦ Classical.choice (nativePullbackIntegralComparison l D Z T p R S O E)
  have hscalar := nativePullbackScalarCoherence l p.left R S O I
  obtain ⟨a, ha⟩ := nativePullbackCommonStageDescent l p.left R S O I hscalar
  obtain ⟨V⟩ := nativePullbackTensorComparison l p.left R S O
    (F.data Z).tensor (F.data T).tensor
  have hu := pullbackTensorCommonStageUnitCoherence l (PadicAlgCl l) p.left
  have hfinite : ∀ E, NativePullbackFiniteTensorSquare l p.left R S O
      (F.data Z).tensor (F.data T).tensor E ((F.data Z).finite E)
      ((F.data T).finite E) (I E) V := by
    intro E
    exact nativePullbackFiniteTensorCoherence l p.left R S O
      (F.data Z).tensor (F.data T).tensor E ((F.data Z).finite E)
      ((F.data T).finite E) (I E) V
  have ht : ∀ M N, NativePullbackTensorEquation l p.left R S O
      (F.data Z).tensor (F.data T).tensor V a M N := by
    apply nativePullbackTensorDescent l p.left R S O
      (F.data Z).tensor (F.data T).tensor V a
    intro E K L
    exact nativePullbackFiniteTensorDescent l p.left R S O
      (F.data Z).tensor (F.data T).tensor E ((F.data Z).finite E)
      ((F.data T).finite E) (I E) V a (ha E) (hfinite E) K L
  exact ⟨{
    operations := O
    integral := I
    tensor := V
    a := a
    integral_normalization := ha
    sourceUnit := hu
    tensor_compatibility := ht
    unit_compatibility := nativePullbackUnitDescent l p.left V a hu (ht _ _) }⟩

end WeilConjectures.AdicQbarRealization.Proper
