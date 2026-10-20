/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q04
-/
module

public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
public import Mathlib.AlgebraicGeometry.Fiber
public import WeilConjectures.AlgebraicGeometry.TensorPullback
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import WeilConjectures.Topology.InverseImageModule
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Topology.Sheaves.Functors
public import WeilConjectures.AlgebraicGeometry.Picard.Defs
public import Sheaf.AlgebraicGeometry.EtaleClosedAmbientAdjoint
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
public import Sheaf.AlgebraicGeometry.EtaleTorAmplitude
public import WeilConjectures.SixFunctors.Etale.Derived.Hom
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Comparison
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.Topology.KrullDimension
public import Mathlib.CategoryTheory.Shift.Adjunction
public import WeilConjectures.SixFunctors.Etale.Derived.Shift
public import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.Localization.FractionRing
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageAlgebraicStructures
import Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses

import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Sheaf.AlgebraicGeometry.OpenClosedRecollement
import Sheaf.AlgebraicGeometry.EtaleClosedImmersionEssentialImage
import Sheaf.AlgebraicGeometry.SmoothBaseChangeLimit
import Sheaf.AlgebraicGeometry.UnboundedAbelianExchangeComparison
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FiniteProjectiveInternalHomEvaluation
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Algebra.Homology.KInjectiveHomComplex
import WeilConjectures.Algebra.Homology.RhomGlobalSections
import WeilConjectures.Algebra.Homology.HomTensorTotal
import Sheaf.Paper.SfHomTriangulated
import Sheaf.AlgebraicGeometry.IsIsoIffOfJointlySurjectiveEtaleFamily
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtaleOver
import Sheaf.AlgebraicGeometry.EtaleSmoothZeroDimensionalFibres
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import WeilConjectures.Mathlib.Topology.KrullDimension
import Sheaf.Paper.ExchangeIdentityPasting
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.FiniteComparison
import WeilConjectures.AlgebraicGeometry.InverseImageStalkGerm
import WeilConjectures.RingTheory.LocalizationColimitPrincipalLocalizations
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import Sheaf.Algebra.Homology.RingedInternalHomExactRestriction
import Sheaf.CategoryTheory.RingedSliceExtensionTensor
import Sheaf.Paper.ProEtaleCanonicalTensorPullback
import Sheaf.Algebra.Homology.SiteDerivedTensorDescent
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import WeilConjectures.ConstructibleSheaf.KernelCokernel
import Sheaf.AlgebraicGeometry.FiniteTypeDirectImageConstructibility
import Sheaf.Algebra.Homology.RingedInternalHomShiftOfUniverses
import Sheaf.AlgebraicGeometry.EtaleClosedSupportTriangle
import Sheaf.AlgebraicGeometry.EtaleGenericDirectImageExchange
import Sheaf.AlgebraicGeometry.EtaleGenericEvaluationCoherence
import Sheaf.AlgebraicGeometry.EtaleGenericImmersionProjection
import Sheaf.AlgebraicGeometry.EtaleGenericStratumMate
import Sheaf.AlgebraicGeometry.SmoothStratificationFiniteTor
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
import Sheaf.Paper.StratumAmbientHom
import Sheaf.SixFunctors.EtaleGenericHomTriangle
import Sheaf.SixFunctors.EtaleGenericPerfectHom

/-! # Ordinary etale exchange at a geometric generic point

Source: Stacks Project, Tags 0F09, 0GIT, 0A45 and 09BI; the ordinary-etale
geometric-generic argument of blueprint sk-prop-sf-biduality-general
(blueprint: lem-sf-etale-generic-exchange-algclosed).

The coefficient ring is arbitrary finite commutative. The base field is arbitrary
algebraically closed. Closed exceptional inverse image is the right adjoint of ordinary
closed direct image, with no compactification or pro-etale coefficient convention.

## Main declarations

- `closedSupportExchange`: the closed-adjunction mate of inverse direct-image exchange.
- `inverseImageHomExchange`: the tensor-Hom transpose of pulled-back evaluation.
- `isIso_closedSupportExchange_geometricGeneric` and
  `isIso_inverseImageHomExchange_geometricGeneric`: the geometric-generic isomorphisms.
- The remaining theorem declarations specify counit, evaluation, shift, tensor and open
  restriction compatibility for these canonical maps.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

/-- The geometric generic point from a nonempty affine chart, its fraction field, and an
algebraic closure. Source: Stacks Tags 01JX and 0F09
(blueprint: lem-sf-etale-generic-exchange-algclosed). -/
noncomputable def geometricGenericMap {B : Scheme.{u}} (U : B.Opens)
    (hU : IsAffineOpen U) (Q : Type u) [Field Q] [Algebra (B.presheaf.obj (op U)) Q]
    (L : Type u) [Field L] [Algebra Q L] : Spec (.of L) ⟶ B :=
  Spec.map (CommRingCat.ofHom
    ((algebraMap Q L).comp (algebraMap (B.presheaf.obj (op U)) Q))) ≫ hU.fromSpec

/-- The canonical ordinary-etale closed-support comparison is the transpose of inverse
closed direct-image exchange followed by the pulled-back counit. Source: Stacks Tag 0A45,
proof step 4 of the node (blueprint: lem-sf-etale-generic-exchange-algclosed). -/
noncomputable def closedSupportExchange (A : Type (u + 1)) [CommRing A] [Finite A]
    {Z X Z' X' : Scheme.{u}} {i : Z ⟶ X} {i' : Z' ⟶ X'}
    [IsClosedImmersion i] [IsClosedImmersion i'] {gZ : Z' ⟶ Z} {gX : X' ⟶ X}
    (sq : IsPullback gZ i' i gX) :
    ((lowerStar (ModuleCat.{u + 1} A) i).rightDerivedFunctor).rightAdjoint ⋙
        (upperStar (ModuleCat.{u + 1} A) gZ).leftDerivedFunctor ⟶
      (upperStar (ModuleCat.{u + 1} A) gX).leftDerivedFunctor ⋙
        ((lowerStar (ModuleCat.{u + 1} A) i').rightDerivedFunctor).rightAdjoint :=
  letI := isIso_derivedBaseChangeMap_of_isProper_of_isAddTorsion_ring A
    isAddTorsion_of_finite sq
  (mateEquiv
    (Adjunction.ofIsLeftAdjoint ((lowerStar (ModuleCat.{u + 1} A) i).rightDerivedFunctor))
    (Adjunction.ofIsLeftAdjoint ((lowerStar (ModuleCat.{u + 1} A) i').rightDerivedFunctor))
    (TwoSquare.mk _ _ _ _ (asIso
      (derivedBaseChangeMap (ModuleCat.{u + 1} A) sq.toCommSq)).inv)).natTrans

/-- The internal-Hom exchange is the tensor-Hom transpose of pulled-back evaluation.
Source: Stacks Tags 09BI and 0F09, proof steps 5 and 8 of the node
(blueprint: lem-sf-etale-generic-exchange-algclosed). -/
noncomputable def inverseImageHomExchange (A : Type (u + 1)) [CommRing A]
    {Y X : Scheme.{u}} (g : Y ⟶ X) (K M : DerivedCategoryModule A X) :
    ((upperStar (ModuleCat.{u + 1} A) g).leftDerivedFunctor).obj
        (((derivedHom (ModuleCat.{u + 1} A) X).obj (op K)).obj M) ⟶
      ((derivedHom (ModuleCat.{u + 1} A) Y).obj
        (op (((upperStar (ModuleCat.{u + 1} A) g).leftDerivedFunctor).obj K))).obj
          (((upperStar (ModuleCat.{u + 1} A) g).leftDerivedFunctor).obj M) :=
  (derivedTensorHomAdjunction (ModuleCat.{u + 1} A)
    (((upperStar (ModuleCat.{u + 1} A) g).leftDerivedFunctor).obj K)).homEquiv _ _
      ((leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} A) g K
        (((derivedHom (ModuleCat.{u + 1} A) X).obj (op K)).obj M)).inv ≫
          ((upperStar (ModuleCat.{u + 1} A) g).leftDerivedFunctor).map
            ((derivedTensorHomAdjunction (ModuleCat.{u + 1} A) K).counit.app M))

/-- Canonical shift isomorphism for the closed right adjoint, transported across its
adjunction. Source: Stacks Tag 0A45, proof step 9
(blueprint: lem-sf-etale-generic-exchange-algclosed). -/
noncomputable def closedSupportShiftIso
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] (n : ℤ) :
    shiftFunctor (DerivedCategoryModule A X) n ⋙
        ((lowerStar (ModuleCat.{u + 1} A) i).rightDerivedFunctor).rightAdjoint ≅
      ((lowerStar (ModuleCat.{u + 1} A) i).rightDerivedFunctor).rightAdjoint ⋙
        shiftFunctor (DerivedCategoryModule A Z) n :=
  Adjunction.RightAdjointCommShift.iso (Adjunction.ofIsLeftAdjoint
    ((lowerStar (ModuleCat.{u + 1} A) i).rightDerivedFunctor)) n

/-- The inverse closed-direct-image projection formula used to define exceptional tensor
comparison. Source: Stacks Tag 0A45, proof step 9
(blueprint: lem-sf-etale-generic-exchange-algclosed). -/
noncomputable def closedSupportProjectionIso
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (C : DerivedCategoryModule A Z) (Q : DerivedCategoryModule A X) :=
  letI := isIso_rightDerivedLowerStarProjectionMap_of_finite A i
  asIso (((rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} A) i).app C).app Q)

/-- The canonical tensor comparison for the closed right adjoint is the adjoint of
inverse projection formula followed by the old counit tensored with the identity.
Source: Stacks Tag 0A45, proof step 9
(blueprint: lem-sf-etale-generic-exchange-algclosed). -/
noncomputable def closedSupportTensorComparison
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (M Q : DerivedCategoryModule A X) :
    ((derivedTensor (ModuleCat.{u + 1} A) Z).obj
      (((lowerStar (ModuleCat.{u + 1} A) i).rightDerivedFunctor).rightAdjoint.obj M)).obj
        (((upperStar (ModuleCat.{u + 1} A) i).leftDerivedFunctor).obj Q) ⟶
      ((lowerStar (ModuleCat.{u + 1} A) i).rightDerivedFunctor).rightAdjoint.obj
        (((derivedTensor (ModuleCat.{u + 1} A) X).obj M).obj Q) :=
  (Adjunction.ofIsLeftAdjoint
    ((lowerStar (ModuleCat.{u + 1} A) i).rightDerivedFunctor)).homEquiv _ _
      ((closedSupportProjectionIso A i
        (((lowerStar (ModuleCat.{u + 1} A) i).rightDerivedFunctor).rightAdjoint.obj M) Q).inv ≫
        ((derivedTensor (ModuleCat.{u + 1} A) X).map
          ((Adjunction.ofIsLeftAdjoint
            ((lowerStar (ModuleCat.{u + 1} A) i).rightDerivedFunctor)).counit.app M)).app Q)

/-- Counit normalization of the specified closed-support comparison.
Source: Stacks Tag 0A45, proof steps 4 and 9
(blueprint: lem-sf-etale-generic-exchange-algclosed).
Proof: apply the counit identity for mates to inverse closed direct-image exchange.
Precompose with direct-image exchange and cancel its inverse. This gives precisely
pullback of the original exceptional counit. -/
theorem closedSupportExchange_counit
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {Z X Z' X' : Scheme.{u}} {i : Z ⟶ X} {i' : Z' ⟶ X'}
    [IsClosedImmersion i] [IsClosedImmersion i'] {gZ : Z' ⟶ Z} {gX : X' ⟶ X}
    (sq : IsPullback gZ i' i gX) (M : DerivedCategoryModule A X) :
    (derivedBaseChangeMap (ModuleCat.{u + 1} A) sq.toCommSq).app
        (((lowerStar (ModuleCat.{u + 1} A) i).rightDerivedFunctor).rightAdjoint.obj M) ≫
      ((lowerStar (ModuleCat.{u + 1} A) i').rightDerivedFunctor).map
        ((closedSupportExchange A sq).app M) ≫
      (Adjunction.ofIsLeftAdjoint
        ((lowerStar (ModuleCat.{u + 1} A) i').rightDerivedFunctor)).counit.app
          (((upperStar (ModuleCat.{u + 1} A) gX).leftDerivedFunctor).obj M) =
    ((upperStar (ModuleCat.{u + 1} A) gX).leftDerivedFunctor).map
      ((Adjunction.ofIsLeftAdjoint
        ((lowerStar (ModuleCat.{u + 1} A) i).rightDerivedFunctor)).counit.app M) := by
  sorry

/-- The comparison is the transpose of pulled-back evaluation, with the canonical tensor
identification. We write evaluation with K first; symmetry gives the displayed
Hom tensor K convention of the node. Source: Stacks Tag 09BI, proof steps 5 and 8
(blueprint: lem-sf-etale-generic-exchange-algclosed).
Proof: cancel the tensor-Hom adjunction homEquiv with its inverse in the definition.
The resulting composite is exactly inverse tensor pullback followed by pulled-back
original evaluation. Composing with the symmetry gives evaluation with K on the right. -/
theorem inverseImageHomExchange_evaluation
    (A : Type (u + 1)) [CommRing A] {Y X : Scheme.{u}} (g : Y ⟶ X)
    (K M : DerivedCategoryModule A X) :
    ((derivedTensor (ModuleCat.{u + 1} A) Y).obj
      (((upperStar (ModuleCat.{u + 1} A) g).leftDerivedFunctor).obj K)).map
        (inverseImageHomExchange A g K M) ≫
      (derivedTensorHomAdjunction (ModuleCat.{u + 1} A)
        (((upperStar (ModuleCat.{u + 1} A) g).leftDerivedFunctor).obj K)).counit.app
          (((upperStar (ModuleCat.{u + 1} A) g).leftDerivedFunctor).obj M) =
    (leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} A) g K
      (((derivedHom (ModuleCat.{u + 1} A) X).obj (op K)).obj M)).inv ≫
      ((upperStar (ModuleCat.{u + 1} A) g).leftDerivedFunctor).map
        ((derivedTensorHomAdjunction (ModuleCat.{u + 1} A) K).counit.app M) := by
  sorry

/-- Closed-support exchange respects the canonical adjunction shift structures.
Source: Stacks Tag 0A45, proof step 9
(blueprint: lem-sf-etale-generic-exchange-algclosed).
Proof: shift the support triangle and its counit. The shifted comparison and the comparison
on the shifted input have the same counit transpose. Uniqueness in the closed adjunction
identifies them, with the shift isomorphisms transported across that adjunction. -/
theorem closedSupportExchange_commShift
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {Z X Z' X' : Scheme.{u}} {i : Z ⟶ X} {i' : Z' ⟶ X'}
    [IsClosedImmersion i] [IsClosedImmersion i'] {gZ : Z' ⟶ Z} {gX : X' ⟶ X}
    (sq : IsPullback gZ i' i gX) :
    ∀ (M : DerivedCategoryModule A X) (n : ℤ),
    (closedSupportExchange A sq).app (M⟦n⟧) ≫
      ((lowerStar (ModuleCat.{u + 1} A) i').rightDerivedFunctor).rightAdjoint.map
        ((((upperStar (ModuleCat.{u + 1} A) gX).leftDerivedFunctor).commShiftIso n).hom.app
          M) ≫
      (closedSupportShiftIso A i' n).hom.app
        (((upperStar (ModuleCat.{u + 1} A) gX).leftDerivedFunctor).obj M) =
    ((upperStar (ModuleCat.{u + 1} A) gZ).leftDerivedFunctor).map
        ((closedSupportShiftIso A i n).hom.app M) ≫
      (((upperStar (ModuleCat.{u + 1} A) gZ).leftDerivedFunctor).commShiftIso n).hom.app
        (((lowerStar (ModuleCat.{u + 1} A) i).rightDerivedFunctor).rightAdjoint.obj M) ≫
      ((closedSupportExchange A sq).app M)⟦n⟧' := by
  sorry

/-- The two arrows in the tensor compatibility square, with all canonical tensor and
inverse-image-composition identifications displayed. Source: Stacks Tag 0A45, proof step 9
(blueprint: lem-sf-etale-generic-exchange-algclosed). -/
def ClosedSupportExchangeTensorCompatible
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {Z X Z' X' : Scheme.{u}} {i : Z ⟶ X} {i' : Z' ⟶ X'}
    [IsClosedImmersion i] [IsClosedImmersion i'] {gZ : Z' ⟶ Z} {gX : X' ⟶ X}
    (sq : IsPullback gZ i' i gX) (M Q : DerivedCategoryModule A X) : Prop :=
    ((upperStar (ModuleCat.{u + 1} A) gZ).leftDerivedFunctor).map
        (closedSupportTensorComparison A i M Q) ≫
      (closedSupportExchange A sq).app
        (((derivedTensor (ModuleCat.{u + 1} A) X).obj M).obj Q) ≫
      ((lowerStar (ModuleCat.{u + 1} A) i').rightDerivedFunctor).rightAdjoint.map
        (leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} A) gX M Q).hom =
    (leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} A) gZ
      (((lowerStar (ModuleCat.{u + 1} A) i).rightDerivedFunctor).rightAdjoint.obj M)
      (((upperStar (ModuleCat.{u + 1} A) i).leftDerivedFunctor).obj Q)).hom ≫
      ((derivedTensor (ModuleCat.{u + 1} A) Z').map
        ((closedSupportExchange A sq).app M)).app
          (((upperStar (ModuleCat.{u + 1} A) gZ).leftDerivedFunctor).obj
            (((upperStar (ModuleCat.{u + 1} A) i).leftDerivedFunctor).obj Q)) ≫
      ((derivedTensor (ModuleCat.{u + 1} A) Z').obj
        (((lowerStar (ModuleCat.{u + 1} A) i').rightDerivedFunctor).rightAdjoint.obj
          (((upperStar (ModuleCat.{u + 1} A) gX).leftDerivedFunctor).obj M))).map
            ((derivedSquareUpperStarIso (ModuleCat.{u + 1} A) sq.toCommSq).inv.app Q) ≫
      closedSupportTensorComparison A i'
        (((upperStar (ModuleCat.{u + 1} A) gX).leftDerivedFunctor).obj M)
        (((upperStar (ModuleCat.{u + 1} A) gX).leftDerivedFunctor).obj Q)

/-- Closed-support exchange respects tensoring with an invertible locally constant
rank-one coefficient sheaf. Rank one is expressed by a trivializing etale cover with
constant value A; invertible explicitly means possession of a tensor inverse.
Source: Stacks Tag 0A45, proof step 9
(blueprint: lem-sf-etale-generic-exchange-algclosed).
Proof: etale locally trivialize Q. The closed projection map and its inverse are the
identity on the support and zero outside; on overlaps both transition maps multiply
by the same unit. Tensor with Q is exact since Q has a tensor inverse. Thus the
exceptional tensor comparison is the closed adjunction mate of the original counit
tensored with Q. Pull back this identity and use the inverse-image tensor identification.
Both paths in the displayed square have the same exceptional counit transpose. The
closed adjunction identifies them. The tensor inverse gives invertibility of these
exceptional tensor comparisons. -/
theorem closedSupportExchange_tensor
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {Z X Z' X' : Scheme.{u}} {i : Z ⟶ X} {i' : Z' ⟶ X'}
    [IsClosedImmersion i] [IsClosedImmersion i'] {gZ : Z' ⟶ Z} {gX : X' ⟶ X}
    (sq : IsPullback gZ i' i gX) (M : DerivedCategoryModule A X)
    (Q : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))
    (_hQ : ∃ d : Scheme.LocallyConstantDatum Q, ∀ k : d.cover.I₀,
      Nonempty (Q.over (d.cover.etalePrecoverageToEtale k) ≅
        (constantSheaf
          (X.smallEtaleTopology.over (d.cover.etalePrecoverageToEtale k))
          (ModuleCat.{u + 1} A)).obj (ModuleCat.of A A)))
    (_hInv : ∃ Qinv : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A),
      Nonempty (Q ⊗ Qinv ≅ 𝟙_ _) ∧ Nonempty (Qinv ⊗ Q ≅ 𝟙_ _)) :
    ClosedSupportExchangeTensorCompatible A sq M
      ((_root_.DerivedCategory.singleFunctor _ 0).obj Q) ∧
    IsIso (closedSupportTensorComparison A i M
      ((_root_.DerivedCategory.singleFunctor _ 0).obj Q)) ∧
    IsIso (closedSupportTensorComparison A i'
      (((upperStar (ModuleCat.{u + 1} A) gX).leftDerivedFunctor).obj M)
      (((upperStar (ModuleCat.{u + 1} A) gX).leftDerivedFunctor).obj
        ((_root_.DerivedCategory.singleFunctor _ 0).obj Q))) := by
  sorry

/-- Paste two closed-support comparisons using the canonical inverse-image composition
isomorphisms. The common composite maps are specified, so two orders of restriction
have identical endpoints. Source: Stacks Tag 0A45, proof step 9
(blueprint: lem-sf-etale-generic-exchange-algclosed). -/
noncomputable def pastedClosedSupportExchange
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {Z X Z' X' Z'' X'' : Scheme.{u}}
    {i : Z ⟶ X} {i' : Z' ⟶ X'} {i'' : Z'' ⟶ X''}
    [IsClosedImmersion i] [IsClosedImmersion i'] [IsClosedImmersion i'']
    {gZ : Z' ⟶ Z} {gX : X' ⟶ X} {hZ : Z'' ⟶ Z'} {hX : X'' ⟶ X'}
    (sq : IsPullback gZ i' i gX) (sq' : IsPullback hZ i'' i' hX)
    (kZ : Z'' ⟶ Z) (kX : X'' ⟶ X) (hkZ : kZ = hZ ≫ gZ) (hkX : kX = hX ≫ gX)
    (M : DerivedCategoryModule A X) :
    (((upperStar (ModuleCat.{u + 1} A) kZ).leftDerivedFunctor).obj
      (((lowerStar (ModuleCat.{u + 1} A) i).rightDerivedFunctor).rightAdjoint.obj M)) ⟶
    ((lowerStar (ModuleCat.{u + 1} A) i'').rightDerivedFunctor).rightAdjoint.obj
      (((upperStar (ModuleCat.{u + 1} A) kX).leftDerivedFunctor).obj M) :=
  (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) hZ gZ kZ hkZ).hom.app
      (((lowerStar (ModuleCat.{u + 1} A) i).rightDerivedFunctor).rightAdjoint.obj M) ≫
    ((upperStar (ModuleCat.{u + 1} A) hZ).leftDerivedFunctor).map
      ((closedSupportExchange A sq).app M) ≫
    (closedSupportExchange A sq').app
      (((upperStar (ModuleCat.{u + 1} A) gX).leftDerivedFunctor).obj M) ≫
    ((lowerStar (ModuleCat.{u + 1} A) i'').rightDerivedFunctor).rightAdjoint.map
      ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) hX gX kX hkX).inv.app M)

/-- Closed-support exchange commutes with open restriction: the base-change then open
restriction path equals the open restriction then base-change path of the cartesian cube.
Source: Stacks Tag 0A45 and Tag 0F09, proof step 9
(blueprint: lem-sf-etale-generic-exchange-algclosed).
Proof: open restriction carries the support triangle to the support triangle for the
restricted closed immersion. Ordinary direct-image exchange for the open immersion
identifies their counits. The two paths in the cube are the transpose of the same
restricted exceptional counit; inverse-image composition and direct-image exchange
pasting identify their endpoints and transposes. Uniqueness of adjunction gives equality. -/
theorem closedSupportExchange_openRestriction
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {Z X Z' X' W V W' V' : Scheme.{u}}
    {i : Z ⟶ X} {i' : Z' ⟶ X'} {c : W ⟶ V} {c' : W' ⟶ V'}
    [IsClosedImmersion i] [IsClosedImmersion i']
    [IsClosedImmersion c] [IsClosedImmersion c']
    {gZ : Z' ⟶ Z} {gX : X' ⟶ X} {pZ : W ⟶ Z} {pX : V ⟶ X}
    {qZ : W' ⟶ Z'} {qX : V' ⟶ X'} {hZ : W' ⟶ W} {hX : V' ⟶ V}
    [IsOpenImmersion pX] [IsOpenImmersion qX]
    (sq : IsPullback gZ i' i gX) (sqU : IsPullback hZ c' c hX)
    (openSq : IsPullback pZ c i pX) (openSq' : IsPullback qZ c' i' qX)
    (hZcomm : qZ ≫ gZ = hZ ≫ pZ) (hXcomm : qX ≫ gX = hX ≫ pX)
    (M : DerivedCategoryModule A X) :
    pastedClosedSupportExchange A sq openSq' (qZ ≫ gZ) (qX ≫ gX) rfl rfl M =
    pastedClosedSupportExchange A openSq sqU (qZ ≫ gZ) (qX ≫ gX) hZcomm hXcomm M := by
  sorry

/-- Closed-support exchange at the geometric generic point is invertible.
Source: Stacks Tags 0F09, 0GIT and 0A45
(blueprint: lem-sf-etale-generic-exchange-algclosed).

Proof:
1. On a nonempty affine chart Spec R of B, express Frac R as the filtered colimit of
   R[1/f], f nonzero. Spec carries this colimit to the inverse limit of principal opens.
   Apply lem-kun-0f09 to this system of smooth affine open immersions and a qcqs map.
2. Apply lem-kun-0f1c-exchange to L/Frac R, including inseparable algebraic extensions.
   The module/abelian comparison lem-kun-unbounded-abelian-exchange-comparison and
   exchange pasting identify the composite with the actual module exchange.
3. For the open complement j of i, the support triangle identifies i_* Ri! M with
   the fibre of M → Rj_* j* M. Finite-type direct-image constructibility and the Serre
   property of constructible sheaves show Ri! M is bounded constructible. Exact closed
   pushforward and its inverse-image left inverse identify its cohomology on Z.
4. Pull back this triangle. The ordinary direct-image exchanges for i and j identify
   its other terms with the support triangle on the geometric generic fibre. The
   first map is the mate of inverse exchange and the pulled-back counit, exactly
   closedSupportExchange. The two other maps are isomorphisms, so its closed pushforward
   is an isomorphism. Exact fully faithful closed pushforward reflects isomorphisms.
This argument uses the actual algebraically closed field F, with no finite-field base. -/
theorem isIso_closedSupportExchange_geometricGeneric
    (F : Type u) [Field F] [IsAlgClosed F]
    (N : ℕ) (_hN : 1 ≤ N) (_hNF : IsUnit (N : F))
    (A : Type (u + 1)) [CommRing A] [Finite A] (_hNA : (N : A) = 0)
    (B : Scheme.{u}) (b : B ⟶ Spec (.of F)) [Smooth b] [IsIntegral B]
    [LocallyOfFiniteType b] [QuasiCompact b]
    (_hdim : topologicalKrullDim B = 1)
    (U : B.Opens) (hU : IsAffineOpen U) (_hUnonempty : Nonempty U)
    (Q : Type u) [Field Q] [Algebra (B.presheaf.obj (op U)) Q]
    [IsFractionRing (B.presheaf.obj (op U)) Q]
    (L : Type u) [Field L] [Algebra Q L] [Algebra.IsAlgebraic Q L] [IsAlgClosed L]
    (X : Scheme.{u}) (f : X ⟶ B) [IsSeparated f]
    [LocallyOfFiniteType f] [QuasiCompact f]
    (Z : Scheme.{u}) (i : Z ⟶ X) [IsClosedImmersion i]
    (M : DerivedCategoryModule A X) (_hM : DerivedCategory.isBoundedConstructible A X M) :
    IsIso ((closedSupportExchange A
      (IsPullback.of_hasPullback i (pullback.fst f (geometricGenericMap U hU Q L)))).app M) := by
  sorry

/-- The tensor-adjoint internal-Hom comparison at the geometric generic point is invertible.
Source: Stacks Tags 0F09, 09BI and 0A45
(blueprint: lem-sf-etale-generic-exchange-algclosed).

Proof:
1. For a finite locally perfect first complex, trivialize etale locally by a bounded
   complex of finite projective A-modules (09BI). Its Hom complex is a finite total
   complex of finite-projective dual tensor terms. Exact inverse image preserves its
   sums and splittings, and derived tensor pullback identifies the canonical evaluations.
   Thus the specified evaluation transpose is an isomorphism on these strata, with
   Hom cohomology bounded in [c-b,d-a] for Tor interval [a,b] and second interval [c,d].
2. Restrict to affine opens of X. This includes nonseparated B: each such open is
   separated and finite type over F. Tor amplitude survives open restriction by exact
   extension by zero. Apply lem-sf-etale-smooth-stratified-ctf to obtain the finite
   smooth-stratum localization filtration of K, in its actual Tor interval.
3. For each stratum s, the ambient-stratum Hom adjunction identifies Hom(Rs! P,M)
   with Rs_* Hom(P,Rs! M). Closed-support constructibility makes Rs! M bounded.
   The local calculation makes the Hom input bounded. Apply generic ordinary
   direct-image exchange, the local Hom calculation, and closed-support exchange.
   Closed pushforward exchange and the stalk formula for open extension by zero
   identify the first input after base change with Rs_generic! of the pulled-back P.
4. The ambient-stratum isomorphism is determined by the tensor-Hom adjunction,
   projection formula, inverse/direct-image adjunction, and exceptional counit.
   Transposing their composite gives pulled-back evaluation: the closed projection
   formula is identity on the support and zero off it; the open formula uses identical
   total-tensor summands. The Hom evaluation and exceptional counit identities then
   identify the piecewise comparison with inverseImageHomExchange, rather than an
   unspecified isomorphism. Naturality of evaluation gives a morphism of the Hom
   localization triangles. Induct along the finite filtration, starting at zero.
The empty filtration, zero complex, empty scheme and N=1 cases are included. -/
theorem isIso_inverseImageHomExchange_geometricGeneric
    (F : Type u) [Field F] [IsAlgClosed F]
    (N : ℕ) (_hN : 1 ≤ N) (_hNF : IsUnit (N : F))
    (A : Type (u + 1)) [CommRing A] [Finite A] (_hNA : (N : A) = 0)
    (B : Scheme.{u}) (b : B ⟶ Spec (.of F)) [Smooth b] [IsIntegral B]
    [LocallyOfFiniteType b] [QuasiCompact b]
    (_hdim : topologicalKrullDim B = 1)
    (U : B.Opens) (hU : IsAffineOpen U) (_hUnonempty : Nonempty U)
    (Q : Type u) [Field Q] [Algebra (B.presheaf.obj (op U)) Q]
    [IsFractionRing (B.presheaf.obj (op U)) Q]
    (L : Type u) [Field L] [Algebra Q L] [Algebra.IsAlgebraic Q L] [IsAlgClosed L]
    (X : Scheme.{u}) (f : X ⟶ B) [IsSeparated f]
    [LocallyOfFiniteType f] [QuasiCompact f]
    (K M : DerivedCategoryModule A X)
    (_hK : DerivedCategory.isBoundedConstructible A X K)
    (_hM : DerivedCategory.isBoundedConstructible A X M)
    (_hTor : ∃ a b : ℤ, DerivedCategory.hasTorAmplitudeIn A X a b K) :
    IsIso (inverseImageHomExchange A (pullback.fst f (geometricGenericMap U hU Q L)) K M) := by
  sorry

end AlgebraicGeometry.Etale
