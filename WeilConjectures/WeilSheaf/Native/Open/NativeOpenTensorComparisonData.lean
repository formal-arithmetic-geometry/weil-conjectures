/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.LowerShriek
public import WeilConjectures.WeilSheaf.UpperStarComp
public import WeilConjectures.WeilSheaf.SixFunctors.DerivedWeilTensorOperations
public import WeilConjectures.WeilSheaf.Native.Weil.NativeWeilClosedForgetful
public import WeilConjectures.CategoryTheory.Native.NativeOpenTensorPresentation
public import WeilConjectures.WeilSheaf.Native.Open.NativeOpenTensorOperations
public import WeilConjectures.Algebra.Homology.OpenTensorNormalization.ExactDerivedAdjunctionSupplement
import WeilConjectures.SixFunctors.ProEtale.Adic.Constructible
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import WeilConjectures.Algebra.Homology.BifunctorHomComplex
public import WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Braided
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.ClosedTriangulated
public import WeilConjectures.CategoryTheory.DerivedCategory.ProEtaleCoefficients.DerivedMonoidalClosed
public import WeilConjectures.CategoryTheory.Endofunctor.EquivalenceOrbitInduction
public import WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebraCompIso
public import WeilConjectures.CategoryTheory.ProEtaleCoefficients.PreservesTotalTensorKFlatQuasiIsoSupplement
public import WeilConjectures.DeligneLaumon.NativeWeilDerivedFramework
public import WeilConjectures.Mathlib.CategoryTheory.Endofunctor.Algebra
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import WeilConjectures.SixFunctors.CoefficientClosedStructure.CoefficientRingedTensorHomModelSupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.MonoidalModule

/-! # Native open comparison data

The data types are extracted verbatim from NativeOpenDerivedTensor so that the
sheaf construction, localization, and normalization can be proved independently.
Source: Stacks 0E8I and 0GL1
(blueprint: def-sf-native-open-tensor-presentation-data).
-/

@[expose] public noncomputable section

set_option autoImplicit false

attribute [local irreducible]
  AlgebraicGeometry.ProEtaleWeilSheaf.nativeDerivedClosedComparison

universe u a b

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtaleWeilSheaf

variable (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
  [Fact (ringChar k₀ ≠ l)]

variable {U Z : Scheme.{u}} [U.Over (Spec (CommRingCat.of k₀))]
  [Z.Over (Spec (CommRingCat.of k₀))] (j : U ⟶ Z) [IsOpenImmersion j]
  [j.IsOver (Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (U ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (U ↘ Spec (CommRingCat.of k₀))]
  [IsSeparated (U ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (Z ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Z ↘ Spec (CommRingCat.of k₀))]
  [IsSeparated (Z ↘ Spec (CommRingCat.of k₀))]

/-- All normalizations of the native open tensor isomorphism. These are conclusions
of the theorem below, not extra hypotheses on the open immersion or its inputs.
The coefficient localization is the actual adic coefficient pullback used by upperStar.
Source: Stacks 0E8I, 0GL1, 03D8 and openTensorNormalization
(blueprint: lem-sf-native-open-derived-tensor). -/
structure NativeOpenTensorData where
  /-- The equivariant open adjunction. -/
  adj : extensionByZero k₀ l j ⊣ upperStar k₀ l j
  /-- Its unit is the ordinary unit on the geometric open. -/
  unit_forget : ∀ M, (adj.unit.app M).hom.f =
    (ProEtale.adicOpenImmersionLowerShriekAdjunction l
      (Scheme.Hom.geometricFiberMap j (comp_over j _))).unit.app M.carrier
  /-- Its counit is the ordinary counit, fixing the adjunction itself. -/
  counit_forget : ∀ N, (adj.counit.app N).hom.f =
    (ProEtale.adicOpenImmersionLowerShriekAdjunction l
      (Scheme.Hom.geometricFiberMap j (comp_over j _))).counit.app N.carrier
  /-- The open unit is invertible. -/
  unit_iso : ∀ M, IsIso (adj.unit.app M)
  /-- Restriction commutes with sheaf tensor. -/
  sheafRestriction : ∀ M N : ProEtaleWeilSheaf k₀ l Z,
    (upperStar k₀ l j).obj (tensor k₀ l Z N M) ≅
      tensor k₀ l U ((upperStar k₀ l j).obj N) ((upperStar k₀ l j).obj M)
  /-- Its underlying map is the canonical balanced tensor comparison. -/
  restriction_forget : ∀ M N, HEq ((sheafRestriction M N).hom.hom.f) (
    (ProEtale.adicUpperStarTensorLeftIso l
      (Scheme.Hom.geometricFiberMap j (comp_over j _)) N.carrier).hom.app M.carrier)
  /-- The generator-normalized, equivariant sheaf open tensor isomorphism. -/
  sheafGamma : ∀ (M : ProEtaleWeilSheaf k₀ l U) (N : ProEtaleWeilSheaf k₀ l Z),
    tensor k₀ l Z N ((extensionByZero k₀ l j).obj M) ≅
      (extensionByZero k₀ l j).obj (tensor k₀ l U ((upperStar k₀ l j).obj N) M)
  /-- Its inverse is the unit transpose, which fixes both maps uniquely. -/
  sheaf_inverse : ∀ M N, HEq (adj.homEquiv _ _ ((sheafGamma M N).inv)) (
    (tensorFunctor k₀ l U ((upperStar k₀ l j).obj N)).map (adj.unit.app M) ≫
      (sheafRestriction ((extensionByZero k₀ l j).obj M) N).inv)
  /-- Exact extension preserves categorical two-sided K-flatness. -/
  extension_kflat : ∀ P, NativeIsKFlat k₀ l U P → NativeIsKFlat k₀ l Z
    (((extensionByZero k₀ l j).mapHomologicalComplex (.up ℤ)).obj P)
  /-- Exact restriction preserves categorical two-sided K-flatness. -/
  restriction_kflat : ∀ T, NativeIsKFlat k₀ l Z T → NativeIsKFlat k₀ l U
    (((upperStar k₀ l j).mapHomologicalComplex (.up ℤ)).obj T)

/-- Chain and derived comparisons extending the normalized sheaf comparison.
Source: Stacks 0GL1 (blueprint: lem-sf-native-open-derived-tensor). -/
structure NativeOpenDerivedTensorData (sheaves : NativeOpenTensorData k₀ l j) where
  /-- The natural isomorphism on arbitrary ambient derived inputs. -/
  gamma : nativeOpenDerivedLeft k₀ l j ≅ nativeOpenDerivedRight k₀ l j
  /-- Derived restriction and tensor comparison. -/
  restriction : nativeDerivedTensor k₀ l Z ⋙ nativeOpenPull k₀ l j ≅
    (nativeOpenPull k₀ l j).prod (nativeOpenPull k₀ l j) ⋙ nativeDerivedTensor k₀ l U
  /-- The inverse is the open-unit transpose in the actual derived adjunction. -/
  inverse_unit : OpenTensorUnitNormalization
    (nativeOpenExtension k₀ l j) (nativeOpenPull k₀ l j)
    (nativeDerivedTensor k₀ l U) (nativeDerivedTensor k₀ l Z)
    sheaves.adj.mapExactDerivedCategory restriction gamma
  /-- Ordinary normalization and the equality after forgetting Frobenius. -/
  ordinary : Nonempty (OpenTensorForgetData
    (nativeOpenExtension k₀ l j) (nativeOpenPull k₀ l j)
    (ProEtale.adicOpenImmersionLowerShriek l
      (Scheme.Hom.geometricFiberMap j (comp_over j _))).mapDerivedCategory
    (ProEtale.adicUpperStar l
      (Scheme.Hom.geometricFiberMap j (comp_over j _))).mapDerivedCategory
    (nativeForget k₀ l U) (nativeForget k₀ l Z)
    (nativeDerivedTensor k₀ l U) (nativeDerivedTensor k₀ l Z)
    (nativeDerivedClosedComparison k₀ l U).ordinaryClosed.tensor
    (nativeDerivedClosedComparison k₀ l Z).ordinaryClosed.tensor
    (nativeOpenForgetExtension k₀ l j) (nativeOpenForgetPull k₀ l j)
    (nativeDerivedClosedComparison k₀ l U).tensorComparison
    (nativeDerivedClosedComparison k₀ l Z).tensorComparison
    (ProEtale.adicOpenImmersionLowerShriekAdjunction l
      (Scheme.Hom.geometricFiberMap j (comp_over j _))).mapExactDerivedCategory restriction gamma)

/-- Every operation and representative in the presentation is the actual native one.
HEq records equality of dependent presentations without imposing another tensor choice.
Source: Stacks 0GL1 (blueprint: lem-sf-native-open-derived-tensor). -/
def NativeOpenPresentationCompatibility (s : NativeOpenTensorData k₀ l j)
    (d : NativeOpenDerivedTensorData k₀ l j s)
    (c : OpenTensorPresentation (ProEtaleWeilSheaf k₀ l U) (ProEtaleWeilSheaf k₀ l Z)) :
    Prop :=
  HEq c.E (extensionByZero k₀ l j) ∧ HEq c.R (upperStar k₀ l j) ∧
  HEq c.SA (nativeOpenSheafTensor k₀ l U) ∧ HEq c.SB (nativeOpenSheafTensor k₀ l Z) ∧
  HEq c.TA (nativeTensorTotal k₀ l U) ∧ HEq c.TB (nativeTensorTotal k₀ l Z) ∧
  HEq c.DA (nativeDerivedTensor k₀ l U) ∧ HEq c.DB (nativeDerivedTensor k₀ l Z) ∧
  HEq c.flatA (NativeIsKFlat k₀ l U) ∧ HEq c.flatB (NativeIsKFlat k₀ l Z) ∧
  HEq c.modelA (nativeOpenTensorModel k₀ l U) ∧
  HEq c.modelB (nativeOpenTensorModel k₀ l Z) ∧
  HEq c.iA (nativeOpenTensorInsertion k₀ l U) ∧
  HEq c.iB (nativeOpenTensorInsertion k₀ l Z) ∧
  HEq c.sheafGamma s.sheafGamma ∧ HEq c.gamma d.gamma ∧
  HEq c.sheafRestriction s.sheafRestriction ∧ HEq c.restriction d.restriction

end AlgebraicGeometry.ProEtaleWeilSheaf

namespace WeilConjectures

/-- The actual condensed Weil-module open extension.
Source: `prop-weil-operations` and the native framework
(blueprint: def-sf-native-open-tensor-presentation-data). -/
abbrev nativeComparisonExtension :=
  nativeWeilModuleOpenExtension (WeilCoefficient.ab c)
    (D.geometricFrobenius U₀) (D.geometricFrobenius Z₀)
    (D.geometricFiberMap j₀) (nativeWeilGeometricSquare D j₀)

/-- The actual condensed Weil-module restriction.
Source: `prop-weil-operations` and the native framework
(blueprint: def-sf-native-open-tensor-presentation-data). -/
abbrev nativeComparisonRestriction :=
  nativeWeilModulePullback (WeilCoefficient.ab c)
    (D.geometricFrobenius U₀) (D.geometricFrobenius Z₀)
    (D.geometricFiberMap j₀) (nativeWeilGeometricSquare D j₀)

/-- The actual ordinary relative derived tensor of condensed modules.
Source: the native framework and derived module tensor construction
(blueprint: def-sf-native-open-tensor-presentation-data). -/
abbrev nativeComparisonOrdinaryTensor :=
  MonoidalCategory.tensor (nativeWeilDerivedCategory ell c (D.geometricFiber X₀).left)

/-- Extension and restriction are the actual condensed Weil-module functors.
Source: the open projection factor in `fix-lem-tensor-adjunction`, Step 1
(blueprint: def-sf-native-open-tensor-presentation-data). -/
def NativeOpenFunctorCompatibility : Prop :=
  HEq p.E (nativeComparisonExtension D ell c j₀) ∧
  HEq p.R (nativeComparisonRestriction D ell c j₀)

/-- The sheaf and derived comparisons agree with the specified native data.
Each equality is a field so the kernel checks the dependent projections separately.
Source: the open projection factor in `fix-lem-tensor-adjunction`, Step 1
(blueprint: def-sf-native-open-tensor-presentation-data). -/
structure NativeOpenComparisonCompatibility (s : NativeOpenTensorData D ell c j₀)
    (d : NativeOpenDerivedTensorData D ell hell c j₀ s) : Prop where
  sheafGamma : HEq p.sheafGamma s.sheafGamma
  gamma : HEq p.gamma d.gamma
  sheafRestriction : HEq p.sheafRestriction s.sheafRestriction
  restriction : HEq p.restriction d.restriction

end WeilConjectures
