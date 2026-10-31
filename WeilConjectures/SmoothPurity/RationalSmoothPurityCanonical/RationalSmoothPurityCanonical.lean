/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.AdicSmoothDualizing.AdicSmoothDualizingIntegralDetection
public import WeilConjectures.PoincareDuality.RationalSmoothPurityCanonical.RationalSmoothPurityFiniteTrace
public import WeilConjectures.PoincareDuality.RationalSmoothPurityCanonical.PuritySourceTransports
public import WeilConjectures.SixFunctors.PurCompactSupport.IntegralCompactSupportCoefficientComparison
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.FiniteCoefficientSmoothPurity
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.SmoothTrace
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.HomComparison
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekComparison
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependence
import all WeilConjectures.PoincareDuality.RationalSmoothPurityCanonical.RationalSmoothPurityFiniteTrace
import all WeilConjectures.PoincareDuality.RationalSmoothPurityCanonical.PuritySourceTransports
import all WeilConjectures.SmoothPurity.Integral.IntegralOperationsWellDefinedSupplement
import WeilConjectures.SixFunctors.Integral.IntegralResidueTor
import WeilConjectures.PoincareDuality.RationalSmoothPurityCanonical.CanonicalFiniteUnitTensor
import WeilConjectures.PoincareDuality.RationalSmoothPurityCanonical.CanonicalFiniteUnitCounit
import all WeilConjectures.SixFunctors.SfProEtaleProjection.SfProEtaleProjectionFormula
import WeilConjectures.SixFunctors.Sf.SfIntegralReductionConservative
import WeilConjectures.SixFunctors.Integral.IntegralOrdinaryProjectionReduction

/-! # Canonical rational purity in the intrinsic constructible presentation

Source: main-20261015, prop-weil-operations.proof.md, sentences 3--4;
sk-prop-sp-rational, Steps 1--2, and thm-pur-adic-reconstruction
(blueprint: def-pur-canonical-rational-purity-realization).

The family is the localized trace transpose of the adically reconstructed unit
orientation. Its source transports retain the actual shift comparisons.
-/

set_option linter.privateModule false

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme CategoryTheory.Endofunctor MonoidalCategory
namespace WeilConjectures

namespace RationalSmoothPurityCanonical

attribute [local instance 3000] instCategoryDerivedCategory ScalarLocalization.category

attribute [local instance 0] ConstructibleExceptionalCoefficients.category

/-- The inherited shift retains the specified ambient object. -/
private theorem fullSubcategory_shift_obj {C : Type*} [Category C]
    (P0 : ObjectProperty C) (A : Type*) [AddMonoid A] [HasShift C A]
    [P0.IsStableUnderShift A] (K : P0.FullSubcategory) (a : A) :
    (K⟦a⟧).obj = K.obj⟦a⟧ := by
  unfold shiftFunctor ObjectProperty.hasShift
  rfl

attribute [local irreducible] completedIntegralCoefficientSheafUnrestricted
  completedIntegralCommRingSheafUnrestricted
  PurCompactSupport.image sfIntrinsicModuleEquivalence ProEtale.comparisonUpperStar
  IntegralOnSlice.duality ordinaryModel
  integralDerivedPullback integralCompletedTensor sfRationalScalarExtension
  HasDerivedCategory.standard SheafOfModules.monoidalCategory
  rationalDerivedTensor rationalDerivedPullback rationalSource
  Functor.mapIso Iso.trans Iso.prod Functor.mapDerivedCategory
  Functor.mapDerivedCategoryFactors Functor.leftAdjoint
  IntegralOnSlice.completion
  IntegralOnSlice.completionUnit IntegralOnSlice.completionComparison IntegralOnSlice.roosUnit
  IntegralAmbient.pull IntegralAmbient.pullTowerIso IntegralAmbient.pullOperationUnit

section RelativeOrientation
variable (P : PurityFiniteSetting.{u}) {X Y : Scheme.{u}}
  [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
  [QuasiCompact (X ↘ Spec (.of P.field.k))]
  [IsSeparated (X ↘ Spec (.of P.field.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
  [QuasiCompact (Y ↘ Spec (.of P.field.k))]
  [IsSeparated (Y ↘ Spec (.of P.field.k))]
  (f : X ⟶ Y) [f.IsOver (Spec (.of P.field.k))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  (c : Compactification f)

section FiniteUnitTrace

attribute [local irreducible] levelSmoothExceptionalCounit sfIntrinsicDerivedEquivalence
  PurityFiniteSetting.smoothPurityExceptional PurityFiniteSetting.smoothPurityPullback

end FiniteUnitTrace

/-- Finite trace normalization, using the actual coefficient comparison and root projection.
Source: rational purity proof, reconstruction of the coefficient-unit orientation
(blueprint: def-pur-canonical-rational-purity-realization). -/
def IsNormalizedTrace (d : ℕ) [SmoothOfRelativeDimension d f]
    (t : (PurCompactSupport.image
        (PurCompactSupport.completed P.coefficients.l P.extension) c).obj
          (twist P X (X ↘ Spec (.of P.field.k)) d).obj ⟶
      (twist P Y (Y ↘ Spec (.of P.field.k)) 0).obj) : Prop :=
  ∀ n : ℕ,
    (PurCompactSupport.comparison (PurCompactSupport.reduction P.coefficients.l P.extension
        (n + 1) (Nat.succ_pos n)) c).app
          (twist P X (X ↘ Spec (.of P.field.k)) d).obj ≫
      (PurCompactSupport.image (PurCompactSupport.finite P.coefficients.l P.extension
        (n + 1) (Nat.succ_pos n)) c).map
          (AdicSmoothDualizing.twistReduction P X (X ↘ Spec (.of P.field.k)) n d) ≫
      finiteIntegration P f c n d =
    (pbcDerivedExtend (PurCompactSupport.projection P.coefficients.l P.extension
      (n + 1) (Nat.succ_pos n) Y)).map t ≫
        AdicSmoothDualizing.twistReduction P Y (Y ↘ Spec (.of P.field.k)) n 0

variable (S : ConstructibleExceptionalCoefficients.System P.coefficients.l P.coefficients.Qbar
  P.field P.coefficients.different (f := f))

/-- The specified constructible operation, retaining its actual adjunction.
Source: rational purity proof, exceptional pullback
(blueprint: def-pur-canonical-rational-purity-realization). -/
abbrev operation (s : ConstructibleExceptionalCoefficients.Stage.{u} P.coefficients.l) :=
  S.ring.operation c s

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- The coefficient-unit orientation's trace in ordinary compact-support coordinates.
Source: rational purity proof Step 1, trace transpose
(blueprint: def-pur-canonical-rational-purity-realization). -/
def orientationTrace (d : ℕ)
    (a : twist P X (X ↘ Spec (.of P.field.k)) d ≅
      (operation P f c S (ConstructibleExceptionalCoefficients.Stage.integral
        (l := P.coefficients.l) (AdicSmoothDualizing.fieldStage P))).G.obj
        (twist P Y (Y ↘ Spec (.of P.field.k)) 0)) :
    (PurCompactSupport.image (PurCompactSupport.completed P.coefficients.l P.extension) c).obj
      (twist P X (X ↘ Spec (.of P.field.k)) d).obj ⟶
        (twist P Y (Y ↘ Spec (.of P.field.k)) 0).obj :=
  (S.ring.left c (ConstructibleExceptionalCoefficients.RingStage.integral
      (l := P.coefficients.l) (AdicSmoothDualizing.fieldStage P))).inv.app
      (twist P X (X ↘ Spec (.of P.field.k)) d) ≫
    (finiteTorConstructibleIntegral P.coefficients.l P.extension Y).ι.map
      ((operation P f c S (ConstructibleExceptionalCoefficients.Stage.integral
        (l := P.coefficients.l) (AdicSmoothDualizing.fieldStage P))).F.map a.hom ≫
        (operation P f c S (ConstructibleExceptionalCoefficients.Stage.integral
        (l := P.coefficients.l) (AdicSmoothDualizing.fieldStage P))).adjunction.counit.app
          (twist P Y (Y ↘ Spec (.of P.field.k)) 0))

/-- The unit orientation is uniquely fixed by the finite diagonal traces.
This uniqueness is only for a shifted rank-one line, not for arbitrary derived lifts.
Source: rational purity proof Step 1; finite diagonal orientation
(blueprint: def-pur-canonical-rational-purity-realization).
Proof: adic reconstruction of the finite unit-object purity gives the orientation.
Its counit reductions are precisely finiteIntegration by scalar compatibility.
If two orientations have these traces, transpose under the specified adjunction and
use either orientation to identify their quotient with an endomorphism of the shifted
completed line. This is an ordinary degree-zero line endomorphism. Its projections
to every finite quotient vanish, so it vanishes, since completed coefficients are the
inverse limit of those quotients. This proves uniqueness without a phantom-map claim. -/
theorem orientation_existsUnique (d : ℕ) [SmoothOfRelativeDimension d f] :
    ∃! a : twist P X (X ↘ Spec (.of P.field.k)) d ≅
        (operation P f c S (ConstructibleExceptionalCoefficients.Stage.integral
        (l := P.coefficients.l) (AdicSmoothDualizing.fieldStage P))).G.obj
          (twist P Y (Y ↘ Spec (.of P.field.k)) 0),
      IsNormalizedTrace P f c d (orientationTrace P f c S d a) := by
  sorry

/-- The unique finite-trace-normalized unit orientation.
Source: rational purity proof Step 1
(blueprint: def-pur-canonical-rational-purity-realization). -/
def orientation (d : ℕ) [SmoothOfRelativeDimension d f] :
    twist P X (X ↘ Spec (.of P.field.k)) d ≅
      (operation P f c S (ConstructibleExceptionalCoefficients.Stage.integral
        (l := P.coefficients.l) (AdicSmoothDualizing.fieldStage P))).G.obj
        (twist P Y (Y ↘ Spec (.of P.field.k)) 0) :=
  (orientation_existsUnique P f c S d).exists.choose

/-- Smooth completed-to-ordinary pullback on a good finite-Tor representative.
Source: rational purity proof, integral source
(blueprint: def-pur-canonical-rational-purity-realization). -/
@[irreducible]
def smoothPullToOrdinaryOnGood (d : ℕ) [SmoothOfRelativeDimension d f]
    (C : CochainComplex (integralTowerModules P.coefficients.l P.extension Y) ℤ)
    (hC : integralOperationsGoodComplex P.coefficients.l P.extension Y C)
    (hK : finiteTorConstructibleIntegral P.coefficients.l P.extension Y
      (DerivedCategory.Q.obj C)) :
    (integralDerivedPullback P.coefficients.l P.extension f).obj (DerivedCategory.Q.obj C) ≅
      (PurCompactSupport.pull (PurCompactSupport.completed P.coefficients.l P.extension)
        f).obj (DerivedCategory.Q.obj C) :=
  (integralDerivedPullbackComparison P.coefficients.l P.extension f).app ⟨C,hC⟩ ≪≫
    (@asIso _ _ _ _ (DerivedCategory.Q.map
      ((FrobeniusCoefficientTwists.pullbackAugmentation
        P.coefficients.l P.extension f).app C))
      (smoothPullAugmentation_isIso P.coefficients.l P.extension f C hC hK)).symm ≪≫
    ((FrobeniusCoefficientTwists.modulePull
      P.coefficients.l P.extension f).mapDerivedCategoryFactors.app C).symm

/-- The smooth comparison is fixed on every representative and every presentation map.
Source: rational purity proof, integral source
(blueprint: def-pur-canonical-rational-purity-realization).
Proof: use good K-flat resolutions. The normalized strict augmentation is natural,
so its descent is independent of resolution and of the isomorphism presenting K.
Every K has a resolution, which also proves uniqueness. -/
theorem smoothPullToOrdinary_existsUnique (d : ℕ) [SmoothOfRelativeDimension d f]
    (K : finiteTorConstructibleIntegralCategory P.coefficients.l P.extension Y) :
    ∃! e : (integralDerivedPullback P.coefficients.l P.extension f).obj K.obj ≅
        (PurCompactSupport.pull (PurCompactSupport.completed P.coefficients.l P.extension)
          f).obj K.obj,
      ∀ (C : CochainComplex (integralTowerModules P.coefficients.l P.extension Y) ℤ)
        (hC : integralOperationsGoodComplex P.coefficients.l P.extension Y C)
        (hK : finiteTorConstructibleIntegral P.coefficients.l P.extension Y
          (DerivedCategory.Q.obj C)) (a : DerivedCategory.Q.obj C ≅ K.obj),
        e = (integralDerivedPullback P.coefficients.l P.extension f).mapIso a.symm ≪≫
          smoothPullToOrdinaryOnGood P f d C hC hK ≪≫
          (PurCompactSupport.pull (PurCompactSupport.completed P.coefficients.l P.extension)
            f).mapIso a := by
  let G := integralOperationsGoodComplex P.coefficients.l P.extension Y
  let L := integralOperationsGoodLocalization P.coefficients.l P.extension Y
  let V := (HomologicalComplex.quasiIso
    (integralTowerModules P.coefficients.l P.extension Y) (.up ℤ)).inverseImage G.ι
  have : L.IsLocalization V :=
    integralOperationsGoodLocalization_isLocalization P.coefficients.l P.extension Y
  let r := Functor.isoWhiskerLeft G.ι
    (FrobeniusCoefficientTwists.modulePull P.coefficients.l P.extension f).mapDerivedCategoryFactors
  let α := Functor.whiskerLeft G.ι (Functor.whiskerRight
    (FrobeniusCoefficientTwists.pullbackAugmentation P.coefficients.l P.extension f)
    DerivedCategory.Q)
  obtain ⟨e, he, hu⟩ := normalized_descent_comparison L V r.symm
    (integralDerivedPullbackComparison P.coefficients.l P.extension f) α K.obj
    (fun C ↦ finiteTorConstructibleIntegral P.coefficients.l P.extension Y
      (DerivedCategory.Q.obj C.obj))
    (fun C a ↦ finiteTor_of_iso P.coefficients.l P.extension Y a.symm K.property)
    (fun C hC ↦ smoothPullToOrdinaryOnGood P f d C.obj C.property hC)
    (fun C hC ↦ by
      obtain ⟨C, hC'⟩ := C
      unfold smoothPullToOrdinaryOnGood
      rw [Iso.trans_inv, Iso.trans_inv, Category.assoc]
      with_unfolding_all rfl)
  refine ⟨e, ?_, ?_⟩
  · intro C hC hK a
    exact he ⟨C, hC⟩ hK a
  · intro e' he'
    exact hu e' (fun C hC a ↦ he' C.obj C.property hC a)

/-- The specified smooth completed-to-ordinary comparison.
Source: rational purity proof, integral source
(blueprint: def-pur-canonical-rational-purity-realization). -/
def smoothPullToOrdinary (d : ℕ) [SmoothOfRelativeDimension d f]
    (K : finiteTorConstructibleIntegralCategory P.coefficients.l P.extension Y) :=
  (smoothPullToOrdinary_existsUnique P f d K).exists.choose

/-- Completed pullback preserves the finite-Tor constructible domain here.
Source: rational purity proof, bounded integral representatives
(blueprint: def-pur-canonical-rational-purity-realization).
Proof: integral pullback preserves the constructible complete category. Its actual
reductions are finite pullbacks of the reductions of K and retain their one Tor
interval. Thus the result has the required complete membership and uniform bounds. -/
theorem pullFiniteTor (d : ℕ) [SmoothOfRelativeDimension d f]
    (K : finiteTorConstructibleIntegralCategory P.coefficients.l P.extension Y) :
    finiteTorConstructibleIntegral P.coefficients.l P.extension X
      ((integralDerivedPullback P.coefficients.l P.extension f).obj K.obj) := by
  classical
  let (x : X) : Invertible (P.coefficients.l : X.residueField x) :=
    (show IsUnit (P.coefficients.l : X.residueField x) by
      simpa only [map_natCast] using
        (P.coefficientPrime_isUnit_stalk X (X ↘ Spec (.of P.field.k)) x).map
          (X.residue x).hom).invertible
  let (y : Y) : Invertible (P.coefficients.l : Y.residueField y) :=
    (show IsUnit (P.coefficients.l : Y.residueField y) by
      simpa only [map_natCast] using
        (P.coefficientPrime_isUnit_stalk Y (Y ↘ Spec (.of P.field.k)) y).map
          (Y.residue y).hom).invertible
  have hY := (integral_residue_tor P.field P.coefficients.l P.coefficients.different
    P.extension Y).2
  have hX := (integral_residue_tor P.field P.coefficients.l P.coefficients.different
    P.extension X).2
  rw [← hX]
  exact ((integralOperations_preserve_constructible P.coefficients.l P.extension f).1
    K.obj (by rw [hY]; exact K.property)).1

/-- The integral twisted pullback, with the even shift on the coefficient line.
This is canonically Lf*K(d)[2d] by the specified tensor symmetry and shift constraints.
Source: rational purity proof Step 1
(blueprint: def-pur-canonical-rational-purity-realization).
Proof: the coefficient line is complete constructible with uniform Tor interval [-2d,-2d].
Pullback of K has its original uniform interval. Completed tensor adds those intervals
and preserves constructibility. This proves finite-Tor membership of the displayed object. -/
theorem integralSource_mem (d : ℕ) [SmoothOfRelativeDimension d f]
    (K : finiteTorConstructibleIntegralCategory P.coefficients.l P.extension Y) :
    finiteTorConstructibleIntegral P.coefficients.l P.extension X
      ((integralCompletedTensor P.coefficients.l P.extension X).obj
        ((twist P X (X ↘ Spec (.of P.field.k)) d).obj,
          (integralDerivedPullback P.coefficients.l P.extension f).obj K.obj)) := by
  classical
  let (x : X) : Invertible (P.coefficients.l : X.residueField x) :=
    (show IsUnit (P.coefficients.l : X.residueField x) by
      simpa only [map_natCast] using
        (P.coefficientPrime_isUnit_stalk X (X ↘ Spec (.of P.field.k)) x).map
          (X.residue x).hom).invertible
  have hX := (integral_residue_tor P.field P.coefficients.l P.coefficients.different
    P.extension X).2
  apply (congrFun hX _).mp
  have hK := (congrFun hX _).mpr (pullFiniteTor P f d K)
  exact ((integralOperations_preserve_constructible P.coefficients.l P.extension (𝟙 X)).2
    X (Or.inl rfl) _ _ (twist P X (X ↘ Spec (.of P.field.k)) d).property.1 hK).1

/-- The integral source in the existing finite-Tor full subcategory.
Source: rational purity proof Step 1
(blueprint: def-pur-canonical-rational-purity-realization). -/
def integralSource (d : ℕ) [SmoothOfRelativeDimension d f]
    (K : finiteTorConstructibleIntegralCategory P.coefficients.l P.extension Y) :
    finiteTorConstructibleIntegralCategory P.coefficients.l P.extension X :=
  ⟨_,integralSource_mem P f d K⟩

attribute [local irreducible] smoothPullToOrdinary

/-- The canonical source comparison to the ordinary tensor used by projection.
Source: rational purity proof, trace-transpose source
(blueprint: def-pur-canonical-rational-purity-realization). -/
def ordinarySource (d : ℕ) [SmoothOfRelativeDimension d f]
    (K : finiteTorConstructibleIntegralCategory P.coefficients.l P.extension Y) :
    (integralSource P f d K).obj ≅
      (ordinaryModel P.coefficients.l P.extension X).tensor.obj
        ((twist P X (X ↘ Spec (.of P.field.k)) d).obj,
          (PurCompactSupport.pull (PurCompactSupport.completed P.coefficients.l P.extension)
            f).obj K.obj) :=
  tensorToOrdinary P.coefficients.l P.extension X
    (twist P X (X ↘ Spec (.of P.field.k)) d)
    ⟨_,pullFiniteTor P f d K⟩ ≪≫
    (ordinaryModel P.coefficients.l P.extension X).tensor.mapIso
      (Iso.prod (Iso.refl _) (smoothPullToOrdinary P f d K))

attribute [local irreducible] ordinarySource

attribute [local semireducible] PurCompactSupport.image in
/-- The actual proper/open projection transformation for the fixed compactification.
Source: rational purity proof, inverse projection in the trace transpose
(blueprint: def-pur-canonical-rational-purity-realization). -/
def projection (d : ℕ) (K : finiteTorConstructibleIntegralCategory
    P.coefficients.l P.extension Y) :
    (ordinaryModel P.coefficients.l P.extension Y).tensor.obj
      (((PurCompactSupport.image (PurCompactSupport.completed P.coefficients.l P.extension)
        c).obj (twist P X (X ↘ Spec (.of P.field.k)) d).obj), K.obj) ⟶
      (PurCompactSupport.image (PurCompactSupport.completed P.coefficients.l P.extension)
        c).obj ((ordinaryModel P.coefficients.l P.extension X).tensor.obj
          ((twist P X (X ↘ Spec (.of P.field.k)) d).obj,
            (PurCompactSupport.pull (PurCompactSupport.completed P.coefficients.l P.extension)
              f).obj K.obj)) :=
  ((PurCompactSupport.projectionMap
    (PurCompactSupport.completed P.coefficients.l P.extension) c
    (ordinaryModel P.coefficients.l P.extension X)
    (ordinaryModel P.coefficients.l P.extension c.Z)
    (ordinaryModel P.coefficients.l P.extension Y)
    (PurCompactSupport.completedPull_comp P.coefficients.l P.extension c.i c.g)).app
      (twist P X (X ↘ Spec (.of P.field.k)) d).obj).app K.obj

attribute [local semireducible] PurCompactSupport.image in
/-- Projection is invertible on the indicated constructible finite-Tor inputs.
The asserted map is the actual counit-first proper/open composite above.
Source: rational purity proof, projection formula
(blueprint: def-pur-canonical-rational-purity-realization).
Proof: finite coefficient projection is invertible for a bounded flat constructible
second input. Ordinary coefficient tensor agrees with completed tensor on this domain.
The normalized strict quotient-tower realization carries the finite projection and its
inverse to the displayed ordinary map and inverse. Proper and open comparisons retain
their original units and counits throughout, so this proves invertibility of this map. -/
theorem projection_isIso (d : ℕ) [SmoothOfRelativeDimension d f]
    (K : finiteTorConstructibleIntegralCategory P.coefficients.l P.extension Y) :
    IsIso (projection P f c d K) := by
  classical
  have : IsLocallyNoetherian X :=
    LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of P.field.k))
  have : IsLocallyNoetherian Y :=
    LocallyOfFiniteType.isLocallyNoetherian (Y ↘ Spec (.of P.field.k))
  have : CompactSpace X :=
    QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of P.field.k))
  have : CompactSpace Y :=
    QuasiCompact.compactSpace_of_compactSpace (Y ↘ Spec (.of P.field.k))
  have : IsNoetherian X := ⟨⟩
  have : IsNoetherian Y := ⟨⟩
  let (x : X) : Invertible (P.coefficients.l : X.residueField x) :=
    (SfProEtaleProjection.residue_unit P.coefficients.l P.field
      P.coefficients.different X x).invertible
  let (y : Y) : Invertible (P.coefficients.l : Y.residueField y) :=
    (SfProEtaleProjection.residue_unit P.coefficients.l P.field
      P.coefficients.different Y y).invertible
  let A : sfIntegralConstructibleCategory P.coefficients.l P.extension X :=
    ⟨(twist P X (X ↘ Spec (.of P.field.k)) d).obj,
      (twist P X (X ↘ Spec (.of P.field.k)) d).property.1⟩
  let B : sfIntegralConstructibleCategory P.coefficients.l P.extension Y :=
    ⟨K.obj, K.property.1⟩
  have support (M : sfIntegralConstructibleCategory P.coefficients.l P.extension X) :
      sfIntegralConstructible P.coefficients.l P.extension Y
        ((PurCompactSupport.image
          (PurCompactSupport.completed P.coefficients.l P.extension) c).obj M.obj) :=
    (sfIntegralConstructible P.coefficients.l P.extension Y).prop_of_iso
      ((sfQcqsCompactSupportRealization P.coefficients.l P.extension P.field.k
        (PurCompactSupport.coefficientPrimeUnit P.coefficients.l P.field
          P.coefficients.different) c).app M).symm
      ((sfCompactSupportFiniteIntegralFunctor P.coefficients.l P.field.k
        (PurCompactSupport.coefficientPrimeUnit P.coefficients.l P.field
          P.coefficients.different) c P.extension).obj M).property
  have hs := SfProEtaleProjection.tensor_domains P.coefficients.l P.extension Y
    (SfProEtaleProjection.scheme_unit P.coefficients.l P.field P.coefficients.different Y)
    (ordinaryModel P.coefficients.l P.extension Y) _ _ (support A) B.property
  have hp := SfProEtaleProjection.pull_domains P.coefficients.l P.extension f
    (SfProEtaleProjection.finite_dimension P.field X)
    (SfProEtaleProjection.finite_dimension P.field Y)
    (SfProEtaleProjection.scheme_unit P.coefficients.l P.field P.coefficients.different X)
    (SfProEtaleProjection.scheme_unit P.coefficients.l P.field P.coefficients.different Y)
    B.obj B.property
  have hi := SfProEtaleProjection.tensor_domains P.coefficients.l P.extension X
    (SfProEtaleProjection.scheme_unit P.coefficients.l P.field P.coefficients.different X)
    (ordinaryModel P.coefficients.l P.extension X) _ _ A.property hp
  exact sfIntegralReduction_conservative P.coefficients.l P.extension Y
    (projection P f c d K) hs.1 (support ⟨_, hi.1⟩)
    (integralOrdinaryProjection_finiteReductions P.field P.coefficients.l
      P.coefficients.different P.extension f c
      (ordinaryModel P.coefficients.l P.extension X)
      (ordinaryModel P.coefficients.l P.extension c.Z)
      (ordinaryModel P.coefficients.l P.extension Y) A B)

/-- The published ordinary closed structure, with its presentation kept abstract locally.
Source: rational purity proof Step 1, tensor-unit constraint
(blueprint: def-pur-canonical-rational-purity-realization). -/
def ordinaryClosed (T : Scheme.{u}) :=
  @RingedSiteDualityModel.closed.{u + 1, u, u, u + 2}
    _ _ _ (IntegralOnSlice.abSheafify.{u, u} T none)
    (IntegralOnSlice.abLocallyBijective.{u, u} T none) _ _
    (IntegralOnSlice.duality.{u, u} P.coefficients.l P.extension T none)

attribute [local irreducible] ordinaryClosed

attribute [local irreducible] ordinaryMonoidal

/-- The shifted zero-power line is the coefficient unit of the normalized ordinary tensor.
Source: rational purity proof, tensor-unit constraint
(blueprint: def-pur-canonical-rational-purity-realization). -/
def ordinaryCoefficientUnit (T : Scheme.{u}) (aT : T ⟶ Spec (.of P.field.k)) :
    (twist P T aT 0).obj ≅
      (ordinaryMonoidal P.coefficients.l P.extension T).tensorUnit := by
  unfold ordinaryMonoidal
  exact (shiftFunctorZero _ ℤ).app _ ≪≫
    (@RingedSiteDualityModel.unitIso.{u + 1, u, u, u + 2}
      _ _ _ (IntegralOnSlice.abSheafify.{u, u} T none)
      (IntegralOnSlice.abLocallyBijective.{u, u} T none) _ _
      (IntegralOnSlice.duality.{u, u} P.coefficients.l P.extension T none)).symm

/-- Equality of the published ordinary tensor and its closed monoidal presentation.
Source: rational purity proof Step 1, tensor-unit constraint
(blueprint: def-pur-canonical-rational-purity-realization). -/
theorem ordinaryTensor_eq (T : Scheme.{u}) :
    (ordinaryModel P.coefficients.l P.extension T).tensor =
      @MonoidalCategory.tensor _ _ (ordinaryMonoidal P.coefficients.l P.extension T) := by
  exact ordinaryMonoidal_tensor P.coefficients.l P.extension T

attribute [local irreducible] ordinaryCoefficientUnit CoefficientClosedStructure.tensor

/-- The ordinary tensor's coefficient left unitor, retaining its scalar normalization.
Source: rational purity proof, trace transpose
(blueprint: def-pur-canonical-rational-purity-realization). -/
def ordinaryLeftUnitor
    (K : DerivedCategory (integralTowerModules P.coefficients.l P.extension Y)) :
    (ordinaryModel P.coefficients.l P.extension Y).tensor.obj
      ((twist P Y (Y ↘ Spec (.of P.field.k)) 0).obj,K) ≅ K :=
by
  exact tensorLeftUnitorFromPresentation (ordinaryMonoidal P.coefficients.l P.extension Y)
    (ordinaryModel P.coefficients.l P.extension Y).tensor
    (ordinaryTensor_eq P Y) _ K
    (ordinaryCoefficientUnit P Y (Y ↘ Spec (.of P.field.k)))

section
attribute [local semireducible] PurCompactSupport.image
attribute [local irreducible] orientationTrace ordinaryLeftUnitor projection

/-- The actual trace/projection composite whose adjoint is smooth purity.
Source: rational purity proof Step 1, trace-transpose construction
(blueprint: def-pur-canonical-rational-purity-realization). -/
def integralTraceTransposeOfOrientation (d : ℕ) [SmoothOfRelativeDimension d f]
    (a : twist P X (X ↘ Spec (.of P.field.k)) d ≅
      (operation P f c S (ConstructibleExceptionalCoefficients.Stage.integral
        (l := P.coefficients.l) (AdicSmoothDualizing.fieldStage P))).G.obj
        (twist P Y (Y ↘ Spec (.of P.field.k)) 0))
    (K : finiteTorConstructibleIntegralCategory P.coefficients.l P.extension Y) :
    (operation P f c S (ConstructibleExceptionalCoefficients.Stage.integral
        (l := P.coefficients.l) (AdicSmoothDualizing.fieldStage P))).F.obj
      (integralSource P f d K) ⟶ K :=
  ObjectProperty.homMk
    ((S.ring.left c (ConstructibleExceptionalCoefficients.RingStage.integral
      (l := P.coefficients.l) (AdicSmoothDualizing.fieldStage P))).hom.app
        (integralSource P f d K) ≫
      (PurCompactSupport.image (PurCompactSupport.completed P.coefficients.l P.extension)
        c).map (ordinarySource P f d K).hom ≫
      (@asIso _ _ _ _ (projection P f c d K) (projection_isIso P f c d K)).inv ≫
      (ordinaryModel P.coefficients.l P.extension Y).tensor.map
        (Prod.mkHom (orientationTrace P f c S d a) (𝟙 K.obj)) ≫
      (ordinaryLeftUnitor P K.obj).hom)

end

attribute [local irreducible] integralTraceTransposeOfOrientation

/-- The fixed transpose uses the transported, finite-trace-normalized adic unit
orientation. Source: rational purity proof Step 1
(blueprint: def-pur-canonical-rational-purity-realization). -/
def integralTraceTranspose (d : ℕ) [SmoothOfRelativeDimension d f]
    (K : finiteTorConstructibleIntegralCategory P.coefficients.l P.extension Y) :=
  integralTraceTransposeOfOrientation P f c S d (orientation P f c S d) K

attribute [local irreducible] integralTraceTranspose

/-- Integral purity is the actual adjoint transpose of that fixed composite.
The only chosen orientation is uniquely determined on the coefficient unit.
Source: rational purity proof Step 1 and the trace-transpose convention
(blueprint: def-pur-canonical-rational-purity-realization). -/
def integralMap (d : ℕ) [SmoothOfRelativeDimension d f]
    (K : finiteTorConstructibleIntegralCategory P.coefficients.l P.extension Y) :
    integralSource P f d K ⟶
      (operation P f c S (ConstructibleExceptionalCoefficients.Stage.integral
        (l := P.coefficients.l) (AdicSmoothDualizing.fieldStage P))).G.obj K :=
  (operation P f c S (ConstructibleExceptionalCoefficients.Stage.integral
        (l := P.coefficients.l) (AdicSmoothDualizing.fieldStage P))).adjunction.homEquiv _ _
    (integralTraceTranspose P f c S d K)

attribute [local irreducible] integralMap

/-- The trace-transpose integral comparison is invertible.
Source: rational purity proof Step 1, transporting adic purity
(blueprint: def-pur-canonical-rational-purity-realization).
Proof: the finite diagonal orientations are compatible with reduction and yield the
normalized tower orientation. The finite tensor-counit transpose is exactly
smoothPurityMap, including its shift reassociation. Strict tower reconstruction
carries that map to integralMap, because all tensor, compactification, and coefficient
comparisons preserve their normalized units and counits. Each finite purity map is
invertible. Normalized reconstruction preserves its inverse, hence integralMap is
invertible. This uses the full trace transpose, not uniqueness of arbitrary lifts. -/
theorem integralMap_isIso (d : ℕ) [SmoothOfRelativeDimension d f]
    (K : finiteTorConstructibleIntegralCategory P.coefficients.l P.extension Y) :
    IsIso (integralMap P f c S d K) := by
  sorry

/-- The canonical integral purity isomorphism, with its map already constructed.
Source: rational purity proof Step 1
(blueprint: def-pur-canonical-rational-purity-realization). -/
def integralIso (d : ℕ) [SmoothOfRelativeDimension d f]
    (K : finiteTorConstructibleIntegralCategory P.coefficients.l P.extension Y) :
    integralSource P f d K ≅
      (operation P f c S (ConstructibleExceptionalCoefficients.Stage.integral
        (l := P.coefficients.l) (AdicSmoothDualizing.fieldStage P))).G.obj K :=
  @asIso _ _ _ _ (integralMap P f c S d K) (integralMap_isIso P f c S d K)

end RelativeOrientation

section Rational
variable (P : PurityFiniteSetting.{u}) {X Y : Scheme.{u}}
  [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
  [QuasiCompact (X ↘ Spec (.of P.field.k))]
  [IsSeparated (X ↘ Spec (.of P.field.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
  [QuasiCompact (Y ↘ Spec (.of P.field.k))]
  [IsSeparated (Y ↘ Spec (.of P.field.k))]
  [∀ x : X, Invertible (P.coefficients.l : X.residueField x)]
  [∀ y : Y, Invertible (P.coefficients.l : Y.residueField y)]
  (f : X ⟶ Y) [f.IsOver (Spec (.of P.field.k))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  (c : Compactification f)
  (S : ConstructibleExceptionalCoefficients.System P.coefficients.l P.coefficients.Qbar
    P.field P.coefficients.different (f := f))

/-- Every underlying integral representative is in the finite-Tor category.
There is no stable-lattice assumption on any rational arrow.
Source: rational purity proof Step 1; integral residue-Tor theorem
(blueprint: def-pur-canonical-rational-purity-realization).
Proof: an object of the scalar localization has an actual integral constructible
representative. integral_residue_tor identifies its object predicate with the
uniform finite-Tor constructible predicate, proving the asserted membership. -/
theorem representativeTor
    (K : sfRationalConstructibleCategory P.coefficients.l P.extension Y) :
    finiteTorConstructibleIntegral P.coefficients.l P.extension Y K.obj.obj := by
  apply (congrFun (integral_residue_tor P.field P.coefficients.l
    P.coefficients.different P.extension Y).2 _).mp
  exact K.obj.property

/-- The unchanged integral object presenting a rational object.
Source: rational purity proof Step 1
(blueprint: def-pur-canonical-rational-purity-realization). -/
def representative
    (K : sfRationalConstructibleCategory P.coefficients.l P.extension Y) :
    finiteTorConstructibleIntegralCategory P.coefficients.l P.extension Y :=
  ⟨K.obj.obj,representativeTor P K⟩

/-- Rationalization returns the original object, literally in the scalar localization.
Source: rational purity proof Step 1
(blueprint: def-pur-canonical-rational-purity-realization).
Proof: rationalization includes the integral full subcategory and changes only Hom
groups by scalar localization. Both objects therefore have the same integral
representative; their membership proofs are equal by proof irrelevance. -/
theorem representative_eq
    (K : sfRationalConstructibleCategory P.coefficients.l P.extension Y) :
    (ConstructibleExceptionalCoefficients.rationalization P.coefficients.l P.coefficients.Qbar
      (AdicSmoothDualizing.fieldStage P) Y).obj (representative P K) = K := by
  cases K
  rfl

/-- The rational tensor and pullback retain their integral object formulas.
The first input here is the localization of the *integrally* shifted line, so this
identity makes no claim that a rational shift by 2d is literally the integral shift.
Source: rational purity proof Step 1, localization of integral representatives
(blueprint: def-pur-canonical-rational-purity-realization).
Proof: use the recorded object clauses of rationalDerivedTensor and
rationalDerivedPullback. The nonnegative integral Tate line is the positive root
tensor power used by twist; inherited integral shifts retain the ambient shift.
The resulting ambient objects agree. Full-subcategory membership proofs agree by
proof irrelevance, yielding this object equality. -/
theorem rationalIntegralSource_eq (d : ℕ) [SmoothOfRelativeDimension d f]
    (K : sfRationalConstructibleCategory P.coefficients.l P.extension Y) :
    (rationalDerivedTensor P.coefficients.l P.extension X).obj
      ((sfRationalConstructibleLocalization P.coefficients.l P.extension X).obj
        ((sfIntegralTwistingCoefficient P.coefficients.l P.extension X (d : ℤ))⟦2*(d : ℤ)⟧),
        (rationalDerivedPullback P.coefficients.l P.extension f).obj K) =
      (ConstructibleExceptionalCoefficients.rationalization P.coefficients.l P.coefficients.Qbar
        (AdicSmoothDualizing.fieldStage P) X).obj
        (integralSource P f d (representative P K)) := by
  have hTensor : ∀ MN,
      (rationalDerivedTensor P.coefficients.l P.extension X).obj MN =
        ⟨(constructibleIntegralTensor P.coefficients.l P.extension X).obj
          (MN.1.obj, MN.2.obj)⟩ := by
    unfold rationalDerivedTensor
    exact (rationalDerivedTensor_existsUnique P.coefficients.l P.extension X).exists.choose_spec.1
  have hPull : (rationalDerivedPullback P.coefficients.l P.extension f).obj K =
      ⟨(constructibleIntegralPullback P.coefficients.l P.extension f).obj K.obj⟩ := by
    unfold rationalDerivedPullback
    exact (rationalDerivedPullback_existsUnique
      P.coefficients.l P.extension f).exists.choose_spec.2.1 K
  rw [hTensor, hPull]
  apply congrArg ScalarLocalization.mk
  apply ObjectProperty.FullSubcategory.ext
  change (integralCompletedTensor P.coefficients.l P.extension X).obj (_, _) =
    (integralCompletedTensor P.coefficients.l P.extension X).obj (_, _)
  congr 1
  change (((sfIntegralTwistingCoefficient P.coefficients.l P.extension X
      (d : ℤ))⟦2 * (d : ℤ)⟧).obj,
      (integralDerivedPullback P.coefficients.l P.extension f).obj K.obj.obj) =
    ((twist P X (X ↘ Spec (.of P.field.k)) d).obj,
      (integralDerivedPullback P.coefficients.l P.extension f).obj K.obj.obj)
  rw [fullSubcategory_shift_obj]
  unfold twist
  rfl

attribute [local irreducible] integralIso integralSource representative
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

/-- The source comparison uses the inverse localization commShiftIso at 2d,
followed by the unchanged integral tensor/pullback object formulas. The rational
shift is only normalized at one; its coherent comparison supplies all other shifts.
Source: rational purity proof Step 1
(blueprint: def-pur-canonical-rational-purity-realization). -/
def rationalSourceComparison (d : ℕ) [SmoothOfRelativeDimension d f]
    (K : sfRationalConstructibleCategory P.coefficients.l P.extension Y) :
    (rationalSource P.coefficients.l P.extension f d).obj K ≅
      (ConstructibleExceptionalCoefficients.rationalization P.coefficients.l P.coefficients.Qbar
        (AdicSmoothDualizing.fieldStage P) X).obj
        (integralSource P f d (representative P K)) :=
by
  unfold rationalSource
  exact
    (rationalDerivedTensor P.coefficients.l P.extension X).mapIso
      (Iso.prod
        (((sfRationalConstructibleLocalization P.coefficients.l P.extension X).commShiftIso
          (2*(d : ℤ))).symm.app
            (sfIntegralTwistingCoefficient P.coefficients.l P.extension X (d : ℤ)))
        (Iso.refl _)) ≪≫ eqToIso (rationalIntegralSource_eq P f d K)

attribute [local irreducible] rationalSourceComparison

/-- The canonical rational purity isomorphism: rationalize the constructed integral
trace transpose, then use the specified counit-preserving exceptional comparison.
Source: rational purity proof Step 1
(blueprint: def-pur-canonical-rational-purity-realization). -/
def rationalIso (d : ℕ) [SmoothOfRelativeDimension d f]
    (K : sfRationalConstructibleCategory P.coefficients.l P.extension Y) :
    (rationalSource P.coefficients.l P.extension f d).obj K ≅
      (operation P f c S (ConstructibleExceptionalCoefficients.Stage.rational
        (l := P.coefficients.l)
        (AdicSmoothDualizing.fieldStage P))).G.obj K :=
by
  refine rationalSourceComparison P f d K ≪≫ ?_
  refine (ConstructibleExceptionalCoefficients.rationalization
    P.coefficients.l P.coefficients.Qbar (AdicSmoothDualizing.fieldStage P) X).mapIso
      (integralIso P f c S d (representative P K)) ≪≫ ?_
  refine (S.fields.rationalizationComparison c (AdicSmoothDualizing.fieldStage P)).b.app
    (representative P K) ≪≫ ?_
  exact (operation P f c S (ConstructibleExceptionalCoefficients.Stage.rational
    (l := P.coefficients.l) (AdicSmoothDualizing.fieldStage P))).G.mapIso
      (eqToIso (representative_eq P K))

attribute [local irreducible] rationalIso

end Rational

section CommonPurity
attribute [local instance 2000] IntermediateField.algebra'
attribute [local instance 0] ConstructibleExceptionalCoefficients.category

open AlgebraicallyClosedCoefficients GeneralAlgebraicallyClosedCoefficients
variable (P : PurityFiniteSetting.{u})

/-- Cache the published field structure on the small coefficient model.
Source: rational purity proof Step 2, coefficient size transport
(blueprint: def-pur-canonical-rational-purity-realization). -/
local instance commonModelField (i : Index P.coefficients.l P.coefficients.Qbar) :
    Field (Coefficient.{u} P.coefficients.l P.coefficients.Qbar i) :=
  (ConstructibleExceptionalCoefficients.commonField P.coefficients.l P.coefficients.Qbar
    i).field

/-- Cache the published algebra structure on the small coefficient model.
Source: rational purity proof Step 2, coefficient size transport
(blueprint: def-pur-canonical-rational-purity-realization). -/
local instance commonModelAlgebra (i : Index P.coefficients.l P.coefficients.Qbar) :
    Algebra (Padic P.coefficients.l)
    (Coefficient.{u} P.coefficients.l P.coefficients.Qbar
      i) :=
  (ConstructibleExceptionalCoefficients.commonField P.coefficients.l P.coefficients.Qbar
    i).algebra

/-- Cache the finite-dimensionality of the published small coefficient model.
Source: rational purity proof Step 2, coefficient size transport
(blueprint: def-pur-canonical-rational-purity-realization). -/
local instance commonModelFinite (i : Index P.coefficients.l P.coefficients.Qbar) :
    FiniteDimensional (Padic P.coefficients.l)
    (Coefficient.{u} P.coefficients.l P.coefficients.Qbar
      i) :=
  (ConstructibleExceptionalCoefficients.commonField P.coefficients.l P.coefficients.Qbar
    i).finite

/-- The fixed purity datum at an arbitrary finite subfield; only the coefficient field changes.
Source: rational purity proof Step 2
(blueprint: def-pur-canonical-rational-purity-realization). -/
abbrev stageSetting (L : Index P.coefficients.l P.coefficients.Qbar) : PurityFiniteSetting.{u} :=
  { P with extension := L.val, finiteExtension := L.property }

/-- The inverse of the published small-model algebra equivalence.
Source: rational purity proof Step 2, coefficient size transport
(blueprint: def-pur-canonical-rational-purity-realization). -/
def modelInverse : Coefficient.{u} P.coefficients.l P.coefficients.Qbar
    (AdicSmoothDualizing.fieldIndex P) →ₐ[Padic P.coefficients.l] P.extension :=
  (Shrink.algEquiv (Padic P.coefficients.l) P.extension).toAlgHom

/-- Scalar transport from the small model back to the given finite coefficient field.
Source: rational purity proof Step 2
(blueprint: def-pur-canonical-rational-purity-realization). -/
def modelBack (T : Scheme.{u}) :
    sfRationalConstructibleCategory P.coefficients.l
      (Coefficient.{u} P.coefficients.l P.coefficients.Qbar
        (AdicSmoothDualizing.fieldIndex P)) T ⥤
      sfRationalConstructibleCategory P.coefficients.l P.extension T :=
  sfRationalScalarExtension P.coefficients.l
    (Coefficient.{u} P.coefficients.l P.coefficients.Qbar
      (AdicSmoothDualizing.fieldIndex P)) T 0
      (Fact.out : P.coefficients.l.Prime).ne_zero P.extension (modelInverse P)

/-- The two actual algebra equivalences compose to the identity.
Source: rational purity proof Step 2, small-model identity
(blueprint: def-pur-canonical-rational-purity-realization).
Proof: apply the left inverse identity of Shrink.algEquiv pointwise. AlgHom
extensionality gives exactly the identity of algebra homomorphisms. -/
theorem modelComposite :
    (AdicSmoothDualizing.modelEmbedding P).comp (modelInverse P) =
      AlgHom.id (Padic P.coefficients.l)
        (Coefficient.{u} P.coefficients.l P.coefficients.Qbar
          (AdicSmoothDualizing.fieldIndex P)) := by
  apply AlgHom.ext
  intro x
  change (AdicSmoothDualizing.modelEmbedding P) (modelInverse P x) = x
  exact (Shrink.algEquiv (Padic P.coefficients.l) P.extension).symm_apply_apply x

/-- The canonical round trip is balanced scalar associativity followed by the unit.
Source: rational purity proof Step 2, small-model transport
(blueprint: def-pur-canonical-rational-purity-realization). -/
def modelRoundtrip (T : Scheme.{u}) :
    modelBack P T ⋙ AdicSmoothDualizing.modelScalar P T ≅
      𝟭 (sfRationalConstructibleCategory P.coefficients.l
        (Coefficient.{u} P.coefficients.l P.coefficients.Qbar
          (AdicSmoothDualizing.fieldIndex P)) T) :=
  scalarAssociator P.coefficients.l
    (Coefficient.{u} P.coefficients.l P.coefficients.Qbar
      (AdicSmoothDualizing.fieldIndex P)) P.extension
    (Coefficient.{u} P.coefficients.l P.coefficients.Qbar
      (AdicSmoothDualizing.fieldIndex P))
    (modelInverse P) (AdicSmoothDualizing.modelEmbedding P)
    (AlgHom.id (Padic P.coefficients.l) _) (modelComposite P) T ≪≫
    sfRationalScalarUnit P.coefficients.l
      (Coefficient.{u} P.coefficients.l P.coefficients.Qbar
        (AdicSmoothDualizing.fieldIndex P)) T 0
        (Fact.out : P.coefficients.l.Prime).ne_zero

variable {X Y : Scheme.{u}}
  [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
  [QuasiCompact (X ↘ Spec (.of P.field.k))]
  [IsSeparated (X ↘ Spec (.of P.field.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
  [QuasiCompact (Y ↘ Spec (.of P.field.k))]
  [IsSeparated (Y ↘ Spec (.of P.field.k))]
  [∀ x : X, Invertible (P.coefficients.l : X.residueField x)]
  [∀ y : Y, Invertible (P.coefficients.l : Y.residueField y)]
  (f : X ⟶ Y) [f.IsOver (Spec (.of P.field.k))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  (c : Compactification f)
  (S : ConstructibleExceptionalCoefficients.System P.coefficients.l P.coefficients.Qbar
    P.field P.coefficients.different (f := f))

attribute [local irreducible] sourceScalar modelRoundtrip
  AdicSmoothDualizing.modelEmbedding

/-- Rational purity in the actual small coefficient model, transported through the
specified algebra equivalence and counit-preserving exceptional comparison.
Source: rational purity proof Step 2
(blueprint: def-pur-canonical-rational-purity-realization). -/
def smallModelIso (d : ℕ) [SmoothOfRelativeDimension d f]
    (K : sfRationalConstructibleCategory P.coefficients.l
      (Coefficient.{u} P.coefficients.l P.coefficients.Qbar
        (AdicSmoothDualizing.fieldIndex P)) Y) :
    (rationalSource P.coefficients.l
      (Coefficient.{u} P.coefficients.l P.coefficients.Qbar
        (AdicSmoothDualizing.fieldIndex P)) f d).obj K ≅
    (S.ring.operation c (ConstructibleExceptionalCoefficients.Stage.rational (l := P.coefficients.l)
      (ConstructibleExceptionalCoefficients.commonField P.coefficients.l P.coefficients.Qbar
        (AdicSmoothDualizing.fieldIndex P)))).G.obj K :=
  (rationalSource P.coefficients.l
    (Coefficient.{u} P.coefficients.l P.coefficients.Qbar
      (AdicSmoothDualizing.fieldIndex P)) f d).mapIso ((modelRoundtrip P Y).app K).symm ≪≫
    (sourceScalar P.coefficients.l P.extension
      (Coefficient.{u} P.coefficients.l P.coefficients.Qbar
        (AdicSmoothDualizing.fieldIndex P)) (AdicSmoothDualizing.modelEmbedding P)
      f d ((modelBack P Y).obj K)).symm ≪≫
    (AdicSmoothDualizing.modelScalar P X).mapIso
      (rationalIso P f c S d ((modelBack P Y).obj K)) ≪≫
    (S.fields.rationalComparison c (AdicSmoothDualizing.fieldStage P)
      (ConstructibleExceptionalCoefficients.commonField P.coefficients.l P.coefficients.Qbar
        (AdicSmoothDualizing.fieldIndex P)) (AdicSmoothDualizing.modelEmbedding P)).b.app
          ((modelBack P Y).obj K) ≪≫
    (S.ring.operation c (ConstructibleExceptionalCoefficients.Stage.rational (l := P.coefficients.l)
      (ConstructibleExceptionalCoefficients.commonField P.coefficients.l P.coefficients.Qbar
        (AdicSmoothDualizing.fieldIndex P)))).G.mapIso ((modelRoundtrip P Y).app K)

attribute [local irreducible] smallModelIso

/-- The two published rational-stage category instances agree.
Source: rational purity proof Step 2, coefficient size transport
(blueprint: def-pur-canonical-rational-purity-realization). -/
theorem commonCategory_eq (T : Scheme.{u})
    (i : Index P.coefficients.l P.coefficients.Qbar) :
    ConstructibleExceptionalCoefficients.category P.coefficients.l
      P.coefficients.Qbar T (.rational (ConstructibleExceptionalCoefficients.commonField
        P.coefficients.l P.coefficients.Qbar i)) =
      GeneralAlgebraicallyClosedCoefficients.stageCategory
        P.coefficients.l P.coefficients.Qbar T i := by
  unfold ConstructibleExceptionalCoefficients.category
    GeneralAlgebraicallyClosedCoefficients.stageCategory
  rfl

/-- Transport an isomorphism along equality of the inherited category structures.
Source: rational purity proof Step 2, coefficient size transport
(blueprint: def-pur-canonical-rational-purity-realization). -/
def transportIsoCategory {C : Type (u + 2)} (cat cat' : Category.{u + 2} C)
    (h : cat = cat') {A B : C} (e : @Iso C cat A B) : @Iso C cat' A B := h ▸ e

/-- The canonical common-stage purity family. Each object is treated at its literal
finite stage, transported by its actual field-model equivalence, then included with the
specified exceptional coefficient comparison.
Source: rational purity proof Step 2
(blueprint: def-pur-canonical-rational-purity-realization). -/
def commonIso (d : ℕ) [SmoothOfRelativeDimension d f]
    (K : generalAlgebraicallyClosedConstructibleCategory P.coefficients.l
      P.coefficients.Qbar Y) :
    (commonSource P.coefficients.l P.coefficients.Qbar f d).obj K ≅
      (S.ring.operation c .closed).G.obj K :=
by
  have e := smallModelIso (stageSetting P K.stage) f c S d K.obj
  dsimp only [stageSetting, AdicSmoothDualizing.fieldIndex,
    commonModelField, commonModelAlgebra, commonModelFinite] at e
  have e' := transportIsoCategory _ _ (commonCategory_eq P X K.stage) e
  refine commonSourceComparison P.coefficients.l P.coefficients.Qbar f d K ≪≫ ?_
  refine (GeneralAlgebraicallyClosedCoefficients.inclusion
    (l := P.coefficients.l) (Ω := P.coefficients.Qbar) (Y := X) K.stage).mapIso e' ≪≫ ?_
  exact (S.common.commonComparison c K.stage).b.app K.obj

attribute [local irreducible] ScalarLocalization.category

attribute [-instance] commonModelField commonModelAlgebra commonModelFinite
attribute [local instance 1000] IntermediateField.algebra'
attribute [local instance 0] ConstructibleExceptionalCoefficients.category
attribute [local irreducible] AlgebraicGeometry.Scheme.ProEt
  AlgebraicGeometry.Scheme.instCategoryProEt AlgebraicGeometry.Scheme.ProEt.precoverage
  SheafOfModules.instAbelian SheafOfModules.instCategory scalarReductionSourceDerived

end CommonPurity

end RationalSmoothPurityCanonical

end WeilConjectures
