/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NU
-/
module

public import Sheaf.AlgebraicGeometry.VectorBundleZeroSection
public import Sheaf.AlgebraicGeometry.CartierKummerMap
public import Sheaf.AlgebraicGeometry.OrdinarySupportedCartierKummer
public import Sheaf.Paper.SectionCompactSourceExchange
public import Sheaf.Paper.AmbTateRootProjectionReduction
public import Sheaf.Paper.FiniteTorAmplitudeSites
public import Sheaf.Paper.IntrinsicFiniteTorsionConstructibility

/-! # Field realization of the supported Kummer class of a line bundle

Source: blueprint main-20261015, sec-smooth-purity/sk-prop-an,
thm-pur-rank-one-thom.proof.md, Steps 1--3
(blueprint: lem-pur-line-kummer-field-realization).

The index n denotes the positive coefficient exponent n+1, also in the root
exponent l^(n+1). All coefficients use the published fixed-scalar realization.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
universe u v w
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.LineKummerField
open Scheme

/-- Canonical inclusion comparison for a shifted degree-zero sheaf.
Source: Mathlib DerivedCategory.Plus.singleFunctorιIso and shift compatibility;
blueprint rank-one Thom proof, Step 2
(blueprint: lem-pur-line-kummer-field-realization). -/
@[irreducible]
def singleShiftInclusion {C : Type v} [Category.{w} C] [Abelian C]
    [HasDerivedCategory C] (M : C) :
    DerivedCategory.Plus.ι.obj
      (((DerivedCategory.Plus.singleFunctor C 0).obj M)⟦(2 : ℤ)⟧) ≅
        ((DerivedCategory.singleFunctor C 0).obj M)⟦(2 : ℤ)⟧ :=
  (DerivedCategory.Plus.ι.commShiftIso (2 : ℤ)).app _ ≪≫
    (shiftFunctor _ (2 : ℤ)).mapIso ((DerivedCategory.Plus.singleFunctorιIso C 0).app M)

/-- Degree-two Ext realization in the full bounded-below subcategory.
Source: Mathlib Ext.homEquiv and DerivedCategory.Plus.singleFunctorιIso
(blueprint: lem-pur-line-kummer-field-realization). -/
@[irreducible]
def extPlusMap {C : Type v} [Category.{w} C] [Abelian C] [HasDerivedCategory C]
    [HasExt.{w} C] {M N : C} (κ : Ext M N 2) :
    (DerivedCategory.Plus.singleFunctor C 0).obj M ⟶
      ((DerivedCategory.Plus.singleFunctor C 0).obj N)⟦(2 : ℤ)⟧ :=
  DerivedCategory.Plus.ι.preimage
    ((DerivedCategory.Plus.singleFunctorιIso C 0).hom.app M ≫ κ.hom ≫
      (singleShiftInclusion N).inv)

variable (l : ℕ) [Fact l.Prime] (F : Type u) [Field F]
  [Algebra (Padic l) F] [FiniteDimensional (Padic l) F] (n : ℕ)

/-- The ordinary etale tensor representative, in degree zero.
Source: blueprint rank-one Thom proof, Step 2
(blueprint: lem-pur-line-kummer-field-realization). -/
def etaleLine (hA : ((l ^ (n + 1) : ℕ) : finiteTateCoefficient l F n) = 0)
    (T : Scheme.{u}) :
    DerivedCategory.Plus (Sheaf T.smallEtaleTopology
      (ModuleCat.{u + 1} (finiteTateCoefficient l F n))) :=
  (DerivedCategory.Plus.singleFunctor _ 0).obj
    (finiteEtaleTateLine T (l ^ (n + 1)) (finiteTateCoefficient l F n) hA)

/-- The prescribed pro-etale twist, in degree zero; no new Tate object is chosen.
Source: blueprint rank-one Thom proof, Step 2
(blueprint: lem-pur-line-kummer-field-realization). -/
def proLine (T : Scheme.{u}) :
    DerivedCategory.Plus (Sheaf (Scheme.ProEt.topology T)
      (ModuleCat.{u + 1} (finiteTateCoefficient l F n))) :=
  (DerivedCategory.Plus.singleFunctor _ 0).obj (finiteTateProSheaf l F n T 1)

/-- The ordinary supported class from the uniquely boundary-normalized Kummer family.
Source: Stacks 03PL, 0A45; blueprint rank-one Thom proof, Step 2
(blueprint: lem-pur-line-kummer-field-realization). -/
@[irreducible]
def etaleClass
    (hA : ((l ^ (n + 1) : ℕ) : finiteTateCoefficient l F n) = 0)
    {D T : Scheme.{u}} (i : D ⟶ T) [IsClosedImmersion i]
    (hI : i.ker.IsInvertible) (hT : IsUnit (l : Γ(T, ⊤))) :
    SectionCompactSource.etaleSupported (finiteTateCoefficient l F n) i ⟶
      (etaleLine l F n hA T)⟦(2 : ℤ)⟧ :=
  by
    exact extPlusMap
      ((Etale.cartier_kummer_map l F).2.exists.choose.1 n n hA i hI hT)

/-- The prescribed pro-etale class, restricted through the fully faithful D+ inclusion.
Source: blueprint rank-one Thom proof, Step 2
(blueprint: lem-pur-line-kummer-field-realization). -/
@[irreducible]
def proClass {D T : Scheme.{u}} (i : D ⟶ T) [IsClosedImmersion i]
    (hI : i.ker.IsInvertible) (hT : IsUnit (l : Γ(T, ⊤))) :
    SectionCompactSource.proSupported (finiteTateCoefficient l F n) i ⟶
      (proLine l F n T)⟦(2 : ℤ)⟧ :=
  by
    let κ := (Etale.cartier_kummer_map l F).2.exists.choose.2 n i hI hT
    unfold Etale.cartierSupported at κ
    exact extPlusMap κ

/-- The specified root-projection comparison, on shifted degree-zero objects.
Source: blueprint rank-one Thom proof, Step 2
(blueprint: lem-pur-line-kummer-field-realization). -/
@[irreducible]
def shiftedComparison
    (hA : ((l ^ (n + 1) : ℕ) : finiteTateCoefficient l F n) = 0)
    (T : Scheme.{u})
    (q : (ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} (finiteTateCoefficient l F n)) T).obj
        (finiteEtaleTateLine T (l ^ (n + 1)) (finiteTateCoefficient l F n) hA) ≅
          finiteTateProSheaf l F n T 1) :
    (ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} (finiteTateCoefficient l F n)) T).mapDerivedCategoryPlus.obj
        ((etaleLine l F n hA T)⟦(2 : ℤ)⟧) ≅ (proLine l F n T)⟦(2 : ℤ)⟧ :=
  ((ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} (finiteTateCoefficient l F n)) T).mapDerivedCategoryPlus.commShiftIso
        (2 : ℤ)).app _ ≪≫
    (shiftFunctor _ (2 : ℤ)).mapIso
      ((Functor.mapDerivedCategoryPlusSingleFunctor
        (ProEtale.comparisonUpperStar
          (ModuleCat.{u + 1} (finiteTateCoefficient l F n)) T) 0).app _ ≪≫
        (DerivedCategory.Plus.singleFunctor _ 0).mapIso q)

end AlgebraicGeometry.LineKummerField

namespace AlgebraicGeometry.LineKummerField
open Scheme

/-- The published zero section is closed, with its existing proof.
Source: VectorBundleZeroSection.zero_spec, Stacks 01M2
(blueprint: lem-pur-line-kummer-field-realization). -/
instance zeroClosed (B : Scheme.{u}) [IsNoetherian B] (V : B.Modules)
    [V.IsFiniteLocallyFreeOfRank 1] :
    IsClosedImmersion (VectorBundleZeroSection.zero B 1 V) :=
  (VectorBundleZeroSection.zero_spec B 1 V).2

variable (l : ℕ) [Fact l.Prime] (F : Type u) [Field F]
  [Algebra (Padic l) F] [FiniteDimensional (Padic l) F] (n : ℕ)

/-- Finiteness of the published lifted positive coefficient quotient.
Source: Padic.finite_coefficientExtensionRing, positive finite coefficient levels
(blueprint: lem-pur-line-kummer-field-realization). -/
instance coefficientFinite : Finite (finiteTateCoefficient l F n) :=
  Equiv.ulift.finite_iff.mpr
    (Padic.finite_coefficientExtensionRing l F (n + 1) (Nat.le_add_left 1 n))

/-- Compact image of the ordinary supported class with the prescribed etale source.
Source: blueprint rank-one Thom proof, Steps 1--2
(blueprint: lem-pur-line-kummer-field-realization). -/
@[irreducible]
def etaleTau
    (hA : ((l ^ (n + 1) : ℕ) : finiteTateCoefficient l F n) = 0)
    {B X : Scheme.{u}} {π : X ⟶ B} (c : Compactification π)
    (z : B ⟶ X) [IsClosedImmersion z] (hz : z ≫ π = 𝟙 B)
    (hI : z.ker.IsInvertible) (hX : IsUnit (l : Γ(X, ⊤))) :
    SectionCompactSource.etaleConstant (finiteTateCoefficient l F n) B ⟶
      (Etale.rightDerivedLowerShriekOfCompactificationPlus
        (ModuleCat.{u + 1} (finiteTateCoefficient l F n)) c).obj
          ((etaleLine l F n hA X)⟦(2 : ℤ)⟧) :=
  (SectionCompactSource.etaleSource (finiteTateCoefficient l F n) c z hz).hom ≫
    (Etale.rightDerivedLowerShriekOfCompactificationPlus
      (ModuleCat.{u + 1} (finiteTateCoefficient l F n)) c).map
        (etaleClass l F n hA z hI hX)

/-- Compact image of the prescribed pro-etale supported class with normalized source.
Source: blueprint rank-one Thom proof, Steps 1--2
(blueprint: lem-pur-line-kummer-field-realization). -/
@[irreducible]
def proTau {B X : Scheme.{u}} {π : X ⟶ B} (c : Compactification π)
    (z : B ⟶ X) [IsClosedImmersion z] (hz : z ≫ π = 𝟙 B)
    (hI : z.ker.IsInvertible) (hX : IsUnit (l : Γ(X, ⊤))) :
    SectionCompactSource.proConstant (finiteTateCoefficient l F n) B ⟶
      (ProEtale.rightDerivedLowerShriekOfCompactificationPlus
        (ModuleCat.{u + 1} (finiteTateCoefficient l F n)) c).obj
          ((proLine l F n X)⟦(2 : ℤ)⟧) :=
  SectionCompactSource.proSource (finiteTateCoefficient l F n) c z hz ≫
    (ProEtale.rightDerivedLowerShriekOfCompactificationPlus
      (ModuleCat.{u + 1} (finiteTateCoefficient l F n)) c).map
        (proClass l F n z hI hX)

/-- The compact target comparison includes exactly the inverse root-projection witness.
Source: blueprint rank-one Thom proof, Step 2
(blueprint: lem-pur-line-kummer-field-realization). -/
@[irreducible]
def compactTarget
    (hA : ((l ^ (n + 1) : ℕ) : finiteTateCoefficient l F n) = 0)
    {B X : Scheme.{u}} {π : X ⟶ B} (c : Compactification π)
    (q : (ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} (finiteTateCoefficient l F n)) X).obj
        (finiteEtaleTateLine X (l ^ (n + 1)) (finiteTateCoefficient l F n) hA) ≅
          finiteTateProSheaf l F n X 1) :
    (ProEtale.rightDerivedLowerShriekOfCompactificationPlus
      (ModuleCat.{u + 1} (finiteTateCoefficient l F n)) c).obj
        ((proLine l F n X)⟦(2 : ℤ)⟧) ≅
      (ProEtale.comparisonUpperStar
        (ModuleCat.{u + 1} (finiteTateCoefficient l F n)) B).mapDerivedCategoryPlus.obj
          ((Etale.rightDerivedLowerShriekOfCompactificationPlus
            (ModuleCat.{u + 1} (finiteTateCoefficient l F n)) c).obj
              ((etaleLine l F n hA X)⟦(2 : ℤ)⟧)) :=
  (ProEtale.rightDerivedLowerShriekOfCompactificationPlus
      (ModuleCat.{u + 1} (finiteTateCoefficient l F n)) c).mapIso
        (shiftedComparison l F n hA X q).symm ≪≫
    (ProEtale.compactSupportSiteComparisonPlus (finiteTateCoefficient l F n) c).symm.app
      ((etaleLine l F n hA X)⟦(2 : ℤ)⟧)

end AlgebraicGeometry.LineKummerField

namespace AlgebraicGeometry.LineKummerField
open Scheme
variable (l : ℕ) [Fact l.Prime] (F : Type u) [Field F]
  [Algebra (Padic l) F] [FiniteDimensional (Padic l) F] (n : ℕ)

/-- Realization of a Cartier pair: exact supported images and equality of actual arrows.
Source: blueprint rank-one Thom proof, Steps 2--3
(blueprint: lem-pur-line-kummer-field-realization). -/
@[irreducible]
def PairRealization
    (hA : ((l ^ (n + 1) : ℕ) : finiteTateCoefficient l F n) = 0)
    {D T : Scheme.{u}} (i : D ⟶ T) [IsClosedImmersion i]
    (hI : i.ker.IsInvertible) (hT : IsUnit (l : Γ(T, ⊤)))
    (q : (ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} (finiteTateCoefficient l F n)) T).obj
        (finiteEtaleTateLine T (l ^ (n + 1)) (finiteTateCoefficient l F n) hA) ≅
          finiteTateProSheaf l F n T 1) : Prop :=
  PreservesFiniteColimits (Etale.lowerStar (ModuleCat.{u + 1} (finiteTateCoefficient l F n)) i) ∧
  PreservesFiniteColimits
    (ProEtale.lowerStar (ModuleCat.{u + 1} (finiteTateCoefficient l F n)) i) ∧
  (ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} (finiteTateCoefficient l F n)) T).mapDerivedCategoryPlus.map
        (etaleClass l F n hA i hI hT) ≫ (shiftedComparison l F n hA T q).hom =
    SectionCompactSource.compareSupported (finiteTateCoefficient l F n) i ≫
      proClass l F n i hI hT

/-- The two supported Kummer pullback equations, using the canonical supported mate
and root-normalized target comparisons. No compact-support exchange is involved.
Source: blueprint rank-one Thom proof, Step 3
(blueprint: lem-pur-line-kummer-field-realization). -/
@[irreducible]
def PairPullback
    (hA : ((l ^ (n + 1) : ℕ) : finiteTateCoefficient l F n) = 0)
    {D D' T T' : Scheme.{u}} (i : D ⟶ T) (i' : D' ⟶ T')
    [IsClosedImmersion i] [IsClosedImmersion i']
    {w : D' ⟶ D} {v : T' ⟶ T} (sq : ChosenCartesianSquare w i' i v)
    (hI : i.ker.IsInvertible) (hI' : i'.ker.IsInvertible)
    (hT : IsUnit (l : Γ(T, ⊤))) (hT' : IsUnit (l : Γ(T', ⊤))) : Prop :=
  ∃ (e : (Etale.upperStar (ModuleCat.{u + 1} (finiteTateCoefficient l F n)) v).obj
        (finiteEtaleTateLine T (l ^ (n + 1)) (finiteTateCoefficient l F n) hA) ≅
          finiteEtaleTateLine T' (l ^ (n + 1)) (finiteTateCoefficient l F n) hA)
    (p : (ProEtale.upperStar (ModuleCat.{u + 1} (finiteTateCoefficient l F n)) v).obj
        (finiteTateProSheaf l F n T 1) ≅ finiteTateProSheaf l F n T' 1),
    IsFiniteTateEtalePullback l F n T v n hA 1 e ∧
    IsFiniteTateProPullback l F n T v 1 p ∧
    (Etale.upperStar (ModuleCat.{u + 1} (finiteTateCoefficient l F n)) v).mapDerivedCategoryPlus.map
        (etaleClass l F n hA i hI hT) ≫
      ((Etale.upperStar
        (ModuleCat.{u + 1} (finiteTateCoefficient l F n)) v).mapDerivedCategoryPlus.commShiftIso
        (2 : ℤ)).hom.app _ ≫
      (shiftFunctor _ (2 : ℤ)).map
        ((Functor.mapDerivedCategoryPlusSingleFunctor
          (Etale.upperStar (ModuleCat.{u + 1} (finiteTateCoefficient l F n)) v) 0).hom.app _ ≫
          (DerivedCategory.Plus.singleFunctor _ 0).map e.hom) =
      SectionCompactSource.etaleBeta (finiteTateCoefficient l F n) sq ≫
        etaleClass l F n hA i' hI' hT' ∧
    (ProEtale.upperStar
      (ModuleCat.{u + 1} (finiteTateCoefficient l F n)) v).mapDerivedCategoryPlus.map
        (proClass l F n i hI hT) ≫
      ((ProEtale.upperStar
        (ModuleCat.{u + 1} (finiteTateCoefficient l F n)) v).mapDerivedCategoryPlus.commShiftIso
        (2 : ℤ)).hom.app _ ≫
      (shiftFunctor _ (2 : ℤ)).map
        ((Functor.mapDerivedCategoryPlusSingleFunctor
          (ProEtale.upperStar (ModuleCat.{u + 1} (finiteTateCoefficient l F n)) v) 0).hom.app _ ≫
          (DerivedCategory.Plus.singleFunctor _ 0).map p.hom) =
      SectionCompactSource.proBeta (finiteTateCoefficient l F n) sq ≫
        proClass l F n i' hI' hT'

/-- The normalized compact-image equality with the scalar-preserving constant source.
Source: blueprint rank-one Thom proof, Step 2
(blueprint: lem-pur-line-kummer-field-realization). -/
@[irreducible]
def CompactRealization
    (hA : ((l ^ (n + 1) : ℕ) : finiteTateCoefficient l F n) = 0)
    {B X : Scheme.{u}} {π : X ⟶ B} (c : Compactification π)
    (z : B ⟶ X) [IsClosedImmersion z] (hz : z ≫ π = 𝟙 B)
    (hI : z.ker.IsInvertible) (hX : IsUnit (l : Γ(X, ⊤)))
    (q : (ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} (finiteTateCoefficient l F n)) X).obj
        (finiteEtaleTateLine X (l ^ (n + 1)) (finiteTateCoefficient l F n) hA) ≅
          finiteTateProSheaf l F n X 1) : Prop :=
  IsIso (SectionCompactSource.proSource (finiteTateCoefficient l F n) c z hz) ∧
  proTau l F n c z hz hI hX ≫ (compactTarget l F n hA c q).hom =
    (SectionCompactSource.compareConstant (finiteTateCoefficient l F n) B).inv ≫
      (ProEtale.comparisonUpperStar
        (ModuleCat.{u + 1} (finiteTateCoefficient l F n)) B).mapDerivedCategoryPlus.map
          (etaleTau l F n hA c z hz hI hX)

end AlgebraicGeometry.LineKummerField

namespace AlgebraicGeometry.LineKummerField
open Scheme
variable (l : ℕ) [Fact l.Prime] (F : Type u) [Field F]
  [Algebra (Padic l) F] [FiniteDimensional (Padic l) F] (n : ℕ)

/-- The intrinsic ringed-site degree-zero object of the same prescribed twist.
Source: def-coefficient-twists-detailed and its fixed-scalar realization
(blueprint: lem-pur-line-kummer-field-realization). -/
def intrinsicLine (T : Scheme.{u}) :
    proEtaleDerivedCategory T (Padic.coefficientExtensionRing l F (n + 1)) :=
  (DerivedCategory.singleFunctor _ 0).obj (WeilConjectures.finiteCoefficientTwist l F T n 1)

/-- Pullback of the root-projection comparison on every scheme morphism.
Source: blueprint rank-one Thom proof, Steps 2--3; finite_tate_site_descent
(blueprint: lem-pur-line-kummer-field-realization). -/
@[irreducible]
def AlphaPullback
    (hA : ((l ^ (n + 1) : ℕ) : finiteTateCoefficient l F n) = 0)
    {T T' : Scheme.{u}} (v : T' ⟶ T)
    (q : (ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} (finiteTateCoefficient l F n)) T).obj
        (finiteEtaleTateLine T (l ^ (n + 1)) (finiteTateCoefficient l F n) hA) ≅
          finiteTateProSheaf l F n T 1)
    (q' : (ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} (finiteTateCoefficient l F n)) T').obj
        (finiteEtaleTateLine T' (l ^ (n + 1)) (finiteTateCoefficient l F n) hA) ≅
          finiteTateProSheaf l F n T' 1) : Prop :=
  ∃ (e : (Etale.upperStar (ModuleCat.{u + 1} (finiteTateCoefficient l F n)) v).obj
        (finiteEtaleTateLine T (l ^ (n + 1)) (finiteTateCoefficient l F n) hA) ≅
          finiteEtaleTateLine T' (l ^ (n + 1)) (finiteTateCoefficient l F n) hA)
    (p : (ProEtale.upperStar (ModuleCat.{u + 1} (finiteTateCoefficient l F n)) v).obj
        (finiteTateProSheaf l F n T 1) ≅ finiteTateProSheaf l F n T' 1),
    IsFiniteTateEtalePullback l F n T v n hA 1 e ∧
    IsFiniteTateProPullback l F n T v 1 p ∧
    (ProEtale.upperStar (ModuleCat.{u + 1} (finiteTateCoefficient l F n)) v).mapIso q ≪≫ p =
      (ProEtale.comparisonUpperStarCompUpperStarIso
        (ModuleCat.{u + 1} (finiteTateCoefficient l F n)) v).app
          (finiteEtaleTateLine T (l ^ (n + 1)) (finiteTateCoefficient l F n) hA) ≪≫
      (ProEtale.comparisonUpperStar
        (ModuleCat.{u + 1} (finiteTateCoefficient l F n)) T').mapIso e ≪≫ q'

/-- The coefficient and site realization clauses on an arbitrary scheme over the field.
The scalar-unit universal property specifies the derived tensor, including unbounded
representatives; its normalization fixes the map on every root tensor.
Source: blueprint rank-one Thom proof, Step 2
(blueprint: lem-pur-line-kummer-field-realization). -/
@[irreducible]
def CoefficientRealization
    (hA : ((l ^ (n + 1) : ℕ) : finiteTateCoefficient l F n) = 0)
    (T : Scheme.{u}) : Prop :=
  IsLocallyConstantSheaf
    (finiteEtaleTateLine T (l ^ (n + 1)) (finiteTateCoefficient l F n) hA) ∧
  (∃ cover : Cover.{u} etalePrecoverage T, ∀ j : cover.I₀,
    Nonempty
      ((finiteEtaleTateLine T (l ^ (n + 1)) (finiteTateCoefficient l F n) hA).over
        (cover.etalePrecoverageToEtale j) ≅
        (constantSheaf (T.smallEtaleTopology.over (cover.etalePrecoverageToEtale j))
          (ModuleCat.{u + 1} (finiteTateCoefficient l F n))).obj
            (ModuleCat.of (finiteTateCoefficient l F n) (finiteTateCoefficient l F n)))) ∧
  HasProEtaleTorAmplitude T (Padic.coefficientExtensionRing l F (n + 1))
    ((intrinsicLine l F n T)⟦(2 : ℤ)⟧) (-2) (-2) ∧
  ∃ η : finiteEtaleTateLine T (l ^ (n + 1)) (ULift.{u + 1} (ZMod (l ^ (n + 1))))
      (congrArg (ULift.up : ZMod (l ^ (n + 1)) → ULift.{u + 1} (ZMod (l ^ (n + 1))))
        (ZMod.natCast_self (l ^ (n + 1)))) ⟶
      (Sheaf.restrictScalars T.smallEtaleTopology
        ((finiteEtaleTwistScalar (l ^ (n + 1)) (finiteTateCoefficient l F n) hA).comp
          ULift.ringEquiv.toRingHom)).obj
            (finiteEtaleTateLine T (l ^ (n + 1)) (finiteTateCoefficient l F n) hA),
    Etale.SupportedDerivedScalarUnit
      ((finiteEtaleTwistScalar (l ^ (n + 1)) (finiteTateCoefficient l F n) hA).comp
        ULift.ringEquiv.toRingHom) T
      (finiteEtaleTateLine T (l ^ (n + 1)) (ULift.{u + 1} (ZMod (l ^ (n + 1))))
        (congrArg (ULift.up : ZMod (l ^ (n + 1)) → ULift.{u + 1} (ZMod (l ^ (n + 1))))
          (ZMod.natCast_self (l ^ (n + 1)))))
      (finiteEtaleTateLine T (l ^ (n + 1)) (finiteTateCoefficient l F n) hA) η ∧
    ∀ (U : T.Etaleᵒᵖ) (a : ULift.{u + 1} (ZMod (l ^ (n + 1))))
      (x : (T.rootsOfUnitySheaf (l ^ (n + 1))).obj.obj U),
      η.hom.app U (finiteEtaleTateOneGenerator
        (ULift.{u + 1} (ZMod (l ^ (n + 1)))) (l ^ (n + 1)) T
        (congrArg (ULift.up : ZMod (l ^ (n + 1)) → ULift.{u + 1} (ZMod (l ^ (n + 1))))
          (ZMod.natCast_self (l ^ (n + 1)))) U a x) =
        finiteEtaleTateOneGenerator (finiteTateCoefficient l F n) (l ^ (n + 1)) T hA U
          ((finiteEtaleTwistScalar (l ^ (n + 1)) (finiteTateCoefficient l F n) hA) a.down) x

/-- The assertions for the total space and zero section of the published line bundle.
The quantifiers over B', X' and their two Cartesian squares allow every base change,
with no flatness, finite-type, separation or Noetherian hypothesis on B'. The final
quantifier also includes isomorphisms of Cartier pairs and arbitrary choices of frame.
Source: blueprint rank-one Thom proof, Steps 1--3
(blueprint: lem-pur-line-kummer-field-realization). -/
@[irreducible]
def BundleRealization
    (hA : ((l ^ (n + 1) : ℕ) : finiteTateCoefficient l F n) = 0)
    (B : Scheme.{u}) [IsNoetherian B] (V : B.Modules) [V.IsFiniteLocallyFreeOfRank 1]
    (X : Scheme.{u}) (π : X ⟶ B) (z : B ⟶ X)
    [IsClosedImmersion z] (hz : z ≫ π = 𝟙 B) : Prop :=
  IsSeparated π ∧ LocallyOfFiniteType π ∧ QuasiCompact π ∧
  (∀ (U : B.Opens) (e : VectorBundleZeroSection.Trivialization B 1 V U),
    IsIso (VectorBundleZeroSection.trivializationMap B 1 V U e) ∧
    VectorBundleZeroSection.trivializationMap B 1 V U e ≫
      AffineSpace (ULift.{u} (Fin 1)) U.toScheme ↘ U.toScheme =
        (VectorBundleZeroSection.π B 1 V) ∣_ U ∧
    VectorBundleZeroSection.zeroRestricted B 1 V U ≫
      VectorBundleZeroSection.trivializationMap B 1 V U e =
        AffineSpace.zeroSection (ULift.{u} (Fin 1)) U.toScheme) ∧
  ∃ (hI : z.ker.IsInvertible) (hX : IsUnit (l : Γ(X, ⊤)))
    (q : (ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} (finiteTateCoefficient l F n)) X).obj
        (finiteEtaleTateLine X (l ^ (n + 1)) (finiteTateCoefficient l F n) hA) ≅
          finiteTateProSheaf l F n X 1),
    IsFiniteTateSiteComparison l F n X n hA 1 q ∧
    WeilConjectures.finiteTorConstructible l F (n + 1) (Nat.le_add_left 1 n) X
      ((intrinsicLine l F n X)⟦(2 : ℤ)⟧) ∧
    PairRealization l F n hA z hI hX q ∧
    (∀ c : Compactification π, CompactRealization l F n hA c z hz hI hX q) ∧
    (∀ {B' X' : Scheme.{u}} (g : B' ⟶ B) (v : X' ⟶ X) (π' : X' ⟶ B')
      (_sq : IsPullback v π' π g) (z' : B' ⟶ X') [IsClosedImmersion z']
      (sqZ : ChosenCartesianSquare g z' z v),
      ∃ (hI' : z'.ker.IsInvertible) (hX' : IsUnit (l : Γ(X', ⊤)))
        (q' : (ProEtale.comparisonUpperStar
          (ModuleCat.{u + 1} (finiteTateCoefficient l F n)) X').obj
            (finiteEtaleTateLine X' (l ^ (n + 1)) (finiteTateCoefficient l F n) hA) ≅
              finiteTateProSheaf l F n X' 1),
        IsFiniteTateSiteComparison l F n X' n hA 1 q' ∧
        AlphaPullback l F n hA v q q' ∧
        PairRealization l F n hA z' hI' hX' q' ∧
        PairPullback l F n hA z z' sqZ hI hI' hX hX') ∧
    (∀ {D' T' : Scheme.{u}} (i' : D' ⟶ T') [IsClosedImmersion i']
      (w : D' ⟶ B) (v : T' ⟶ X) [IsIso w] [IsIso v]
      (sq : ChosenCartesianSquare w i' z v),
      ∃ (hI' : i'.ker.IsInvertible) (hT' : IsUnit (l : Γ(T', ⊤))),
        PairPullback l F n hA z i' sq hI hI' hX hT')

/-- The supported zero class over an arbitrary coefficient-invertible field realizes
on the ordinary etale site, with finite Tor amplitude, arbitrary Cartier pullback,
and identity-normalized compact image on both sites.
Source: blueprint main-20261015, rank-one Thom proof, Steps 1--3
(blueprint: lem-pur-line-kummer-field-realization).

Proof (the nine steps of the node):
1. A field is Noetherian. Finite type makes B Noetherian. The published relative
symmetric-algebra charts identify the rank-one pair with Spec R[t], V(t).
Projective completion makes the projection separated and finite type and E Noetherian.
2. The prime l lies in the uniformizer ideal, so l^(n+1) vanishes in the quotient
at exponent n+1, without a ramification restriction. The finite root sheaf is an
etale locally free Z/l^(n+1) line. Its flatness identifies derived scalar extension
with the ordinary tensor, even when the coefficient quotient itself is not flat.
3. Compose finite-root site comparison with inverse root-projection reduction.
The pure-root formula fixes alpha, and its pullback law follows on the same tensors.
4. Tensor with the locally free pro-etale line is exact. After shifting by two,
all tests have cohomology only in degree -2. A single stratum makes the finite
line constructible; hence its shifted object belongs to D^b_ctf.
5. The polynomial variable is a nonzerodivisor over every ring. After every g the
same charts remain polynomial charts, so the divisor stays Cartier. Its complement
is locally D(t), hence its open immersion is quasi-compact even over a non-Noetherian B'.
6. Etale closed direct image is exact. Pro-etale closed direct image is exact for
this quasi-compact complement. Exact derived comparison gives Rz_* = z_* on both sites,
before and after pullback.
7. Apply ordinary supported Kummer and its prescribed pro-etale realization. The
supported-constant mate and root-projection comparisons identify the actual arrows.
Their Cartier pullback squares apply to every g of step 5 and every pair isomorphism.
8. Use SectionCompactSource.etaleSource and proSource at (pi,z). Their normalization
uses the proper/open composite on the etale site and the canonical composition for
pi z = id on the pro-etale site. The constant-unit comparison fixes the source scalar.
9. Naturality of compactSupportSiteComparisonPlus at the actual Kummer arrow,
composed with the normalized source equality, gives CompactRealization. Every input
uses only a field with l invertible, so a new application with field Omega and its
trivial line proves the geometric-fibre assertion without a finite-type condition
on Omega over the old field. No compact-support exchange under g is claimed. -/
theorem line_kummer_field_realization
    (K₀ : Type u) [Field K₀] (_hl : IsUnit (l : K₀)) :
    ∃ hA : ((l ^ (n + 1) : ℕ) : finiteTateCoefficient l F n) = 0,
      (∀ (T : Scheme.{u}) [T.Over (Spec (.of K₀))],
        CoefficientRealization l F n hA T ∧
        ∃ q : (ProEtale.comparisonUpperStar
          (ModuleCat.{u + 1} (finiteTateCoefficient l F n)) T).obj
            (finiteEtaleTateLine T (l ^ (n + 1)) (finiteTateCoefficient l F n) hA) ≅
              finiteTateProSheaf l F n T 1,
          IsFiniteTateSiteComparison l F n T n hA 1 q ∧
          ∀ (T' : Scheme.{u}) (v : T' ⟶ T)
            (q' : (ProEtale.comparisonUpperStar
              (ModuleCat.{u + 1} (finiteTateCoefficient l F n)) T').obj
                (finiteEtaleTateLine T' (l ^ (n + 1)) (finiteTateCoefficient l F n) hA) ≅
                  finiteTateProSheaf l F n T' 1),
            IsFiniteTateSiteComparison l F n T' n hA 1 q' →
              AlphaPullback l F n hA v q q') ∧
      ∀ (B : Scheme.{u}) [B.Over (Spec (.of K₀))]
        [LocallyOfFiniteType (B ↘ Spec (.of K₀))] [QuasiCompact (B ↘ Spec (.of K₀))]
        [IsSeparated (B ↘ Spec (.of K₀))],
        ∃ hB : IsNoetherian B, ∀ (V : B.Modules) [V.IsFiniteLocallyFreeOfRank 1],
          @BundleRealization l _ F _ _ _ n hA B hB V _
            (@VectorBundleZeroSection.scheme B hB 1 V _)
            (@VectorBundleZeroSection.π B hB 1 V _)
            (@VectorBundleZeroSection.zero B hB 1 V _)
            (@zeroClosed B hB V _) (@VectorBundleZeroSection.zero_spec B hB 1 V _).1 := by
  sorry

end AlgebraicGeometry.LineKummerField
