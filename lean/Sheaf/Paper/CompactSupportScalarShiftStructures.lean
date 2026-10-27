module

public import Sheaf.Paper.PurityFiniteSetting
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.Compactification.RefinementCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Sheaf.Paper.CompletedIntegralConstantMapOfUniverses
public import Sheaf.Algebra.Homology.OrdinaryDerivedChangeOfRings
public import Sheaf.Paper.SfIntegralConstructible
public import Sheaf.Paper.FiniteTorAmplitudeSites
public import Sheaf.Paper.QcqsCompactSupportRealization
public import Sheaf.Paper.CompactSupportReductionTower
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Sheaf.Paper.CompactSupportStrictScalarMate
public import Sheaf.Paper.FiniteFreeCompletedScalarComparison
public import Sheaf.Paper.CompactSupportScalarLimitReduction
public import Mathlib.CategoryTheory.Triangulated.Pretriangulated
public import Mathlib.CategoryTheory.Shift.CommShift
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated

/-! # Canonical shifts of scalar compact-support comparison maps

Source: Stacks 05SU, 06YU, 0B56, 0941 and 03DJ; auxiliary comparison Steps 12--13
(blueprint: lem-pur-compact-support-scalar-shift-normalization).
The data helpers expose canonical shifts of existing functors. The theorem retains
proper/open, strict-tower, signed Roos, and completed total-limit equations.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] WeilConjectures.SemilinearSections.moduleAbelian
attribute [local irreducible] CategoryTheory.Functor.mapDerivedCategory
  CategoryTheory.Functor.rightDerivedFunctor
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale.StrictTower
namespace WeilConjectures.PurStrictScalar
variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (F : Type u) [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
  (i : E →ₐ[ℚ_[l]] F) (W : Scheme.{u})
/-- Canonical integer shifts for tensorCommShift, inherited from the specified construction.
Source: Stacks 05SU, 06YY, 0D6E and 0941
(blueprint: lem-pur-compact-support-scalar-shift-normalization). -/
instance tensorCommShift : (T l E F i W).CommShift ℤ :=
  inferInstanceAs ((tensor l E F i W).mapDerivedCategory.CommShift ℤ)
/-- Canonical integer shifts for properCommShift, inherited from the specified construction.
Source: Stacks 05SU, 06YY, 0D6E and 0941
(blueprint: lem-pur-compact-support-scalar-shift-normalization). -/
instance properCommShift {X Y : Scheme.{u}} (g : X ⟶ Y) :
    (R (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) g).CommShift ℤ :=
  inferInstanceAs ((towerDirectImage
    (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) g).rightDerivedFunctor.CommShift ℤ)
/-- Canonical integer shifts for openCommShift, inherited from the specified construction.
Source: Stacks 05SU, 06YY, 0D6E and 0941
(blueprint: lem-pur-compact-support-scalar-shift-normalization). -/
instance openCommShift {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j] :
    (J (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) j).CommShift ℤ :=
  inferInstanceAs ((towerJ
    (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) j).mapDerivedCategory.CommShift ℤ)
/-- Canonical integer shifts for sequenceLimitCommShift, inherited from the specified construction.
Source: Stacks 05SU, 06YY, 0D6E and 0941
(blueprint: lem-pur-compact-support-scalar-shift-normalization). -/
instance sequenceLimitCommShift : (coefficientSequenceLimit l E W).CommShift ℤ := by
  unfold coefficientSequenceLimit coefficientConstantTowerLimit
  infer_instance
/-- Canonical integer shifts for systemRestrictionCommShift,
 inherited from the specified construction.
Source: Stacks 05SU, 06YY, 0D6E and 0941
(blueprint: lem-pur-compact-support-scalar-shift-normalization). -/
instance systemRestrictionCommShift : (systemU l E W).CommShift ℤ :=
  inferInstanceAs ((systemRestriction l E W).mapDerivedCategory.CommShift ℤ)
/-- Canonical integer shifts for nativeOpenCommShift, inherited from the specified construction.
Source: Stacks 05SU, 06YY, 0D6E and 0941
(blueprint: lem-pur-compact-support-scalar-shift-normalization). -/
instance nativeOpenCommShift {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j] :
    (ProEtale.VaryingRing.J (compactSupportSystemLevel l E)
      (compactSupportSystemQuotient l E) j).CommShift ℤ := by
  unfold ProEtale.VaryingRing.J
  infer_instance
/-- Canonical integer shifts for nativeProperCommShift, inherited from the specified construction.
Source: Stacks 05SU, 06YY, 0D6E and 0941
(blueprint: lem-pur-compact-support-scalar-shift-normalization). -/
instance nativeProperCommShift {X Y : Scheme.{u}} (g : X ⟶ Y) :
    (ProEtale.VaryingRing.P (compactSupportSystemLevel l E)
      (compactSupportSystemQuotient l E) g).CommShift ℤ := by
  unfold ProEtale.VaryingRing.P
  infer_instance
/-- Canonical integer shifts for reductionCommShift, inherited from the specified construction.
Source: Stacks 05SU, 06YY, 0D6E and 0941
(blueprint: lem-pur-compact-support-scalar-shift-normalization). -/
instance reductionCommShift (S : CoefficientDerivedSystemCalculus.{u, u} l E W) :
    S.reduction.CommShift ℤ := S.adjunction.leftAdjointCommShift ℤ
/-- Canonical integer shifts for supportCommShift, inherited from the specified construction.
Source: Stacks 05SU, 06YY, 0D6E and 0941
(blueprint: lem-pur-compact-support-scalar-shift-normalization). -/
instance supportCommShift {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (S : CoefficientDerivedSystemCalculus.{u, u} l E X) : (support l E c S).CommShift ℤ := by
  unfold support
  infer_instance
/-- Canonical integer shifts for nativeSupportCommShift, inherited from the specified construction.
Source: Stacks 05SU, 06YY, 0D6E and 0941
(blueprint: lem-pur-compact-support-scalar-shift-normalization). -/
instance nativeSupportCommShift {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (S : CoefficientDerivedSystemCalculus.{u, u} l E X) :
    (scalarSupportNative l E c S).CommShift ℤ := by
  unfold scalarSupportNative
  infer_instance
/-- Canonical integer shifts for scalarSupportCommShift, inherited from the specified construction.
Source: Stacks 05SU, 06YY, 0D6E and 0941
(blueprint: lem-pur-compact-support-scalar-shift-normalization). -/
instance scalarSupportCommShift {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (S : CoefficientDerivedSystemCalculus.{u, u} l E X) :
    (scalarSupport l E c S).CommShift ℤ :=
  haveI := nativeSupportCommShift l E c S
  haveI := sequenceLimitCommShift l E Y
  inferInstanceAs ((scalarSupportNative l E c S ⋙ coefficientSequenceLimit l E Y).CommShift ℤ)
/-- Canonical integer shifts for baseTensorCommShift, inherited from the specified construction.
Source: Stacks 05SU, 06YY, 0D6E and 0941
(blueprint: lem-pur-compact-support-scalar-shift-normalization). -/
instance baseTensorCommShift : (baseTensor l E F i W).CommShift ℤ :=
  haveI := (baseTensor_exact l E F i W).1
  haveI := (baseTensor_exact l E F i W).2
  inferInstanceAs ((pbcExtend (constantMap l E F i W)).mapDerivedCategory.CommShift ℤ)
/-- Canonical integer shifts for constantRestrictionCommShift,
 inherited from the specified construction.
Source: Stacks 05SU, 06YY, 0D6E and 0941
(blueprint: lem-pur-compact-support-scalar-shift-normalization). -/
instance constantRestrictionCommShift : (scalarConstantRestriction l E W).CommShift ℤ :=
  inferInstanceAs ((constantRestriction l E W).mapDerivedCategory.CommShift ℤ)
/-- Canonical integer shifts for subsequenceCommShift, inherited from the specified construction.
Source: Stacks 05SU, 06YY, 0D6E and 0941
(blueprint: lem-pur-compact-support-scalar-shift-normalization). -/
instance subsequenceCommShift (e : ℕ) : (subsequence l E W e).CommShift ℤ :=
  inferInstanceAs ((ordinarySubsequence l E W e).mapDerivedCategory.CommShift ℤ)
/-- Canonical integer shifts for completedExtensionCommShift,
 inherited from the specified construction.
Source: Stacks 05SU, 06YY, 0D6E and 0941
(blueprint: lem-pur-compact-support-scalar-shift-normalization). -/
instance completedExtensionCommShift :
    (pbcDerivedExtend (completedCoefficientMap l E F i W)).CommShift ℤ :=
  PurCompactSupport.scalarCommShift (completedCoefficientMap l E F i W)
/-- Canonical integer shifts for scalarCompletionTargetCommShift,
 inherited from the specified construction.
Source: Stacks 05SU, 06YY, 0D6E and 0941
(blueprint: lem-pur-compact-support-scalar-shift-normalization). -/
instance scalarCompletionTargetCommShift :
    (pbcDerivedExtend (completedCoefficientMap l E F i W) ⋙
      scalarConstantRestriction l F W).CommShift ℤ :=
  haveI := completedExtensionCommShift l E F i W
  haveI := constantRestrictionCommShift l F W
  inferInstance
/-- Canonical integer shifts for pullCommShift, inherited from the specified construction.
Source: Stacks 05SU, 06YY, 0D6E and 0941
(blueprint: lem-pur-compact-support-scalar-shift-normalization). -/
instance pullCommShift {X Y : Scheme.{u}} (g : X ⟶ Y) :
    (G (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) g).CommShift ℤ :=
  inferInstanceAs ((towerPullback
    (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) g).mapDerivedCategory.CommShift ℤ)

/-- The original-site proper/open squares, including the balanced transpose and counit.
Source: Stacks 07A6, 0B56 and 0E8I
(blueprint: lem-pur-compact-support-scalar-shift-normalization).
Interface attachment: (blueprint: def-pur-compact-support-scalar-shift-structures). -/
def OriginalMateShift {R₀ S₀ : PurCompactSupport.Coefficients.{u}}
    (a : PurCompactSupport.Change R₀ S₀) {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) : Prop :=
  NatTrans.CommShift (PurCompactSupport.properComparison a c.g) ℤ ∧
  NatTrans.CommShift (PurCompactSupport.openComparison a c.i) ℤ ∧
  NatTrans.CommShift (PurCompactSupport.scalarPull a c.g).inv ℤ ∧
  NatTrans.CommShift (proEtaleRingDerivedAdjunction c.g
    (R₀.ring Y) (R₀.ring c.Z) (R₀.pull c.g)).counit ℤ

end WeilConjectures.PurStrictScalar
