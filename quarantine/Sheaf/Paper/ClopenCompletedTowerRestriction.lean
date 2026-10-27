module

public import Sheaf.Paper.ClopenCounitAdjointComparison
public import Sheaf.Paper.CoefficientSystemDerivedComparison
public import Sheaf.Paper.OpenCompletedRestrictionIdentification
public import Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients
public import Sheaf.Paper.DerivedCompleteOnSlices
public import Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory

/-! # Site transport and integral realization on a clopen component

Source: blueprint def-pur-section-invariant, finite-clopen expansion, retained steps 8--9;
Zheng, Lemmas 4.10 and 5.22; Stacks Tags 0941 and 08BJ
(blueprint: def-pur-clopen-completed-tower-restriction).

All systems below are actual strict systems. Their scalar forgetting and inverse limit
are the published functors on the derived category of strict towers. The result records
normalization equations for maps, as well as natural isomorphisms.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option genSizeOfSpec false
set_option genCtorIdx false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology
attribute [local irreducible] HasDerivedCategory.standard
set_option allowUnsafeReducibility true
attribute [local reducible] WeilConjectures.IntegralOnSlice.Site
  WeilConjectures.IntegralOnSlice.topology WeilConjectures.IntegralOnSlice.restrict
  WeilConjectures.IntegralOnSlice.ring WeilConjectures.IntegralOnSlice.finite
  WeilConjectures.IntegralOnSlice.projection
universe u w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace WeilConjectures.PurityFiniteSetting

/-- Positive coefficient level of the same global purity datum.
Source: blueprint purity conventions (blueprint: def-pur-clopen-completed-tower-restriction). -/
def clopenRealizationLevel (P : PurityFiniteSetting.{u}) (n : ℕ) : PurityFiniteSetting.{u} :=
  { P with level := n + 1, level_pos := Nat.succ_pos n }

/-- The published ordinary completed-module restriction, with its global module type fixed.
Source: Stacks 0941 (blueprint: def-pur-clopen-completed-tower-restriction). -/
def clopenCompletedOrdinary (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {Xi X : Scheme.{u}} (j : Xi ⟶ X) [IsOpenImmersion j] :
    scalarReductionSource.{u, u} l E X ⥤ scalarReductionSource.{u, u} l E Xi :=
  OpenCompletedRestriction.ordinary.{u, u} l E j

/-- The existing additive restriction instance in the fixed global presentation.
Source: Stacks 0941 (blueprint: def-pur-clopen-completed-tower-restriction). -/
instance clopenCompletedOrdinaryAdditive (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {Xi X : Scheme.{u}} (j : Xi ⟶ X) [IsOpenImmersion j] :
    (clopenCompletedOrdinary l E j).Additive :=
  OpenCompletedRestriction.ordinaryAdditive.{u, u} l E j

/-- The existing finite-limit restriction instance in the fixed global presentation.
Source: Stacks 0941 (blueprint: def-pur-clopen-completed-tower-restriction). -/
instance clopenCompletedOrdinaryLimits (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {Xi X : Scheme.{u}} (j : Xi ⟶ X) [IsOpenImmersion j] :
    PreservesFiniteLimits (clopenCompletedOrdinary l E j) :=
  OpenCompletedRestriction.ordinaryLimits.{u, u} l E j

/-- The existing finite-colimit restriction instance in the fixed global presentation.
Source: Stacks 0941 (blueprint: def-pur-clopen-completed-tower-restriction). -/
instance clopenCompletedOrdinaryColimits (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {Xi X : Scheme.{u}} (j : Xi ⟶ X) [IsOpenImmersion j] :
    PreservesFiniteColimits (clopenCompletedOrdinary l E j) :=
  OpenCompletedRestriction.ordinaryColimits.{u, u} l E j

/-- The exact ordinary restriction of strict completed-coefficient towers.
Source: Stacks 0941 (blueprint: def-pur-clopen-completed-tower-restriction). -/
def clopenCompletedTowerOrdinary (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {Xi X : Scheme.{u}} (j : Xi ⟶ X) [IsOpenImmersion j] :
    (ℕᵒᵖ ⥤ scalarReductionSource.{u, u} l E X) ⥤
      (ℕᵒᵖ ⥤ scalarReductionSource.{u, u} l E Xi) :=
  (Functor.whiskeringRight ℕᵒᵖ
    (scalarReductionSource.{u, u} l E X) (scalarReductionSource.{u, u} l E Xi)).obj
      (clopenCompletedOrdinary l E j)

/-- Additivity of pointwise completed-coefficient restriction.
Source: Stacks 0941 (blueprint: def-pur-clopen-completed-tower-restriction). -/
instance clopenCompletedTowerAdditive (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {Xi X : Scheme.{u}} (j : Xi ⟶ X) [IsOpenImmersion j] :
    (clopenCompletedTowerOrdinary l E j).Additive := by
  let := clopenCompletedOrdinaryAdditive l E j
  dsimp only [clopenCompletedTowerOrdinary]
  infer_instance

/-- Pointwise finite-limit preservation of the exact tower restriction.
Source: Stacks 0941 (blueprint: def-pur-clopen-completed-tower-restriction). -/
instance clopenCompletedTowerLimits (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {Xi X : Scheme.{u}} (j : Xi ⟶ X) [IsOpenImmersion j] :
    PreservesFiniteLimits (clopenCompletedTowerOrdinary l E j) := by
  let := clopenCompletedOrdinaryLimits l E j
  constructor
  intro J _ _
  dsimp only [clopenCompletedTowerOrdinary]
  infer_instance

/-- Pointwise finite-colimit preservation of the exact tower restriction.
Source: Stacks 0941 (blueprint: def-pur-clopen-completed-tower-restriction). -/
instance clopenCompletedTowerColimits (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {Xi X : Scheme.{u}} (j : Xi ⟶ X) [IsOpenImmersion j] :
    PreservesFiniteColimits (clopenCompletedTowerOrdinary l E j) := by
  let := clopenCompletedOrdinaryColimits l E j
  constructor
  intro J _ _
  dsimp only [clopenCompletedTowerOrdinary]
  infer_instance

/-- Exact restriction of completed-coefficient strict towers, followed by localization.
Source: Stacks 0941 (blueprint: def-pur-clopen-completed-tower-restriction). -/
def clopenCompletedTowerRestriction (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {Xi X : Scheme.{u}} (j : Xi ⟶ X) [IsOpenImmersion j] :
    coefficientSequenceRestrictedDerived.{u, u} l E X ⥤
      coefficientSequenceRestrictedDerived.{u, u} l E Xi :=
  letI := clopenCompletedOrdinaryAdditive l E j
  letI := clopenCompletedOrdinaryLimits l E j
  letI := clopenCompletedOrdinaryColimits l E j
  (clopenCompletedTowerOrdinary l E j).mapDerivedCategory


end WeilConjectures.PurityFiniteSetting
