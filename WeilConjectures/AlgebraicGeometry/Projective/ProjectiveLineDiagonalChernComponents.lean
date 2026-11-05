/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Projective.ProjectiveLineDiagonalData
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1KummerMaps
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteFirstChern
import WeilConjectures.AlgebraicGeometry.ProjectiveLineDiagonalChartComparison
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1DiagonalComponents
import WeilConjectures.AlgebraicGeometry.FiniteP1DiagonalPicard
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteConstantUnitComp
import WeilConjectures.AlgebraicGeometry.OrdinarySupportedChernNormalization
import WeilConjectures.AlgebraicGeometry.ProjectiveLineDiagonalAlphaUnits

/-! # The two Chern components of the projective-line diagonal

Source: blueprint lem-amb-p1-diagonal-integrals, the equation of the diagonal and its
Kummer class (blueprint: lem-amb-p1-diagonal-chern-components).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option Elab.async false
universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
namespace AlgebraicGeometry.Etale

set_option linter.auxLemma false in
attribute [local instance 100000] DerivedCategoryModule._proof_1 DerivedCategoryModule._proof_2
attribute [local irreducible] HasDerivedCategory.ofIsGrothendieckAbelian
  DerivedCategory.singleFunctors derivedUpperStarLowerStarAdjunction

-- Compare recorded instances without expanding the derived localization constructions.
private meta def unfoldBoundary (e : Lean.Expr) : Lean.MetaM (Option Lean.Expr) := do
  if let .fvar id := e then
    if let some v := (← id.getDecl).value? then return some v
  if let .letE _ _ v b _ := e then return some (b.instantiate1 v)
  let names : List Lean.Name := [``DerivedCategoryModule, ``ordinaryFinitePushforward,
    ``ordinaryFinitePullback, ``ordinaryFiniteP1DiagonalTarget,
    ``ordinaryFiniteP1DiagonalChartMap, ``ordinaryFiniteChartTransport,
    ``ordinaryFiniteAdjunction, ``projectiveLineDiagonalChartPushforward,
    ``ordinaryFiniteP1DiagonalSupportedMap, ``ordinaryFiniteSupportedRealization,
    ``ordinaryFiniteSupportedExt, ``pullback.diagonalObj, ``ordinaryFiniteLine,
    ``ordinaryFiniteDegreeZero, ``ordinaryFiniteSingleFunctor, ``ordinaryFiniteUnit]
  if let some n := e.getAppFn.constName? then
    if names.contains n then
      return ← Lean.Meta.withTransparency .all (Lean.Meta.unfoldDefinition? e)
  return none

private meta def reduceRecordProjection (e : Lean.Expr) : Lean.MetaM (Option Lean.Expr) := do
  let some n := e.getAppFn.constName? | return none
  let some info ← Lean.getProjectionFnInfo? n | return none
  let args := e.getAppArgs
  unless args.size == info.numParams + 1 do return none
  let v ← Lean.Meta.withTransparency .all (Lean.Meta.whnf args.back!)
  Lean.Expr.reduceProjStruct? (Lean.mkAppN e.getAppFn (args.set! (args.size - 1) v))

private meta def reduceIdentityObj (e : Lean.Expr) : Lean.Expr := Id.run do
  if e.getAppFn.isConstOf ``Functor.obj then
    let args := e.getAppArgs
    if args.size ≥ 2 && (args[args.size - 2]!).getAppFn.isConstOf ``Functor.id then
      return args.back!
  return e

/-- Build a kernel-checked congruence, treating proof arguments by proof irrelevance. -/
private meta def structuralHEq : Nat → Lean.Expr → Lean.Expr → Lean.MetaM Lean.Expr
  | 0, _, _ => throwError "chart congruence exhausted its structural depth"
  | fuel + 1, lhs, rhs => do
    let lhs := reduceIdentityObj (← Lean.instantiateMVars lhs).consumeMData.headBeta
    let rhs := reduceIdentityObj (← Lean.instantiateMVars rhs).consumeMData.headBeta
    if lhs == rhs then return ← Lean.Meta.mkHEqRefl lhs
    if let (.const n _, .const m _) := (lhs, rhs) then
      if n == m then return ← Lean.Meta.mkHEqRefl lhs
    if lhs.isSort && rhs.isSort && (← Lean.Meta.isDefEq lhs rhs) then
      return ← Lean.Meta.mkHEqRefl lhs
    if ← Lean.Meta.isProp (← Lean.Meta.inferType lhs) then
      return ← Lean.Meta.mkAppM ``proof_irrel_heq #[lhs, rhs]
    let aa := lhs.getAppArgs
    let bb := rhs.getAppArgs
    let sameHead := lhs.getAppFn == rhs.getAppFn ||
      (lhs.getAppFn.constName?.isSome && lhs.getAppFn.constName? == rhs.getAppFn.constName?)
    unless sameHead && aa.size == bb.size && aa.size > 0 do
      if let some a ← unfoldBoundary lhs then return ← structuralHEq fuel a rhs
      if let some b ← unfoldBoundary rhs then return ← structuralHEq fuel lhs b
      if let some a ← reduceRecordProjection lhs then return ← structuralHEq fuel a rhs
      if let some b ← reduceRecordProjection rhs then return ← structuralHEq fuel lhs b
      if lhs.isLambda || rhs.isLambda then
        if ← Lean.Meta.isDefEq lhs rhs then return ← Lean.Meta.mkHEqRefl lhs
      throwError "chart congruence: {lhs} versus {rhs}"
    let ct ← Lean.Meta.mkHCongrWithArity lhs.getAppFn aa.size
    let mut pf := ct.proof
    for i in [:aa.size] do
      let ih ← structuralHEq fuel aa[i]! bb[i]!
      let arg ← match ct.argKinds[i]! with
        | .eq => Lean.Meta.mkAppM ``eq_of_heq #[ih]
        | .heq => pure ih
        | _ => throwError "unexpected chart congruence argument"
      pf := Lean.mkAppN pf #[aa[i]!, bb[i]!, arg]
    if (← Lean.Meta.inferType pf).isEq then
      return ← Lean.Meta.mkAppM ``heq_of_eq #[pf]
    return pf

/-- The Chern adjunct of the diagonal is the sum of the relative hyperplane adjunct
and the shifted twisted unit after the base hyperplane class.
Source: blueprint lem-amb-p1-diagonal-integrals, the equation x0 y1 - x1 y0 and
proof steps 2--5 (blueprint: lem-amb-p1-diagonal-chern-components).

Proof: The four product-chart equations for the diagonal are the local expressions of
one section of pr1^* O(1) tensor pr2^* O(1). Their nonzerodivisor property identifies
its dual ideal with that tensor product. Under either canonical chart this line is
O(1) tensor r^* O(1). Apply the supported-Kummer unit/Chern equation. The Kummer
connecting homomorphism is additive on Picard classes, so its unsupported class is the
sum of the relative hyperplane Chern class and the inverse image of the base hyperplane
Chern class. The integral-generator comparison is bijective, hence gives the equality
of the derived arrows with their prescribed scalar extension. Take adjuncts under r^*
left adjoint to Rr_*. Naturality of its unit gives the base class followed by the
shifted twisted unit; the other summand is precisely the hyperplane Chern adjunct.
The chart adjunction and direct-image composition identify this adjunct with the
left-hand side. All coefficient comparisons are normalized on roots and pure tensors,
so no orientation is chosen. Swapping the factors changes the diagonal equation by
-1, which does not change its divisor line or Chern class. This also covers N=1,
the zero coefficient ring, the empty base, and bases with nilpotents.
-/
theorem projectiveLine_diagonal_chern_components (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤)))
    (hI : (pullback.diagonal (ProjectiveLine S ↘ S)).ker.IsInvertible)
    (κ : Ext
      ((lowerStar (ModuleCat.{u + 1} A) (pullback.diagonal (ProjectiveLine S ↘ S))).obj
        (ordinaryFiniteConstant A (ProjectiveLine S)))
      (Scheme.finiteEtaleTateLine
        (pullback (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)) N A hA) 2)
    (hT : IsUnit (N : Γ(pullback (ProjectiveLine S ↘ S)
      (ProjectiveLine S ↘ S), ⊤)))
    (hκ : SupportedKummerBoundary A N hA
      (pullback.diagonal (ProjectiveLine S ↘ S)) hI hT κ) (a : Bool) :
    letI : IsLocallyNoetherian (ProjectiveLine S) :=
      LocallyOfFiniteType.isLocallyNoetherian (ProjectiveLine S ↘ S)
    letI : CompactSpace (ProjectiveLine S) :=
      QuasiCompact.compactSpace_of_compactSpace (ProjectiveLine S ↘ S)
    letI : IsNoetherian (ProjectiveLine S) := ⟨⟩
    let hP := ordinaryFiniteP1_isUnit N S hS
    projectiveLineDiagonalAlpha A S a ≫
      (ordinaryFinitePushforward A (projectiveLineDiagonalProjection S a)).map
        (supportedExactDerivedMap
          (lowerStar (ModuleCat.{u + 1} A) (pullback.diagonal (ProjectiveLine S ↘ S)))
          (ordinaryFiniteConstant A (ProjectiveLine S))
          (Scheme.finiteEtaleTateLine
            (pullback (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)) N A hA) κ) ≫
      projectiveLineDiagonalChartPushforward N hN A hA S hS a =
    ordinaryFiniteP1ChernPushforward A N hA (ProjectiveLine S)
        (projectiveLineTraceDatum N hN A hA (ProjectiveLine S) hP).chern +
      (projectiveLineTraceDatum N hN A hA S hS).chern ≫
        ordinaryFiniteP1Unit A N hA (projectiveLineTraceTransport N hN A hA)
          (ProjectiveLine S) hP := by
  dsimp only
  let : IsLocallyNoetherian (ProjectiveLine S) :=
    LocallyOfFiniteType.isLocallyNoetherian (ProjectiveLine S ↘ S)
  let : CompactSpace (ProjectiveLine S) :=
    QuasiCompact.compactSpace_of_compactSpace (ProjectiveLine S ↘ S)
  let : IsNoetherian (ProjectiveLine S) := ⟨⟩
  let hP : IsUnit (N : Γ(ProjectiveLine S, ⊤)) := ordinaryFiniteP1_isUnit N S hS
  let hPP : IsUnit (N : Γ(ProjectiveLine (ProjectiveLine S), ⊤)) :=
    ordinaryFiniteP1_isUnit N (ProjectiveLine S) hP
  have hbase : (projectiveLineTraceDatum N hN A hA S hS).chern =
      ordinaryFiniteFirstChern A N hA (ProjectiveLine S) hP
        (Scheme.Pic.ofIsInvertible
          (ProjectiveSpace.twist (ULift.{u} (Fin 2)) S 1)) := by
    apply ordinaryFiniteFirstChern_unique
    exact (ordinaryFiniteP1ChernSpec_iff A N hA S hP _).mp
      (projectiveLineTraceDatum N hN A hA S hS).chern_spec
  have h := ordinaryFiniteP1_diagonal_kummer_component_formula_fixed N hN A hA
    (projectiveLineTraceTransport N hN A hA) S hS hP hPP hT
    (projectiveLineTraceDatum N hN A hA (ProjectiveLine S) hP).chern
    (projectiveLineTraceDatum N hN A hA (ProjectiveLine S) hP).chern_spec hI κ hκ a
  rw [projectiveLineDiagonalChartPushforward_eq, hbase]
  have h' := h.trans (add_comm _ _)
  simp only [ordinaryFiniteP1DiagonalSupportedMap, ordinaryFiniteSupportedRealization,
    Category.assoc] at h'
  run_tac
    let g ← Lean.Elab.Tactic.getMainGoal
    g.withContext do
      let h := (← Lean.Meta.getLocalDeclFromUserName `h').toExpr
      let heq ← structuralHEq 200 (← Lean.Meta.inferType h) (← g.getType)
      let eq ← Lean.Meta.mkAppM ``eq_of_heq #[heq]
      g.assign (← Lean.Meta.mkAppM ``Eq.mp #[eq, h])
    Lean.Elab.Tactic.replaceMainGoal []

end AlgebraicGeometry.Etale
