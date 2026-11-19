/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.TraceFormula.Scalar.ScalarModelRoosZeroLiftCore
import all WeilConjectures.TraceFormula.Scalar.ScalarModelRoosZeroLiftCore
import all WeilConjectures.SixFunctors.Scalar.ScalarRoosComparison
import all WeilConjectures.TraceFormula.Supporting.FiniteFreeCompletedScalarComparison
import WeilConjectures.TraceFormula.Scalar.ScalarModelRoosZeroLiftUniqueness
import WeilConjectures.TraceFormula.Scalar.ScalarModelRoosCounitNormalization

/-! # Factorization from normalized scalar Roos coordinates -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace WeilConjectures

open Lean Meta Elab Tactic

set_option maxHeartbeats 10000000
set_option linter.unusedTactic false

private meta def counitPP (e : Expr) : MetaM String := do
  let fmt ← withOptions (fun o => pp.explicit.set (pp.universes.set (pp.maxSteps.set o 1000) true) true)
    (ppExpr e)
  return ((toString fmt).take 1200).toString

private meta partial def counitFirstDiff (a b : Expr) (path : String := "root") :
    Option (String × Expr × Expr) :=
  if a == b then none else
    match a, b with
    | .app f x, .app g y =>
      (counitFirstDiff f g (path ++ ".fn")).orElse fun _ =>
        counitFirstDiff x y (path ++ ".arg")
    | .forallE _ da ba _, .forallE _ db bb _ =>
      (counitFirstDiff da db (path ++ ".domain")).orElse fun _ =>
        counitFirstDiff ba bb (path ++ ".body")
    | .lam _ da ba _, .lam _ db bb _ =>
      (counitFirstDiff da db (path ++ ".domain")).orElse fun _ =>
        counitFirstDiff ba bb (path ++ ".body")
    | .letE _ ta va ba _, .letE _ tb vb bb _ =>
      (counitFirstDiff ta tb (path ++ ".type")).orElse fun _ =>
        (counitFirstDiff va vb (path ++ ".value")).orElse fun _ =>
          counitFirstDiff ba bb (path ++ ".body")
    | .proj na ia ea, .proj nb ib eb =>
      if na == nb && ia == ib then counitFirstDiff ea eb (path ++ ".proj")
      else some (path, a, b)
    | .mdata _ ea, .mdata _ eb => counitFirstDiff ea eb (path ++ ".mdata")
    | _, _ => some (path, a, b)

elab "counit_pair " h:term : tactic => withMainContext do
  let goal ← getMainGoal
  let proof ← elabTerm h none
  Term.synthesizeSyntheticMVarsNoPostponing
  let proof ← instantiateMVars proof
  let inferred ← instantiateMVars (← inferType proof)
  let expected ← instantiateMVars (← goal.getType)
  match counitFirstDiff inferred expected with
  | none => logInfo "types structurally equal"
  | some (path, a, b) =>
    logInfo m!"first difference: {path}"
    logInfo m!"inferred subterm: {← counitPP a}"
    logInfo m!"expected subterm: {← counitPP b}"
  let inferredArgs := inferred.getAppArgs
  let expectedArgs := expected.getAppArgs
  for i in #[1, 2] do
    match counitFirstDiff inferredArgs[i]! expectedArgs[i]! with
    | none => logInfo m!"component {i}: structurally equal"
    | some (path, a, b) =>
      logInfo m!"component {i}: first difference at {path}"
      logInfo m!"inferred: {← counitPP a}"
      logInfo m!"expected: {← counitPP b}"

attribute [local irreducible] HasDerivedCategory.standard
  integralComparisonSequenceScalarModel coefficientSequenceRestriction coefficientSequenceLimit
  integralScalarExtensionOfUniverses completedScalarChangeData

attribute [local implicit_reducible] completedOrdinaryScalarComplex integralOperationsRoos
  completedDerivedScalarExtension completedScalarCounit completedOrdinaryScalarExtension

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (F : Type u) [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
  (ι : E →ₐ[ℚ_[l]] L) (j : L →ₐ[ℚ_[l]] F) (X : Scheme.{u})

/-- Naturality of the universal cochain counit, without expanding scalar-change data.
Source: Stacks 06YY; the homotopy counit's naturality square. -/
private theorem scalarCounit_natural
    {A B : CochainComplex (integralTowerModules l L X) ℤ} (g : A ⟶ B) :
    (completedDerivedScalarExtension l L F j X).map (DerivedCategory.Q.map g) ≫
        completedScalarCounit l L F j X B =
      completedScalarCounit l L F j X A ≫
        DerivedCategory.Q.map ((completedOrdinaryScalarComplex l L F j X).map g) := by
  dsimp only [completedScalarCounit, completedOrdinaryScalarComplex]
  counit_pair homotopyCounit_naturality
    (completedOrdinaryScalarExtension.{u, u} l L F j X)
    (completedDerivedScalarExtension.{u, u} l L F j X)
    ((completedScalarChangeData.{u, u} l L F j X).choose_spec.choose_spec.choose_spec
      |>.choose_spec.2.2.choose_spec.choose) g
  sorry

end WeilConjectures
