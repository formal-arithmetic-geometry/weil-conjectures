module

import all WeilConjectures.WeilSheaf.Native.NativePullTensor

open Lean Lean.Meta

set_option pp.explicit true
set_option pp.universes true
set_option pp.maxSteps 100000

partial def firstExprDiff (a b : Expr) (path : String := "root") :
    Option (String × Expr × Expr) :=
  if a == b then none else
    match a, b with
    | .app f x, .app g y =>
      (firstExprDiff f g (path ++ ".fn")).orElse fun _ =>
        firstExprDiff x y (path ++ ".arg")
    | .forallE _ da ba _, .forallE _ db bb _ =>
      (firstExprDiff da db (path ++ ".domain")).orElse fun _ =>
        firstExprDiff ba bb (path ++ ".body")
    | .lam _ da ba _, .lam _ db bb _ =>
      (firstExprDiff da db (path ++ ".domain")).orElse fun _ =>
        firstExprDiff ba bb (path ++ ".body")
    | .letE _ ta va ba _, .letE _ tb vb bb _ =>
      (firstExprDiff ta tb (path ++ ".type")).orElse fun _ =>
        (firstExprDiff va vb (path ++ ".value")).orElse fun _ =>
          firstExprDiff ba bb (path ++ ".body")
    | .proj na ia ea, .proj nb ib eb =>
      if na == nb && ia == ib then firstExprDiff ea eb (path ++ ".proj")
      else some (path, a, b)
    | .mdata _ ea, .mdata _ eb => firstExprDiff ea eb (path ++ ".mdata")
    | _, _ => some (path, a, b)

run_meta do
  let env ← getEnv
  let names := #[
    `AlgebraicGeometry.ProEtaleWeilSheaf.exists_nativePullTotalTensor,
    `AlgebraicGeometry.ProEtaleWeilSheaf.nativePullTotalTensor,
    `AlgebraicGeometry.ProEtaleWeilSheaf.nativePullTotalTensor_summands,
    `AlgebraicGeometry.ProEtaleWeilSheaf.nativeRestrictionDerivedTensor]
  for name in names do
    let info ← getConstInfo name
    let value := info.value! (allowOpaque := true)
    match Kernel.check env {} value with
    | .error _ => logInfo m!"{name}: value replay failed"
    | .ok inferred =>
      match firstExprDiff inferred info.type with
      | none => logInfo m!"{name}: structurally equal"
      | some (path, a, b) =>
        let pa ← ppExpr a
        let pb ← ppExpr b
        logInfo m!"{name}: first diff at {path}"
        logInfo m!"left: {(toString pa).take 3000}"
        logInfo m!"right: {(toString pb).take 3000}"
