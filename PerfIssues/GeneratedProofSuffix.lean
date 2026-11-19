
open Lean Lean.Meta

set_option pp.explicit true
set_option pp.universes true

private def proofShape : Expr → String
  | .app .. => "app"
  | .const n _ => s!"const {n}"
  | .proj n i _ => s!"proj {n}.{i}"
  | .lam .. => "lambda"
  | .forallE .. => "forall"
  | .letE .. => "let"
  | .mdata .. => "metadata"
  | .fvar .. => "fvar"
  | .bvar .. => "bvar"
  | .sort .. => "sort"
  | .lit .. => "literal"
  | .mvar .. => "mvar"

private partial def stripProofBinders (e : Expr) (n : Nat := 0) : Nat × Expr :=
  match e with
  | .lam _ _ b _ => stripProofBinders b (n + 1)
  | .forallE _ _ b _ => stripProofBinders b (n + 1)
  | _ => (n, e)

run_meta do
  let env ← getEnv
  for n in [1, 2, 3] do
    let name := Name.str `AlgebraicGeometry.ProEtaleWeilSheaf.powFunctor s!"_proof_{n}"
    if let some info := env.find? name then
      let value := info.value! (allowOpaque := true)
      let (typeBinders, resultType) := stripProofBinders info.type
      let (valueBinders, body) := stripProofBinders value
      logInfo m!"{name}: type binders={typeBinders}, result outer={proofShape resultType}, head={proofShape resultType.getAppFn}"
      logInfo m!"{name}: value binders={valueBinders}, body outer={proofShape body}, head={proofShape body.getAppFn}, args={body.getAppArgs.size}"
      let startValue ← IO.monoMsNow
      let checked := Kernel.check env {} value
      let stopValue ← IO.monoMsNow
      logInfo m!"{name}: Kernel.check value={stopValue - startValue} ms"
      match checked with
      | .error _ => logInfo m!"{name}: value check failed"
      | .ok inferred =>
        logInfo m!"{name}: inferred structurally equal to declared={inferred == info.type}"
        let startEq ← IO.monoMsNow
        let equal := Kernel.isDefEq env {} inferred info.type
        let stopEq ← IO.monoMsNow
        logInfo m!"{name}: final defeq={stopEq - startEq} ms, result={match equal with | .ok true => "equal" | .ok false => "unequal" | .error _ => "error"}"
