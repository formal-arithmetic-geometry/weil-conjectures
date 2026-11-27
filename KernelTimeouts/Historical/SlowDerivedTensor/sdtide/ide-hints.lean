import WeilConjectures.SixFunctors.Etale.Derived.Tensor

open Lean Elab Command Meta

private def create (n : Name) (height : Nat) : CommandElabM Unit := do
  let decl : Declaration := .defnDecl {
    name := n, levelParams := [], type := mkConst ``Nat,
    value := mkNatLit 7, hints := .regular height.toUInt32, safety := .safe }
  liftCoreM <| addDecl decl
  let some (.defnInfo saved) := (← getEnv).find? n | throwError "missing control"
  let result := Kernel.check (← getEnv) default saved.value
  logInfo m!"[IDE-HINT] name={n} requested={height} kernelCheck={result.isOk}"

run_cmd do
  create `ideHint24 24
  create `ideHint25 25
  create `ideHint25Equal 25
  create `ideHint24Equal 24
  let env ← getEnv
  for (label, a, b) in #[("original-order", `ideHint24, `ideHint25),
      ("equal-25", `ideHint25, `ideHint25Equal),
      ("swapped", `ideHint25, `ideHint24),
      ("equal-24", `ideHint24, `ideHint24Equal)] do
    let x := mkConst a
    let y := mkConst b
    let t0 ← IO.monoMsNow
    let r := Kernel.isDefEq env default x y
    let t1 ← IO.monoMsNow
    let answer := match r with | .ok v => s!"{v}" | .error _ => "error"
    logInfo m!"[IDE-HINT-CMP] {label} structural={x == y} defeq={answer} ms={t1-t0}"
