module

public import WeilConjectures.Tactic.ExactModProofs

public meta section

open Lean Meta Elab Tactic

partial def traceFirstProofMismatch (a b : Expr) (remaining : IO.Ref Nat) : MetaM Unit := do
  if a == b then return
  match a, b with
  | .app .., .app .. =>
    let fa := a.getAppFn
    let fb := b.getAppFn
    let aa := a.getAppArgs
    let bb := b.getAppArgs
    if fa == fb && aa.size == bb.size then
      for i in [:aa.size] do
        try
          traceFirstProofMismatch aa[i]! bb[i]! remaining
        catch err =>
          let n ← remaining.get
          if n > 0 then
            remaining.set (n - 1)
            throwError m!"{err.toMessageData}\nMismatch parent argument {i} of {fa}:\nLEFT {a}\nRIGHT {b}"
          throw err
      return
  | _, _ => pure ()
  if (← isProof a) then return
  if (← isDefEq a b) then return
  throwError "First mismatch: {a}\nversus {b}"

elab "trace_proof_mismatch " h:term : tactic => withMainContext do
  let e ← elabTerm h none
  let H := ExactModProofs.stripMData (← instantiateMVars (← inferType e))
  let G := ExactModProofs.stripMData (← instantiateMVars (← getMainTarget))
  let remaining ← IO.mkRef 6
  try traceFirstProofMismatch H G remaining
  catch err => logInfo err.toMessageData
