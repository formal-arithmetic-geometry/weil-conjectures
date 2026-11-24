import WeilConjectures.SixFunctors.Etale.Derived.Tensor

open Lean Elab Command Meta
open CategoryTheory Limits MonoidalCategory
set_option linter.style.emptyLine false
set_option linter.style.longLine false

namespace AlgebraicGeometry
open Scheme
universe u' u

set_option debug.skipKernelTC true in
lemma icd_tensorObj_probe
    (A : Type u') [Category.{u + 1, u'} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1, u + 1, u'} A] [MonoidalCategory A]
    [MonoidalPreadditive A] [SymmetricCategory A] (X : Scheme.{u})
    [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    (K L : DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    @tensorObj (DerivedCategory (Sheaf X.smallEtaleTopology A)) _ inferInstance K L =
    @tensorObj (DerivedMonoidal DerivedCategory.Qh
      (HomotopyCategory.quasiIso (Sheaf X.smallEtaleTopology A) (ComplexShape.up ℤ)))
      _ inferInstance K L := by
  rfl

private def h (e : Expr) : String :=
  match e.getAppFn with
  | .const n _ => s!"{n}/{e.getAppNumArgs}"
  | .proj n i _ => s!"proj {n}.{i}"
  | .fvar _ => s!"fvar/{e.getAppNumArgs}"
  | .lam .. => "lam"
  | .forallE .. => "forall"
  | f => s!"{f.ctorName}/{e.getAppNumArgs}"

private def detail (label : String) (a b : Expr) : MetaM Unit := do
  logInfo m!"[ICD] {label} head={h a} | {h b} hash={a.hash}/{b.hash} size={a.sizeWithoutSharing}/{b.sizeWithoutSharing} ptr={a.equal b}"
  try
    let ta ← inferType a
    let tb ← inferType b
    logInfo m!"[ICD] {label} type={h ta} | {h tb} typeHash={ta.hash}/{tb.hash} typeSize={ta.sizeWithoutSharing}/{tb.sizeWithoutSharing}"
  catch _ => pure ()

private def compare (env : Environment) (label : String) (a b : Expr) : MetaM Unit := do
  let t0 ← IO.monoMsNow
  let r := Kernel.isDefEq env (← getLCtx) a b
  let result := match r with
    | .ok value => s!"{value}"
    | .error _ => "error"
  let t1 ← IO.monoMsNow
  logInfo m!"[ICD-COMPARE] {label} result={result} wall_ms={t1-t0}"

private def extract (env : Environment) (a b : Expr) : MetaM Unit := do
  let leftProvider := (a.getAppArgs[2]!).getAppArgs[2]!
  let rightProvider := (b.getAppArgs[2]!).getAppArgs[2]!
  let leftParent ← whnf leftProvider
  let rightParent ← whnf rightProvider
  let leftField := leftParent.getAppArgs[2]!
  let rightField := rightParent.getAppArgs[2]!
  detail "tensorObj" leftField rightField
  let rec bind (a b : Expr) (n : Nat) : MetaM Unit := do
    match n with
    | 0 =>
      detail "object-body" a b
      let as := a.getAppArgs
      let bs := b.getAppArgs
      logInfo m!"[ICD] body args={as.size}/{bs.size}"
      for i in [0:min as.size bs.size] do
        detail s!"body.arg{i}" as[i]! bs[i]!
      let fnA := a.getAppFn
      let fnB := b.getAppFn
      detail "body.fn" fnA fnB
      let fa := fnA.getAppArgs
      let fb := fnB.getAppArgs
      logInfo m!"[ICD] body.fn args={fa.size}/{fb.size}"
      for i in [0:min fa.size fb.size] do
        detail s!"body.fn.arg{i}" fa[i]! fb[i]!
      let rec spine (x y : Expr) (n : Nat) : MetaM Unit := do
        match n with
        | 0 => pure ()
        | n+1 =>
          let xs := x.getAppArgs
          let ys := y.getAppArgs
          logInfo m!"[ICD] spine level={n} argc={xs.size}/{ys.size}"
          for j in [0:min xs.size ys.size] do
            detail s!"spine.{n}.arg{j}" xs[j]! ys[j]!
          if xs.size > 4 && ys.size > 4 then spine xs[4]! ys[4]! n
      spine a b 4
      let bifA := (as[4]!).getAppArgs[4]!
      let bifB := (bs[4]!).getAppArgs[4]!
      let proofA := bifA.getAppArgs[9]!
      let proofB := bifB.getAppArgs[9]!
      let propA ← inferType proofA
      let propB ← inferType proofB
      detail "existence-proof" proofA proofB
      detail "existence-type" propA propB
      let psA := propA.getAppArgs
      let psB := propB.getAppArgs
      for i in [0:min psA.size psB.size] do
        detail s!"existence-type.arg{i}" psA[i]! psB[i]!
      let sourceA := psA[6]!
      let sourceB := psB[6]!
      detail "source-F" sourceA sourceB
      logInfo m!"[ICD] source-F-left={sourceA}"
      logInfo m!"[ICD] source-F-right={sourceB}"
      let leftDerivedA ← unfoldDefinition bifA
      let leftDerivedB ← unfoldDefinition bifB
      detail "leftDerived2-term" leftDerivedA leftDerivedB
      let curryA ← unfoldDefinition leftDerivedA
      let curryB ← unfoldDefinition leftDerivedB
      detail "curry-term" curryA curryB
      let csA := curryA.getAppArgs
      let csB := curryB.getAppArgs
      for i in [0:min csA.size csB.size] do
        detail s!"curry-term.arg{i}" csA[i]! csB[i]!
      let chosenA := csA[5]!
      let chosenB := csB[5]!
      detail "chosen-G" chosenA chosenB
      let gsA := chosenA.getAppArgs
      let gsB := chosenB.getAppArgs
      for i in [0:min gsA.size gsB.size] do
        detail s!"chosen-G.arg{i}" gsA[i]! gsB[i]!
      let chosenUnfA ← unfoldDefinition chosenA
      let chosenUnfB ← unfoldDefinition chosenB
      detail "chosen-G-unfold" chosenUnfA chosenUnfB
      logInfo m!"[ICD] chosen-G-unfold-left={chosenUnfA}"
      logInfo m!"[ICD] chosen-G-unfold-right={chosenUnfB}"
      let rightA := match chosenUnfA with
        | .letE _ _ value body _ => body.instantiate1 value
        | e => e
      let rightB := match chosenUnfB with
        | .letE _ _ value body _ => body.instantiate1 value
        | e => e
      detail "rightKanExtension" rightA rightB
      logInfo m!"[ICD] rightKanExtension-left={rightA}"
      let rightUnfA ← unfoldDefinition rightA
      let rightUnfB ← unfoldDefinition rightB
      detail "rightKanExtension-unfold" rightUnfA rightUnfB
      logInfo m!"[ICD] rightKanExtension-unfold-left={rightUnfA}"
      let terminalA := match rightUnfA with
        | .proj _ _ e => e
        | e => e
      let terminalB := match rightUnfB with
        | .proj _ _ e => e
        | e => e
      detail "selected-terminal" terminalA terminalB
      logInfo m!"[ICD] selected-terminal-left={terminalA}"
      let propWhnfA ← whnf propA
      let propWhnfB ← whnf propB
      detail "existence-whnf" propWhnfA propWhnfB
      let wsA := propWhnfA.getAppArgs
      let wsB := propWhnfB.getAppArgs
      for i in [0:min wsA.size wsB.size] do
        detail s!"existence-whnf.arg{i}" wsA[i]! wsB[i]!
      let uncurryA := wsA[4]!
      let uncurryB := wsB[4]!
      detail "uncurried-U" uncurryA uncurryB
      let uMkA ← whnf uncurryA
      let uMkB ← whnf uncurryB
      detail "uncurried-Functor.mk" uMkA uMkB
      let uTypeA ← inferType uMkA
      let uTypeB ← inferType uMkB
      detail "constructor-result-type" uTypeA uTypeB
      let typeArgsA := uTypeA.getAppArgs
      let typeArgsB := uTypeB.getAppArgs
      for i in [0:min typeArgsA.size typeArgsB.size] do
        detail s!"constructor-result-type.arg{i}" typeArgsA[i]! typeArgsB[i]!
      let uArgsA := uMkA.getAppArgs
      let uArgsB := uMkB.getAppArgs
      for i in [0:min uArgsA.size uArgsB.size] do
        detail s!"uncurried-Functor.mk.arg{i}" uArgsA[i]! uArgsB[i]!
      for i in [5, 6, 7] do
        let fieldA := uArgsA[i]!
        let fieldB := uArgsB[i]!
        detail s!"constructor-arg{i}-type" (← inferType fieldA) (← inferType fieldB)
      let rightProofA := Expr.proj `CategoryTheory.Functor.HasLeftDerivedFunctor 0 proofA
      let rightProofB := Expr.proj `CategoryTheory.Functor.HasLeftDerivedFunctor 0 proofB
      detail "HasRightKanExtension-witness" rightProofA rightProofB
      let hasRightA ← inferType rightProofA
      let hasRightB ← inferType rightProofB
      detail "HasRightKanExtension-type" hasRightA hasRightB
      let hasTerminalA ← whnf hasRightA
      let hasTerminalB ← whnf hasRightB
      detail "HasTerminal-type" hasTerminalA hasTerminalB
      let tsA := hasTerminalA.getAppArgs
      let tsB := hasTerminalB.getAppArgs
      for i in [0:min tsA.size tsB.size] do
        detail s!"HasTerminal.arg{i}" tsA[i]! tsB[i]!
    | n+1 =>
      match a, b with
      | .lam name ty body _, .lam _ _ body' _ =>
        withLocalDeclD name ty fun x => bind (body.instantiate1 x) (body'.instantiate1 x) n
      | _, _ => throwError "not two lambdas"
  bind leftField rightField 2

set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  logInfo m!"[ICD] Functor fields={getStructureFields env `CategoryTheory.Functor}"
  let some info := env.find? ``icd_tensorObj_probe | throwError "missing probe"
  let inferred ← match Kernel.check env default (info.value! true) with
    | .ok ty => pure ty
    | .error _ => throwError "check failed"
  let rec bind (a b : Expr) (n : Nat) : MetaM Unit := do
    match n with
    | 0 => extract env a b
    | n+1 =>
      match a, b with
      | .forallE name ty body _, .forallE _ _ body' _ =>
        withLocalDeclD name ty fun x => bind (body.instantiate1 x) (body'.instantiate1 x) n
      | _, _ => throwError "not two forall binders"
  liftTermElabM <| bind inferred info.type 12

end AlgebraicGeometry
