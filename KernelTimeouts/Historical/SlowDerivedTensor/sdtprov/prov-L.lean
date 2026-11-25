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

private partial def firstDiff (a b : Expr) (path : String := "root") : String :=
  if a == b then s!"{path}:equal" else
  match a, b with
  | .app f x, .app g y =>
    if f == g then firstDiff x y (path ++ "/arg") else firstDiff f g (path ++ "/fn")
  | .lam _ d x _, .lam _ e y _ =>
    if d == e then firstDiff x y (path ++ "/body") else firstDiff d e (path ++ "/domain")
  | .forallE _ d x _, .forallE _ e y _ =>
    if d == e then firstDiff x y (path ++ "/body") else firstDiff d e (path ++ "/domain")
  | .letE _ t v x _, .letE _ u w y _ =>
    if t != u then firstDiff t u (path ++ "/type")
    else if v != w then firstDiff v w (path ++ "/value")
    else firstDiff x y (path ++ "/body")
  | .proj _ _ x, .proj _ _ y => firstDiff x y (path ++ "/proj")
  | .mdata _ x, .mdata _ y => firstDiff x y (path ++ "/mdata")
  | _, _ => s!"{path}: {h a} [{a.hash}] | {h b} [{b.hash}]; left={a}; right={b}"

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

private partial def findQuasi? (e : Expr) : Option Expr :=
  match e with
  | .const `HomotopyCategory.quasiIso _ => some e
  | .app f x => (findQuasi? f).orElse fun _ => findQuasi? x
  | .lam _ d b _ | .forallE _ d b _ =>
    (findQuasi? d).orElse fun _ => findQuasi? b
  | .letE _ t v b _ =>
    (findQuasi? t).orElse fun _ =>
      (findQuasi? v).orElse fun _ => findQuasi? b
  | .proj _ _ x | .mdata _ x => findQuasi? x
  | _ => none

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
      logInfo m!"[UAE-DIFF] source-F {firstDiff sourceA sourceB}"
      compare env "original-source-F" sourceA sourceB
      logInfo m!"[ICD] source-F-left={sourceA}"
      logInfo m!"[ICD] source-F-right={sourceB}"
      let sourceArgsA := sourceA.getAppArgs
      let sourceArgsB := sourceB.getAppArgs
      let curryArgsA := sourceArgsA[6]!.getAppArgs
      let curryArgsB := sourceArgsB[6]!.getAppArgs
      logInfo m!"[PROV] curried args={curryArgsA.size}/{curryArgsB.size}"
      for i in [0:min curryArgsA.size curryArgsB.size] do
        detail s!"curried.arg{i}" curryArgsA[i]! curryArgsB[i]!
        if curryArgsA[i]! != curryArgsB[i]! then
          logInfo m!"[PROV] curried.arg{i}.left={curryArgsA[i]!}"
          logInfo m!"[PROV] curried.arg{i}.right={curryArgsB[i]!}"
      let instA := curryArgsA[2]!
      let instB := curryArgsB[2]!
      let ia ← whnf instA
      let ib ← whnf instB
      let pa ← whnf (Expr.proj `CategoryTheory.MonoidalCategory 0 instA)
      let pb ← whnf (Expr.proj `CategoryTheory.MonoidalCategory 0 instB)
      let parentArgsA := pa.getAppArgs
      let parentArgsB := pb.getAppArgs
      let instanceArgsB := ib.getAppArgs
      let whnfPropA ← whnf propA
      let whnfPropB ← whnf propB
      let uncurryA := whnfPropA.getAppArgs[4]!
      let uncurryB := whnfPropB.getAppArgs[4]!
      let originalFieldsA := (← whnf uncurryA).getAppArgs
      logInfo m!"[L] parent={h pa}/{h pb} instance={h ia}/{h ib}"
      for (index, label) in [(2, "whiskerRight"), (1, "whiskerLeft"), (0, "tensorObj")] do
        let hybridParent := mkAppN pb.getAppFn
          (parentArgsB.set! (2 + index) parentArgsA[2 + index]!)
        let hybridInstance := mkAppN ib.getAppFn (instanceArgsB.set! 2 hybridParent)
        try
          let hybridCurried := mkAppN sourceArgsB[6]!.getAppFn
            (curryArgsB.set! 2 hybridInstance)
          let hybridSource := mkAppN sourceB.getAppFn (sourceArgsB.set! 6 hybridCurried)
          let hybridU := mkAppN uncurryB.getAppFn (uncurryB.getAppArgs.set! 5 hybridSource)
          checkWithKernel hybridU
          let hybridFields := (← whnf hybridU).getAppArgs
          logInfo m!"[L] {label} valid=true"
          compare env s!"L-{label}-U" uncurryA hybridU
          compare env s!"L-{label}-map" originalFieldsA[5]! hybridFields[5]!
          compare env s!"L-{label}-map_comp" originalFieldsA[7]! hybridFields[7]!
        catch ex => logInfo m!"[L] {label} valid=false reason={ex.toMessageData}"
      compare env "L-restored-U" uncurryA uncurryB
      return
      for i in [0:min sourceArgsA.size sourceArgsB.size] do
        detail s!"source-F.arg{i}" sourceArgsA[i]! sourceArgsB[i]!
        if sourceArgsA[i]! != sourceArgsB[i]! then
          logInfo m!"[UAE-DIFF] source-F.arg{i} {firstDiff sourceArgsA[i]! sourceArgsB[i]!}"
      for i in [6, 7] do
        let candidateA ← whnf sourceArgsA[i]!
        let candidateB ← whnf sourceArgsB[i]!
        detail s!"source-F.arg{i}-whnf" candidateA candidateB
        if i == 7 then
          logInfo m!"[ICD] source-F.arg7-whnf-type-left={← inferType candidateA}"
          logInfo m!"[ICD] source-F.arg7-whnf-type-right={← inferType candidateB}"
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
      compare env "E0-F" sourceA sourceB
      compare env "E0-U" uncurryA uncurryB
      let originalFieldsA := (← whnf uncurryA).getAppArgs
      let originalFieldsB := (← whnf uncurryB).getAppArgs
      compare env "E0-map" originalFieldsA[5]! originalFieldsB[5]!
      compare env "E0-map_comp" originalFieldsA[7]! originalFieldsB[7]!
      for i in [6] do
        let candidate := mkAppN sourceB.getAppFn (sourceArgsB.set! i sourceArgsA[i]!)
        try
          checkWithKernel candidate
          logInfo m!"[EXCL] source arg{i} valid=true"
          compare env s!"E-arg{i}-F" sourceA candidate
          let uCandidate := mkAppN uncurryB.getAppFn (uncurryB.getAppArgs.set! 5 candidate)
          checkWithKernel uCandidate
          compare env s!"E-arg{i}-U" uncurryA uCandidate
          let rightFields := (← whnf uCandidate).getAppArgs
          compare env s!"E-arg{i}-map" originalFieldsA[5]! rightFields[5]!
          compare env s!"E-arg{i}-map_comp" originalFieldsA[7]! rightFields[7]!
        catch ex => logInfo m!"[EXCL] source arg{i} valid=false reason={ex.toMessageData}"
      let locA := sourceArgsA[7]!.getAppArgs
      let locB := sourceArgsB[7]!.getAppArgs
      let locCandidate := mkAppN sourceArgsB[7]!.getAppFn
        (locB.set! 5 locA[5]!)
      let bLoc := mkAppN sourceB.getAppFn (sourceArgsB.set! 7 locCandidate)
      try
        checkWithKernel locCandidate
        checkWithKernel bLoc
        let uLoc := mkAppN uncurryB.getAppFn (uncurryB.getAppArgs.set! 5 bLoc)
        checkWithKernel uLoc
        logInfo m!"[EXCL] E3 valid=true"
        compare env "E3-F" sourceA bLoc
        compare env "E3-U" uncurryA uLoc
        let fields := (← whnf uLoc).getAppArgs
        compare env "E3-map" originalFieldsA[5]! fields[5]!
        compare env "E3-map_comp" originalFieldsA[7]! fields[7]!
      catch ex => logInfo m!"[EXCL] E3 valid=false reason={ex.toMessageData}"
      if let some leftQuasi := findQuasi? sourceArgsA[4]! then
        let mut aligned := sourceArgsB
        for i in [4, 5, 7] do
          aligned := aligned.set! i (sourceArgsB[i]!.replace fun e =>
            if e.isConstOf `HomotopyCategory.quasiIso then some leftQuasi else none)
        let bQuasi := mkAppN sourceB.getAppFn aligned
        try
          checkWithKernel bQuasi
          let uQuasi := mkAppN uncurryB.getAppFn (uncurryB.getAppArgs.set! 5 bQuasi)
          checkWithKernel uQuasi
          logInfo m!"[EXCL] E2 valid=true leftQuasi={leftQuasi}"
          compare env "E2-F" sourceA bQuasi
          compare env "E2-U" uncurryA uQuasi
          let fields := (← whnf uQuasi).getAppArgs
          compare env "E2-map" originalFieldsA[5]! fields[5]!
          compare env "E2-map_comp" originalFieldsA[7]! fields[7]!
        catch ex => logInfo m!"[EXCL] E2 valid=false reason={ex.toMessageData}"
      else logInfo m!"[EXCL] E2 missing left quasiIso constant"
      let targetArgsA := sourceArgsA[7]!.getAppArgs
      let targetArgsB := sourceArgsB[7]!.getAppArgs
      for i in [0:min targetArgsA.size targetArgsB.size] do
        detail s!"source-F.arg7.arg{i}" targetArgsA[i]! targetArgsB[i]!
      compare env "E0-restored-F" sourceA sourceB
      compare env "E0-restored-U" uncurryA uncurryB
      compare env "E0-restored-map" originalFieldsA[5]! originalFieldsB[5]!
      compare env "E0-restored-map_comp" originalFieldsA[7]! originalFieldsB[7]!
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
        if i >= 4 then logInfo m!"[UAE-DIFF] U.field{i} {firstDiff uArgsA[i]! uArgsB[i]!}"
      for i in [5, 6, 7] do
        let fieldA := uArgsA[i]!
        let fieldB := uArgsB[i]!
        detail s!"constructor-arg{i}-type" (← inferType fieldA) (← inferType fieldB)
      let compTyA ← inferType uArgsA[7]!
      let compTyB ← inferType uArgsB[7]!
      let rec walkComp (ta tb : Expr) (index fuel : Nat) : MetaM Unit := do
        match fuel with
        | 0 => pure ()
        | fuel + 1 =>
          match ta, tb with
          | .forallE n da ba _, .forallE _ db bb _ =>
            detail s!"map_comp.domain{index}" da db
            compare env s!"map_comp.domain{index}" da db
            withLocalDeclD n da fun x => walkComp (ba.instantiate1 x) (bb.instantiate1 x) (index + 1) fuel
          | _, _ =>
            detail "map_comp.conclusion" ta tb
            compare env "map_comp.conclusion" ta tb
            let aa := ta.getAppArgs
            let ab := tb.getAppArgs
            if aa.size == 3 && ab.size == 3 then
              for j in [0:3] do
                detail s!"map_comp.eq.arg{j}" aa[j]! ab[j]!
                compare env s!"map_comp.eq.arg{j}" aa[j]! ab[j]!
      pure ()
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
