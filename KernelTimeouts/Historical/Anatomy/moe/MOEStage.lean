import Lean

/-!
  Mismatch Origin Explorer (MOE), Batch 0.

  The commands in this file are deliberately observational.  They print a
  line-oriented contract which can be retained beside a probe and compared by
  `moe_compare.py`.  The output does not contain machine paths or host names.
-/

open Lean Elab Command Meta

namespace MOE

register_option moe.maxDepth : Nat := {
  defValue := 256
  descr := "maximum expression depth printed by the MOE snapshot dumper"
}

def escape (s : String) : String :=
  s.replace "\\" "\\\\" |>.replace "\t" "\\t" |>.replace "\n" "\\n" |>.replace "\r" "\\r"

def levelText (u : Level) : String := escape (toString u)

def binderText : BinderInfo → String
  | .default => "default"
  | .implicit => "implicit"
  | .strictImplicit => "strictImplicit"
  | .instImplicit => "instImplicit"

def literalText : Literal → String
  | .natVal n => s!"nat:{n}"
  | .strVal s => s!"str:{escape s}"

def exprKind : Expr → String
  | .bvar _ => "bvar"
  | .fvar _ => "fvar"
  | .mvar _ => "mvar"
  | .sort _ => "sort"
  | .const _ _ => "const"
  | .app _ _ => "app"
  | .lam _ _ _ bi => s!"lam:{binderText bi}"
  | .forallE _ _ _ bi => s!"forall:{binderText bi}"
  | .letE _ _ _ _ _ => "let"
  | .lit _ => "lit"
  | .mdata _ _ => "mdata"
  | .proj _ _ _ => "proj"

def exprPayload : Expr → String
  | .bvar i => s!"index={i}"
  | .fvar f => s!"id={f.name}"
  | .mvar m => s!"id={m.name}"
  | .sort u => s!"level={levelText u}"
  | .const n us => s!"name={n};levels={String.intercalate "," (us.map levelText)}"
  | .app .. => ""
  | .lam n _ _ bi => s!"binder={escape n.toString};info={binderText bi}"
  | .forallE n _ _ bi => s!"binder={escape n.toString};info={binderText bi}"
  | .letE n _ _ _ nondep => s!"binder={escape n.toString};nondep={nondep}"
  | .lit l => literalText l
  | .mdata d _ => s!"data={escape (toString d)}"
  | .proj n i _ => s!"name={n};index={i}"

def exprChildren : Expr → List (String × Expr)
  | .app f a => [("fn", f), ("arg", a)]
  | .lam _ t b _ => [("domain", t), ("body", b)]
  | .forallE _ t b _ => [("domain", t), ("body", b)]
  | .letE _ t v b _ => [("type", t), ("value", v), ("body", b)]
  | .mdata _ e => [("data", e)]
  | .proj _ _ e => [("expr", e)]
  | _ => []

def emit (s : String) : IO Unit := IO.println s

partial def dumpExpr (stage side path : String) (e : Expr) (depth : Nat) : IO Unit := do
  let h := toString (hash e)
  emit s!"MOE_NODE stage={stage} side={side} path={path} hash={h} kind={exprKind e} payload={escape (exprPayload e)}"
  if depth < moe.maxDepth.get {} then
    for (label, child) in exprChildren e do
      dumpExpr stage side (path ++ "/" ++ label) child (depth + 1)

def hintsText : ReducibilityHints → String
  | .abbrev => "abbrev"
  | .opaque => "opaque"
  | .regular h => s!"regular:{h}"

def infoKind : ConstantInfo → String
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "def"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quot"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"

def dumpConstant (stage : String) (env : Environment) (side : String) (name : Name) : IO Unit := do
  match env.find? name with
  | none => emit s!"MOE_CONST stage={stage} side={side} name={name} status=missing"
  | some info =>
    emit s!"MOE_CONST stage={stage} side={side} name={name} status=present kind={infoKind info} levels={info.levelParams.length} hints={hintsText info.hints} hasValue={info.hasValue true}"
    dumpExpr stage side (s!"{name}/type") info.type 0
    if let some value := info.value? true then
      dumpExpr stage side (s!"{name}/value") value 0

def auxiliaryNames (env : Environment) (decl : Name) : List Name :=
  env.constants.toList |>.filterMap fun (name, _) =>
    let pfx := decl.toString ++ "."
    if name == decl || name.toString.startsWith pfx then some name else none

def dumpAuxiliaries (env : Environment) (decl : Name) : IO Unit := do
  for name in (auxiliaryNames env decl).toArray.qsort Name.lt do
    emit s!"MOE_AUX decl={decl} name={name}"

def dumpDecl (decl : Name) : CommandElabM Unit := do
  let env ← getEnv
  emit s!"MOE_SNAPSHOT schema=S0-S6 declaration={decl}"
  emit s!"MOE_STAGE stage=S0 status=source-required declaration={decl}"
  emit s!"MOE_STAGE stage=S1 status=source-required declaration={decl}"
  emit s!"MOE_STAGE stage=S2 status=pre-finalization-required declaration={decl}"
  emit s!"MOE_STAGE stage=S3 status=finalization-observable-only declaration={decl}"
  dumpConstant "S3" env "decl" decl
  dumpConstant "S4" env "decl" decl
  dumpAuxiliaries env decl
  emit s!"MOE_STAGE stage=S5 status=kernel-pair-required declaration={decl}"
  emit s!"MOE_STAGE stage=S6 status=kernel-descendants-from-S5 declaration={decl}"

def dumpRoot (decl : Name) : CommandElabM Unit := do
  let env ← getEnv
  let some info := env.find? decl
    | throwError m!"cannot find declaration {decl}"
  let some value := info.value? true
    | throwError m!"declaration {decl} has no value"
  let inferred ← match Kernel.check env default value with
    | .ok type => pure type
    | .error _ => throwError m!"Kernel.check failed for {decl}"
  emit s!"MOE_SNAPSHOT schema=S0-S6 root={decl}"
  dumpExpr "S4" "L" "root" info.type 0
  dumpExpr "S4" "R" "root" inferred 0
  emit s!"MOE_KERNEL stage=S5 result={(Kernel.isDefEq env default info.type inferred).isOk}"
  dumpAuxiliaries env decl

def ppSyntax (stx : Syntax) : String := escape stx.prettyPrint.pretty

def elaborateTerm (stx : Syntax) : TermElabM Expr := do
  let e ← Term.elabTerm stx none
  Term.synthesizeSyntheticMVarsNoPostponing
  instantiateMVars e

def dumpElab (stx : Syntax) : CommandElabM Unit := do
  runTermElabM fun _ => do
    let expanded ← liftMacroM <| expandMacros stx
    emit s!"MOE_SYNTAX stage=S0 text={ppSyntax stx}"
    emit s!"MOE_SYNTAX stage=S1 text={ppSyntax expanded}"
    let e ← elaborateTerm stx
    emit s!"MOE_STAGE stage=S2 status=elaborated"
    dumpExpr "S2" "term" "root" e 0

def dumpPair (leftStx rightStx : Syntax) : CommandElabM Unit := do
  runTermElabM fun _ => do
    let leftExpanded ← liftMacroM <| expandMacros leftStx
    let rightExpanded ← liftMacroM <| expandMacros rightStx
    emit s!"MOE_SYNTAX stage=S0 side=L text={ppSyntax leftStx}"
    emit s!"MOE_SYNTAX stage=S0 side=R text={ppSyntax rightStx}"
    emit s!"MOE_SYNTAX stage=S1 side=L text={ppSyntax leftExpanded}"
    emit s!"MOE_SYNTAX stage=S1 side=R text={ppSyntax rightExpanded}"
    let left ← elaborateTerm leftStx
    let right ← elaborateTerm rightStx
    emit "MOE_STAGE stage=S2 status=elaborated-pair"
    dumpExpr "S2" "L" "root" left 0
    dumpExpr "S2" "R" "root" right 0
    let env ← getEnv
    let result := Kernel.isDefEq env (← getLCtx) left right
    emit s!"MOE_KERNEL stage=S5 result={result.isOk}"

syntax (name := moeDeclCmd) "#moe_decl " ident : command
syntax (name := moeRootCmd) "#moe_root " ident : command
syntax (name := moeElabCmd) "#moe_elab " term : command
syntax (name := moePairCmd) "#moe_pair " term " ; " term : command

elab_rules : command
  | `(#moe_decl $id:ident) => dumpDecl id.getId
  | `(#moe_root $id:ident) => dumpRoot id.getId
  | `(#moe_elab $term:term) => dumpElab term
  | `(#moe_pair $left:term ; $right:term) => dumpPair left right

end MOE
