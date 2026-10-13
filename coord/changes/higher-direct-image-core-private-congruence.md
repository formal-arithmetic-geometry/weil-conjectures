# AlgebraicGeometry.Etale.congrProofs (private metaprogram)

## Reason

The complete proof previously exceeded the kernel-checking time limit when
converting between the definitionally equal presentations of derived objects.
The private congruence metaprogram constructs explicit heterogeneous congruence
proofs, using proof irrelevance for proposition-valued instance arguments and
head normalization for projections and composite-functor objects. The final
proof passes compilation and the axiom probe.

The preflight's source-level interface parser does not recognize `private meta
 def` (written on one line in Lean). It consequently records this private helper
as a changed command rather than excluding it as a private declaration. This
record reports the classifier limitation for the independent reader. No public
definition, statement, import, notation, instance or attribute changes. No tool
was edited or bypassed. This is a proof-only semantic change, though the scanner
requests this record and classifies the delivery CODEX.

## Old

No `congrProofs` declaration. The original public theorem had its unchanged
signature and proof `:= by sorry`.

## New

The public theorem has the same signature and now a kernel-checked proof.
The newly added helper, invisible to importers, is exactly:

```lean
private meta def congrProofs : Nat → Lean.Expr → Lean.Expr → Lean.MetaM Lean.Expr
  | 0, a, b => do
    throwError "congruence depth exhausted: {a} versus {b}"
  | n + 1, a, b => do
    let a := a.consumeMData
    let b := b.consumeMData
    if a == b then
      return ← Lean.Meta.mkHEqRefl a
    if (← Lean.Meta.isProof a) && (← Lean.Meta.isProof b) then
      return ← Lean.Meta.mkAppM ``proof_irrel_heq #[a, b]
    let expandProjection (e : Lean.Expr) : Lean.MetaM Lean.Expr := do
      let fn := e.getAppFn
      let .proj typeName index major := fn | return e
      let info := Lean.getStructureInfo (← Lean.getEnv) typeName
      let p ← Lean.Meta.mkProjection major info.fieldNames[index]!
      return Lean.mkAppN p e.getAppArgs
    let a' ← expandProjection a
    let b' ← expandProjection b
    if a != a' || b != b' then
      return ← congrProofs n a' b'
    let af := a.getAppFn
    let bf := b.getAppFn
    let aa := a.getAppArgs
    let ba := b.getAppArgs
    if af != bf || aa.size != ba.size then
      let isProjection (f : Lean.Expr) : Lean.MetaM Bool := do
        if f.isConst then
          return (← Lean.getProjectionFnInfo? f.constName!).isSome
        return false
      if !(← isProjection af) then
        if let some a' ← Lean.Meta.unfoldDefinition? a (ignoreTransparency := true) then
          return ← congrProofs n a' b
      if !(← isProjection bf) then
        if let some b' ← Lean.Meta.unfoldDefinition? b (ignoreTransparency := true) then
          return ← congrProofs n a b'
      throwError "different congruence heads: {a} versus {b}"
    let expandCompositeObj (e : Lean.Expr) : Lean.MetaM Lean.Expr := do
      let args := e.getAppArgs
      if e.isAppOf ``CategoryTheory.Functor.obj && args.size ≥ 2 then
        let functor := args[args.size - 2]!
        if functor.isAppOf ``CategoryTheory.Functor.comp then
          let fs := functor.getAppArgs
          let x ← Lean.Meta.mkAppM ``CategoryTheory.Functor.obj
            #[fs[fs.size - 2]!, args.back!]
          return ← Lean.Meta.mkAppM ``CategoryTheory.Functor.obj #[fs.back!, x]
      return e
    let a' ← expandCompositeObj a
    let b' ← expandCompositeObj b
    if a != a' || b != b' then
      return ← congrProofs n a' b'
    let mut first := 0
    while first < aa.size && aa[first]! == ba[first]! do
      first := first + 1
    let f := Lean.mkAppN af (aa.extract 0 first)
    let ct ← Lean.Meta.mkHCongrWithArity f (aa.size - first)
    let mut args := #[]
    for i in [first:aa.size] do
      let h ← congrProofs n aa[i]! ba[i]!
      let h ← if ct.argKinds[i - first]! == .eq then
        Lean.Meta.mkEqOfHEq h else pure h
      args := args.push aa[i]! |>.push ba[i]! |>.push h
    return Lean.mkAppN ct.proof args
```

## Users

`tools/downstream.py` finds no use of `congrProofs`, as expected for a private
helper. The public theorem's signature and mathematical meaning are unchanged.
No user needs an adaptation. The existing users of the public theorem are listed
below from the read-only source search; all remain unaffected.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.HigherDirectImageTransitionComposition | unclaimed | Identical public signature and meaning. |
| Sheaf.AlgebraicGeometry.HigherDirectImageTransitionCoreComposition | T3 | Identical public signature and meaning. |

## Status

landed 20261013T181122-L-2607011 2026-10-13 (merge of deliver/T3/Sheaf.AlgebraicGeometry.HigherDirectImageTransitionCoreComposition)
