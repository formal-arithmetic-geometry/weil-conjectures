# AlgebraicGeometry.Scheme.ProEt.Proetale_hasIsos

## Reason

Restore the quarantined pro-etale extra module after the scheduled sync left orphan
scoped commands. This is a syntax repair. All existing public imports and all three
instance signatures and proofs are retained. The source-library module is untouched.

Repair of returned delivery `f2bfe446d0`: its base `e0d550965` predated another write
to the live module. On this retry, the current server has no live module at that path;
its quarantined source matches the shared checkout byte for byte (SHA-256
`fff5a13e7bb54695825110ba965723dcc1fd53948052f86b7c844efaa4761b1f`). Copied this current source and
reapplied the repair. Compiling the current original reproduces the line-107 scope
error; compiling the repaired version succeeds without warnings.

## Old

The following commands surrounded declarations removed during extraction:

```lean
variable (X) in
```

and, immediately before `end OverMap`:

```lean
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency.types false in
```

The preserved instance signatures, verbatim:

```lean
instance Proetale_hasIsos : (precoverage X).HasIsos := by
  dsimp [precoverage]; infer_instance

instance Proetale_isStableUnderComposition : (precoverage X).IsStableUnderComposition := by
  dsimp [precoverage]; infer_instance

instance Proetale_isStableUnderBaseChange : (precoverage X).IsStableUnderBaseChange := by
  dsimp [precoverage]; infer_instance
```

## New

Delete the four orphan scoped command prefixes. The three instance declarations above
are unchanged. Wrap the existing module comment to satisfy the line-length linter.
The restored file compiles without warnings; no statement or definition changes meaning.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.UpstreamExtra.WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale | W5 | Restore from quarantine and repair scoped command syntax; signatures unchanged. |

`tools/downstream.py` with `--allow-missing` reports zero downstream modules and zero
users of each instance name. Direct searches of live and quarantined Lean agree.
No consumers need adaptation. No target statement or definition is changed.

## Status

landed 20261020T145548-L-2413000 2026-10-20 (merge of deliver/W5/Sheaf.UpstreamExtra.WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale)
