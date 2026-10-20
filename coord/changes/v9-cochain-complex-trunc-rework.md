# CochainComplex.CochainComplexTrunc_mono

## Reason

Restore the sync-quarantined companion module at its original library path.
Its extraction left orphaned scoped commands after deleting declarations already
present upstream. Compiling the original reproduces redundant binder annotations
and an unmatched namespace. The repaired module compiles cleanly in 1.0 seconds on this repair retry.
This is a context repair with no change to a declaration or public import.

For the current return of delivery `792be401d1`, re-read the current shared
checkout and the rework row. The live path is absent and the current source
is still its quarantine file. Reapplied the context repair to that current
source. Compiling the current original again fails in 1.0 seconds at lines
41, 42, 43 and 48, with style warnings. The repaired module compiles without
warnings in 1.0 seconds. No declaration or public import changes.

## Old

The instance is retained verbatim:

```lean
instance CochainComplexTrunc_mono (n : ℤ) : Mono (K.ιTruncLE n) := by
  dsimp only [ιTruncLE]
  infer_instance
```

It was followed by this detached context:

```lean
namespace truncLELEIsoOfLE

end truncLELEIsoOfLE

variable {K L} in
set_option backward.defeqAttrib.useBackward true in
set_option backward.defeqAttrib.useBackward true in
set_option backward.defeqAttrib.useBackward true in
variable (C) in
variable {K L} in
variable {K L} in
variable (C)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency false in
end CochainComplex
```

## New

The instance remains verbatim:

```lean
instance CochainComplexTrunc_mono (n : ℤ) : Mono (K.ιTruncLE n) := by
  dsimp only [ιTruncLE]
  infer_instance
```

It is followed directly by `end CochainComplex`. All four public imports are
preserved. The extraction module comment is wrapped to at most 100 characters.
No source-library module or target statement changes. There is no attached DAG node.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.UpstreamExtra.WeilConjectures.FromJoel.Algebra.Homology.Embedding.CochainComplexTrunc | V9 | Restored with the same public API; orphaned commands removed. |

A search of `lean/Sheaf`, `lean/WeilConjectures`, `quarantine`, and `dag/nodes`
found no direct importer, named reference to the instance, or attached node.
No consumers require adaptation. The downstream script reports the
quarantined module as unknown, so the consumer checks use direct ripgrep
searches in the live library, quarantine and DAG nodes instead.

## Status

landed 20261020T145546-L-2412122 2026-10-20 (merge of deliver/V9/Sheaf.UpstreamExtra.WeilConjectures.FromJoel.Algebra.Homology.Embedding.CochainComplexTrunc)
