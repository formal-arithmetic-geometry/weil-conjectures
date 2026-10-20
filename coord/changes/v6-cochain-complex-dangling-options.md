# CochainComplex.CochainComplex_mono

## Reason

Restore the quarantined stage-3 item after the 2026-10-20 upstream sync.
For the repair retry, checked the current live server source: the live Lean path
is absent, and the quarantined file still has the defect below. The sandbox was
repopulated from that current source and the failure was reproduced before repair.
Delivery c4298a9d59 was returned because the item path changed after base e0d550965.
For this retry the source was checked again on the live server and shared checkout,
and copied afresh from the current quarantine archive before applying the repair.
The extraction retained two scoped option commands whose associated lemmas now live
upstream. They incorrectly scope the closing namespace command. The original compiles
with the recorded error at line 38: `Unexpected name CochainComplex after end`.
The original also triggers the long-line linter on its generated module comment.

## Old

```lean
set_option backward.defeqAttrib.useBackward true in
set_option backward.defeqAttrib.useBackward true in
end CochainComplex
```

The retained declaration is:

```lean
instance CochainComplex_mono (n : ℤ) : Mono (K.ιTruncLE n) := by
  dsimp only [ιTruncLE]
  infer_instance
```

## New

```lean
end CochainComplex
```

The instance signature, proof, visibility, and all public imports are unchanged.
The generated module comment is wrapped without changing its text.
No definition or target statement changes.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.UpstreamExtra.WeilConjectures.FromJoel.Algebra.Homology.Embedding.CochainComplex | V6 | Restored from quarantine; now compiles. |

Textual searches of live and quarantined Lean sources find no importers of this
module and no other uses of `CochainComplex_mono`. No consumer adaptation is needed.
`tools/downstream.py --uses` reports the absent live module as unknown, so the
consumer check uses direct searches in both live and quarantined source trees.
The item has no matching DAG node; it contains only the retained proved instance.
The corresponding anonymous upstream instance remains untouched.

## Status

landed 20261020T145545-L-2411688 2026-10-20 (merge of deliver/V6/Sheaf.UpstreamExtra.WeilConjectures.FromJoel.Algebra.Homology.Embedding.CochainComplex)
