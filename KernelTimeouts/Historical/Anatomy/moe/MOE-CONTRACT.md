# MOE Snapshot Contract (S0-S6)

This directory contains the Batch 0 mismatch-origin tooling. The contract is
line-oriented so a run can be inspected with ordinary text tools and compared
without loading a Lean environment.

## Stages

| Stage | Required record | Producer |
| --- | --- | --- |
| S0 | `MOE_SYNTAX stage=S0`, source spelling and declaration context | `#moe_elab` or the probe source |
| S1 | `MOE_SYNTAX stage=S1`, recursively macro-expanded syntax | `#moe_elab` |
| S2 | `MOE_NODE stage=S2`, every expression node on a stable path | `#moe_elab` or `#moe_pair` |
| S3 | declaration-finalization status and finalized declaration record | `#moe_decl`; imported declarations are marked observational-only |
| S4 | `MOE_CONST` metadata, stored type/value node trees, reducibility hints | `#moe_decl` |
| S5 | exact pair and `Kernel.isDefEq` result | `#moe_root` or `#moe_pair` |
| S6 | descendant nodes exposed by the selected S5 pair | kernel READY4 events plus `#moe_decl` for named constants |

`MOE_NODE` fields are `stage`, `side`, `path`, `hash`, `kind`, and `payload`.
The path uses `/fn`, `/arg`, `/domain`, `/body`, `/type`, `/value`, `/expr`,
and `/data`. The hash is Lean's structural expression hash; it is used as a
quick address, while kind, payload, and path remain the authoritative
comparison fields. Payload includes constant names, universe levels, binder
information, literal values, and projection indices.

`MOE_CONST` fields are `stage`, `side`, `name`, `status`, `kind`, `levels`,
`hints`, and `hasValue`. `hints` is exactly `abbrev`, `opaque`, or
`regular:<height>`. `MOE_AUX` records auxiliary declarations found under the
declaration namespace. It is an inventory, not a claim that every auxiliary
constant is on the selected kernel path.

For an imported declaration there is no supported API that exposes the
pre-finalization term after the `.olean` has been loaded. `#moe_decl` therefore
marks S3 `finalization-observable-only` and records the finalized declaration
at both S3 and S4. To obtain a true S2/S3 pair, put `#moe_elab` immediately
beside the source declaration in a scratch probe and run `#moe_decl` after the
declaration is added. This limitation is explicit in the snapshot rather than
silently treating S2 and S4 as identical.

## Provenance

Use Lean's existing trace classes around exactly one declaration or probe:

```lean
set_option trace.Meta.synthInstance true in
set_option trace.Meta.synthInstance.answer true in
set_option trace.Meta.isDefEq.assign true in
set_option trace.Meta.isDefEq.transparency true in
example ... := by
  ...
```

The `synthInstance` and `synthInstance.answer` records identify the target,
candidate route, selected declaration, and recursive instance arguments.
`isDefEq.assign` records metavariable assignment expressions and
`isDefEq.transparency` records the local transparency operation. Keep the
scope around one declaration; do not enable these classes in a shared import
tree. The S2 node path and the trace message's local context are recorded
together in the case report. Imported declarations are labelled
environment/import-frozen because current priorities cannot rewrite their
stored terms.

## Frozen replay

`#moe_root Decl` obtains the stored type (`F0` left), checks the stored value
to obtain its inferred type (`F0` right), and calls `Kernel.isDefEq` in the
same environment and local context. A perturbation is replayed by placing the
perturbed expression in a scratch declaration with the same imports and
options, then running `#moe_pair` or `#moe_root` (`F1`). Kernel metadata-only
controls use two scratch declarations with identical expressions and different
`ReducibilityHints`; they are reported as F2. The replay keeps universe
levels, declaration providers, environment imports, and options unchanged
except for the explicitly named control.

## Stable comparison

```sh
python3 moe_compare.py left.snapshot right.snapshot
python3 moe_compare.py a.snapshot b.snapshot --stage S4 --left-side L --right-side L
```

The comparer walks paths in preorder and reports the first missing path, kind,
universe/binder payload, or structural-hash difference. It also reports
changed `MOE_CONST` metadata. A timing difference without a changed S2/S4
pair or hint is not classified as an origin change.
