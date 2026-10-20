## What changed

Restored `lean/Sheaf/Paper/IntegralConstantModelHeartClosure.lean` from the exact
quarantine source named in `coord/rework.tsv`. Added two proof-only imports:
`Mathlib.CategoryTheory.ObjectProperty.Kernels` and
`Mathlib.CategoryTheory.ObjectProperty.Extensions`. The upstream-sync failure at
`obtain ⟨hk, hc, he⟩ := integralConstructible_serre ℓ E.val X` was caused by the
closure classes not being available in this module's proof context. Naming the
first projection instead exposed the underlying unknown-constant diagnostic.
Explicit imports repair the original proof without changing any declaration,
public import, definition, signature, or DAG dependency.

Single-file server compile: clean, 11.5 seconds. The existing proof still uses
the explicit integral coefficient isomorphism, finite-presentation and
constructibility transport, `integralLfpConstantModelComparison`, and
`integralConstructible_serre`. The unit route and existing node attachment stay
unchanged. Change record:
`coord/changes/B4-integral-constant-heart-closure-restoration.md`.

## Proved and sorry left

Assigned repair completed for
`AlgebraicGeometry.ProEtale.isConstantModelConstructible_serre_padicIntegers`.
The quarantined baseline has zero holes; the restored module has zero holes.
Holes closed: 0. Holes added: 0. Split off: 0. Every existing private helper
and the public theorem retain their complete proofs. No `sorry` remains in the
item or is added elsewhere.

## No longer needed

None. No imports, declarations, modules, node attachments, or proof dependencies
were removed. The absent live file was quarantined, not withdrawn. All original
public and proof imports are retained. The two new imports supply the closure
classes and API used by the existing final proof.

## Where the brief, the DAG or earlier work was wrong

The assigned rework is a zero-hole compile repair, not a new mathematical proof.
The inherited proof relied on transitive availability of Mathlib object-property
closure classes; after upstream synchronization those names were unavailable.
The initial `generalize` diagnostic concealed the missing constant. Explicit
proof imports fix it. The original mathematical argument and DAG remain valid.

`tools/downstream.py` cannot inventory a module absent from live `lean/` and
reports "unknown module(s)". Direct source searches across `lean/` and
`quarantine/` found the seven archived importers listed in the change record.
All use the identical restored interface, so none needs adaptation. No source
or quarantine file in the shared repository was modified.

## Second reading by B4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
