## What changed

Restored `lean/Sheaf/Paper/FieldOrientationSystemComparison.lean` from the quarantine
path recorded in `coord/rework.tsv`. Removed the stale command
`attribute [-instance] WeilConjectures.scalarReductionSiteSmall`.
The declaration is now a definition registered as an instance only locally in its
own module, `Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction`; trying to
unregister it here caused the recorded build failure.

All declaration signatures and all imports are preserved. To reduce elaboration time,
the private naturality proof now specializes a generic exact-functor lemma, whose
comparison is constructed explicitly from the standard single and shift comparisons.
The rewrite runs over abstract categories instead of expanding the tower coefficients. The orientation-square proof presents
the target by composing the canonical source-heart identification with the supplied
orientation isomorphism, and uses explicit inverse cancellation instead of unrestricted
simplification. No shared definition or global transparency setting changes.
The DAG proof description records this presentation; its attachment and dependencies
remain unchanged. The module still combines
`field_orientation_comparison_data` and `field_orientation_system_rigidity`, proving
the orientation equation by shifted-heart detection and the finite Tor clauses directly.

Validation: the optimized module compiled successfully through `lcompile.py` in
36.1 seconds. Profiling options were removed afterwards for delivery. Both public
theorem signatures match the quarantine source verbatim; there are zero `sorry`
tokens and no lines over 100 characters.

Change record: `coord/changes/H1-field-orientation-system-comparison-instance-repair.md`.

## Proved and sorry left

This is a zero-hole compile repair: 0 existing holes closed and 0 new holes added.
Both `shifted_sheaf_map_ext` and `field_orientation_system_comparison` retain their
complete proofs. There is no `sorry` in the restored module.
The existing dependencies `field_orientation_comparison_data` and
`field_orientation_system_rigidity` remain in their separate modules and are not
changed or counted as proved by this delivery.

## No longer needed

No imports, declarations, nodes or dependency modules were pruned.
The obsolete instance-removal command and redundant target-heart presentation
were removed; their replacements do not prune any mathematical dependencies. The quarantine archive is
preserved, and the restored file retains the node's Lean attachment and dependencies.

## Where the brief, the DAG or earlier work was wrong

The rework row correctly identifies the failure. The archived file still assumed
that `WeilConjectures.scalarReductionSiteSmall` was a global instance. Its owner
explicitly changed it to a local instance on 2026-10-26; the restoration follows
that owner rather than changing shared typeclass registrations.
There are no current direct Lean importers of the restored module in either
`lean/Sheaf` or `quarantine`, as checked by exact import search. No consumer needs
adaptation. The unit route and mathematical statement are unchanged.

## Second reading by H1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
