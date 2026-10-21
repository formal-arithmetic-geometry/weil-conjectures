## What changed

Restored `lean/Sheaf/Paper/ExtensionZeroStratifiedPerfect.lean` from its assigned quarantine
archive. Updated the private `extendStratification` type from the removed
`LocallyClosedStratification` to the current `Scheme.Stratification` used by
`IsIntegralStratifiedPerfect`. Removed the empty old compatibility import. All remaining Lean
lines, including the complete public theorem, are verbatim from the archive.

Updated the existing node's proof description and proof_origin to record this interface
migration; the attachment, statement and proof dependencies are unchanged. Change record:
`coord/changes/P6-extension-zero-stratification-upstream-name.md`.

Validation: the restored module compiles through lcompile.py with no errors or warnings
(4.4 seconds after removing the obsolete import). Its lines satisfy the 100-column limit.
The public theorem signature was compared verbatim with the quarantine archive. The source
consumer traversal includes quarantined modules: 28 downstream consumers, no adaptations.
The construction covers empty open or closed complements and zero original strata; the
Fin.cases construction and zero perfect model impose no nonemptiness condition.

## Proved and sorry left

This is a zero-hole repair. The archive contained zero sorry occurrences; the restored
module contains zero. Closed: none. Added: none. Split off: none. The public theorem
`AlgebraicGeometry.Scheme.cbc_extension_zero_stratified_perfect` and its four proved private
helpers/constructions are restored with their existing complete proofs. No claim of a newly
closed hole is made. Dependencies may still contain their own existing holes.

## No longer needed

Removed the archived public import `Sheaf.AlgebraicGeometry.LocallyClosedStratification`,
which is now an empty withdrawn module. No mathematical node or proof dependency is pruned;
the finite stratification, local-model transport, closed vanishing and zero perfect model
arguments remain needed. No source-library declaration is removed. The current
stratification type is already available through the remaining public imports.

## Where the brief, the DAG or earlier work was wrong

The item is an assigned restoration with zero holes, not a fresh unproved theorem. Its
rework row records the unknown old stratification identifier after the upstream sync. The
quarantine archive was preserved and used as the baseline. The current predicate already
uses Scheme.Stratification; the repair aligns its private constructor with that interface.
The DAG's finite locally closed notion and this constructible-stratum presentation agree
under the existing Noetherian hypotheses, with constructibility explicitly proved.

Search before repair: leanfinder for extension by zero preserving perfect stratified models
returned only general scheme/complex results; loogle did not index the project's Stratification
name; msearch grep and direct source searches located the current Scheme.Stratification and
the predicate using it. The archived complete proof is the shortest existing route and was
retained. The unit sk-prop-sf-cbc has no realized step bypassed by this repair. No new nodes,
new statements, definition changes, or forced adaptations were needed.

## Second reading by P6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
