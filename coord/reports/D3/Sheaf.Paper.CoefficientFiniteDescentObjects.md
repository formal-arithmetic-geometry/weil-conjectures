## What changed

Restored `lean/Sheaf/Paper/CoefficientFiniteDescentObjects.lean` verbatim from
`quarantine/Sheaf/Paper/CoefficientFiniteDescentObjects.lean`, as required by its current
`coord/rework.tsv` entry. The module was reverted after a cluster restore; its archived
proof is already complete and compiles against the current server library. This packet
restores the missing declaration, rather than claiming a new proof of an existing hole.

The existing public signature, four public imports, two proved private comparison helpers,
ordinary proof imports and visibility are preserved. The existing change record
`coord/changes/coefficient-finite-descent-objects-proof-commands.md` already documents the
proof's namespace openings and unchanged consumers. No new interface change or adaptation
is needed. The existing DAG attachment and proof dependencies are preserved without edits.

The argument compares finite constant local models with stratified local finite presentation
on Noetherian schemes. It applies the existing same-unit `constructibleCocone_essSurjObj`
to obtain the finite coefficient model, then uses
`boundedConstructible_derivedExtendScalarsSubfield_obj` and `derivedExtendScalarsCompIso`
for persistence under finite enlargement. Its two comparison helpers are proved in full.

Validation: `lcompile.py` compiled the restored file without errors or warnings (10.7 seconds).
Read the node, its dependency declarations, unit record, source statement and source proof.
LeanFinder, Loogle and Mathlib grep found no shorter replacement. The existing route already
reuses the library's object-descent theorem in the same unit. Rank zero, the empty scheme,
and the identity field enlargement require no extra hypotheses.

## Proved and sorry left

Restoration of the already proved
`AlgebraicGeometry.ProEtale.coefficient_finite_descent_objects`
(node `det-lem-coefficient-finite-descent-objects`), including its private proved helpers
`free_hasConstantModel` and `constantModel_eq_of_localFree`.

Actual local hole count: zero before restoration in the archived module, zero after.
New holes closed in this session: zero. Holes added: zero. Split-off statements: zero.
No `sorry` remains in the restored module. Existing imported proof obligations are unchanged;
this packet does not claim to discharge them.

## No longer needed

None newly pruned. All archived imports and existing node dependencies are retained.
The module is not withdrawn: it remains required by the DAG's parent finite-coefficient
descent argument even while related parents are quarantined.

## Where the brief, the DAG or earlier work was wrong

The live Lean source is absent, but the rework entry explicitly preserves the complete
module in quarantine. Its absence is not withdrawal and does not justify deleting its
attachment. Restoring the archived source fixes this rework item with zero local holes.
The existing node's proof already describes the restored Lean route accurately; the older
five-step docstring is the original source plan, whose induction is reused through the
same-unit library object-descent theorem. No statement, definition, target or unit route
has been changed.

## Second reading by D3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
