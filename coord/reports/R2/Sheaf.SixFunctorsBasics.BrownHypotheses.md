## What changed

Added the proved public theorem
`CategoryTheory.brownHypothesesFor_iff_compact_of_admissible`. For any finite-type
scheme over any field, and any of the six admissible coefficients, it identifies
Brown's bundle with compactness of every constructible finite-Tor object in its
localizing closure. It needs neither separatedness nor a characteristic restriction.
It does not assert the missing compactness theorem.

Factored the coefficient-by-coefficient thickness/smallness argument out of the
private finite-field specialization into the proved private helper
`brownHypotheses_admissible_small`. Finite carriers still use the original explicit
`finiteCoefficientLiftIso`. Reused the public criterion in the finite-field assembly.
All original signatures, definitions, public imports and visibility are preserved.
No source-library file is changed. Restored the missing JSON node of the already-proved generic generation theorem.
Updated the item node's proof to use the criterion
and remove its obsolete claim that admissibility still has a seventh coefficient.
Removed that obsolete warning from the Lean comment as well.

## Proved and sorry left

Original holes closed: 0 of 1. Holes added: 0. Split-off holes: 0.
The new public criterion and private smallness helper are proved.
`CategoryTheory.brownHypotheses` remains the sole sorry, node
`sk-lem-brown-hypotheses`, with its original statement. This is a proved refinement
of the formal reduction and reuse of the supported finite-field proof, not a proof
of the disputed original assertion and not a claimed reduction in the hole ledger.

The first prescribed compile reached the new proof but found the previous seven-case
admissibility predicate in the server's last green compiled library. The shared source
already has the human-authorized six-case definition. No copy or substitute of that
landed definition was written; the final version instead uses the existing explicit six-case coefficient interface
of the compactness theorem. This is the same coefficient range and needs no new
predicate, definition, or imported declaration. The final standalone compile passed cleanly through the prescribed lcompile.py in
56.7 seconds (exit 0, no diagnostics). The delivery tool performs its own compile
and axiom probe before pushing.

## No longer needed

No imports, nodes or modules are pruned. The smallness, structural, finite-field
compactness and generic generation dependencies all remain needed. All public imports
are unchanged, as are the restored and quarantined parent dependencies. The new proof
uses the existing explicit six-case compactness interface and does not import any all-continuous algebraic-
closure comparison module. The duplicated private coefficient case proof was factored
out and is now reused rather than repeated.

## Where the brief, the DAG or earlier work was wrong

STATEMENT-DISPUTED: the arbitrary-field compactness assertion still lacks the base-field
finiteness or cohomological bound needed by its geometric dependencies. The conditional
Ext obstructions in the module are already proved; no field-cohomology counterexample
is claimed here. Adding an unproved arbitrary-field compactness theorem would merely
move the unsupported hole, so no such assertion is added.

The earlier all-continuous coefficient warning is stale: the human removed that case
from `IsLocalizingAdmissibleCoefficient` on 2026-10-25. The six remaining alternatives
are covered by the thickness/smallness theorem; the new criterion checks them all.
Its explicit hypothesis retains the existing finite-field compactness interface
(finite, Z_l, O_E, Q_l, E, finite-subextension Qbar_l). The current admissibility
predicate lists the same cases in a different order; it is not unfolded here.

The pre-existing references to `lem-sfb-localizing-closure-generators` pointed to an
absent JSON node, although its public theorem and matching blueprint tag were present.
Restored that missing node, attaching the already-proved declaration verbatim; no
second theorem or new proof hole is introduced. The formal criterion is unchanged.

Edge cases: the empty scheme and zero ring are allowed; compactness is not inferred
from thickness. Finite rings need not be fields. The ULift carrier identification is
explicit and preserves ring structure. Arbitrary characteristic and nonseparated
finite-type schemes are allowed in the criterion. Both sides retain the coproduct
witness in the fixed universe, and generation uses the inherited canonical shift.

## New nodes

`lem-sfb-brown-admissible-compactness-criterion` records the new proved criterion.
It uses the existing coefficient smallness theorem and formal Brown criterion;
its proof contains no new hole. It realizes the first two paragraphs of the original
unit and preserves their route. The node records all three searches actually run.

Change record: `coord/changes/R2-brown-admissible-compactness-criterion.md`.

`lem-sfb-localizing-closure-generators` restores the absent node already cited by the
item and formal criterion. It attaches the existing complete public theorem, whose
statement and proof are unchanged. The search records distinguish this exact project
match from the Mathlib orthogonality tools.

## Second reading by R2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
