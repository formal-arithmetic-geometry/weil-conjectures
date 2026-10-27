## What changed

Proved `AlgebraicGeometry.nodalPoint_etale_locality` in
`Sheaf.AlgebraicGeometry.NodalPointEtaleLocality`, with its signature and the definition of
`Scheme.Hom.completedLocalScalarMap` unchanged. The existing
`AlgebraicGeometry.etale_completedLocalRing_iso` supplies the geometric input.
Four proved private helpers extract rational residue fields from the constant-coefficient
retraction, prove germ naturality for scalars, and upgrade the specified completed ring map
to a `k`-algebra equivalence. Composition of algebra equivalences proves the two implications;
the same geometric input gives closedness in either case.

Updated the item's DAG proof, proof dependencies and proof origin to record this shorter route.
Removed the unused private import `Mathlib.RingTheory.AdicCompletion.LocalRing`.
All public imports, public declarations, definitions and target statements are preserved.
The module's existing proof-only import of `EtaleCompletedLocalRingIso` is used.

## Proved and sorry left

Closed one hole: `AlgebraicGeometry.nodalPoint_etale_locality`
(node `lem-trf-nodal-point-etale-locality`). There are zero holes left in the delivered module
and zero holes added elsewhere; no statements were split off.

The imported theorem `AlgebraicGeometry.etale_completedLocalRing_iso`
(node `lem-trf-etale-completed-local-ring-iso`) remains an existing external proof dependency.
This delivery proves the assigned theorem from that declared dependency; it does not claim
that its entire transitive proof closure is free of `sorry`.

## No longer needed

Removed import: `Mathlib.RingTheory.AdicCompletion.LocalRing`.
Removed direct proof dependency: `lem-weil-pbc-local-completion-local-ring`.
The constant-coefficient retraction proves rationality of the residue field directly from the
stalk, so no Noetherianity assumption, completion-locality instance, or completion residue-field
comparison is needed for this reduction. This Mathlib node remains available elsewhere; no
module or declaration is withdrawn. `EtaleCompletedLocalRingIso` remains needed.
No other planned dependency is bypassed, and no unit statement or step is replaced.

## Where the brief, the DAG or earlier work was wrong

No statement error was found. The DAG's residue-field argument is valid but longer than needed:
a retraction from the stalk to `k` already forces its residue field to be `k`.
The pure-dimension hypothesis is unnecessary for this algebraic invariance argument, but its
binder and type are retained verbatim. Both directions use the specified completed stalk map;
no arbitrary choice of a coefficient field or completed algebra structure is made.

Edge cases checked mathematically: identity and open immersions give the expected transport;
the empty source has no point to instantiate; a nonclosed point cannot have such a nodal
presentation because the residue-field retraction forces rationality and the existing geometric
lemma forces closedness. The constant-term argument uses no characteristic restriction and
no special property of dimension one. No new nodes or change records are needed.

## Second reading by K5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
