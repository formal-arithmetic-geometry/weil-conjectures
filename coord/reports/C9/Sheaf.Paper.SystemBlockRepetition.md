## What changed

Filled five existing proof holes in `Sheaf.Paper.SystemBlockRepetition`: the normalized derived comparison, its adjunction equation, coefficient comparison naturality, composition, and identity. The proofs use the existing derived-category comparison and section pushpull normalization APIs. Existing signatures, definitions and public imports are unchanged. Added proved private helpers and proof-only imports for the normalization and coherence arguments.

## Proved and sorry left

Closed: `blockDerivedComparison_normalization`, `blockDerivedComparison_adjunction`, `blockCoefficientComparison_naturality`, `blockDerivedComparison_comp`, and `blockDerivedComparison_id` (5 of 8 original holes).

Left unchanged: `systemBlockRepetition`, `systemBlockGeometry`, and `blockRepeat_extensionByZero` (3 holes; their existing DAG nodes are `lem-pur-system-block-repetition`). No new sorry declarations were added.

## No longer needed

No declared DAG dependency was removed. The proof uses the existing general derived-square, mate, and composition interfaces. The unfinished endpoint and geometric construction experiments remain outside the delivery.

## Where the brief, the DAG or earlier work was wrong

The stated route is usable for the five derived comparison clauses. The endpoint, geometric system, and open extension clauses require additional concrete sequence-site constructions beyond the available interfaces; no statement was changed.

## Second reading by C9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
