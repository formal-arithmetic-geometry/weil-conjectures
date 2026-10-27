## What changed

Filled two geometric proof obligations in
`Sheaf.AlgebraicGeometry.ProperSupportCompactMaps`, preserving every declaration,
instance attribute, definition, signature, docstring and import.

For `AlgebraicGeometry.Etale.compactProperSupportClosed`, rewrite the structure
composite using `c.comm`, apply Mathlib's `IsProper.of_comp` against the separated
proper map `c.g`, and apply `IsClosedImmersion.of_isPreimmersion` to its closed
range. This uses only the given hypotheses, with no nonemptiness, finite-type or
Noetherian assumption added.

For `AlgebraicGeometry.Etale.compactProductSupportProper`, identify the structure
map of the product support with the first pullback projection followed by
`i ≫ f`. Both factors are proper, by base change and composition. The projection
identity is proved using explicit pullback equations to avoid a looping simp
rule for `pullback.toBase`.

Searched Mathlib with the prescribed LeanFinder, Loogle and grep tools, and read
the matching declarations. Also inspected the supported-coefficient definitions,
open-adjunction APIs and constant-pullback composition coherence in the adopted
source library. The four coefficient obligations remain unchanged; no new
statement is introduced to repackage them. All compilation uses `lcompile.py`; the delivered module compiled cleanly in
9.6 seconds (exit code 0).

## Proved and sorry left

Closed 2 of the original 6 holes:

- `AlgebraicGeometry.Etale.compactProperSupportClosed`.
- `AlgebraicGeometry.Etale.compactProductSupportProper`.

Added 0 holes and split off 0 statements. Four original holes remain, each attached
to `def-pur-proper-support-compact-maps` with its existing source and proof sketch:

- `AlgebraicGeometry.Etale.compactSupportCoefficientRestriction_existsUnique`.
- `AlgebraicGeometry.Etale.compactSupportCoefficientExtension_isIso`.
- `AlgebraicGeometry.ProEtale.compactSupportCoefficientRestriction_existsUnique`.
- `AlgebraicGeometry.ProEtale.compactSupportCoefficientExtension_isIso`.

This is a partial proof delivery, not a decomposition. The unchanged coefficient
restriction definitions still choose only from their uniquely normalized
existence theorems; none of the definitions contains a new hole.

## No longer needed

None. No imports, nodes, modules or tool-use approvals are removed. All three
existing public imports remain needed by the unchanged statements and
constructions. Both geometric proofs follow the existing declaration docstrings,
so the node's route and dependencies are unchanged.

## Where the brief, the DAG or earlier work was wrong

No mathematical discrepancy found. The item is a definition node with an empty
proof array; the individual declaration docstrings supply the proof sketches.
The two filled obligations implement those sketches directly from Mathlib.

## Second reading by B8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
