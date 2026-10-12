## What changed

Proved `AlgebraicGeometry.proper_basic` in
`Sheaf.AlgebraicGeometry.ProperBasic` directly from Mathlib. The first five
conjuncts use existing instances. After installing the affine-base hypothesis,
`HasAffineProperty.iff_of_isAffine` gives separatedness of the source and
`QuasiCompact.compactSpace_of_compactSpace` gives its compactness.
The signature, visibility, docstrings and three public imports are unchanged.
Updated node `pqf-lem-proper-basic` to describe this compiled proof.

## Proved and sorry left

Closed: `AlgebraicGeometry.proper_basic` (node `pqf-lem-proper-basic`), the
module's sole hole. Added holes: none. Remaining holes: none.
This is a complete proof from Mathlib, not a decomposition into unproved lemmas.
The delivery's axiom probe checks that no nonstandard axiom is used.

## No longer needed

None. All four existing proof-dependency nodes still describe facts used by the
proof: `def-weil-proper-morphism`, `def-weil-finite-type-morphism`,
`lem-pc-separated-quasi-separated` and
`lem-sc-separated-over-affine-scheme-separated`.
No Sheaf or WeilConjectures proof modules are required. No imports were removed;
the existing public imports expose types occurring in the statement.
The unit `sk-prop-av-pqf-finite` has no realized nodes or steps to bypass.

## Where the brief, the DAG or earlier work was wrong

No mathematical correction was necessary. Mathlib obtains quasi-compactness
from universal closedness rather than including it as a field of `IsProper`;
the node's updated proof makes that implementation detail explicit.
The unit's blueprint section text is not present in this checkout; its JSON
record was read, including the statement, step and empty `realized` entries.

## Second reading by B2

1. **Visible changes and signatures — PASS.** Compared the delivered module with the repository version. The theorem signature, visibility, docstring, and imports are unchanged; only the proof body changed. The DAG diff changes only the recorded proof route and origin.
2. **Compilation and axioms — PASS.** Compiled the delivered module with `lcompile.py`; it succeeds with no errors and contains no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or `implemented_by`. The proof uses standard Mathlib instances and lemmas.
3. **Statements and split-offs — PASS.** No statements were split off and no new nodes were added. The existing target statement is proved exactly as written, with all six conjuncts and the affine-base implication retained.
4. **Shortest route and pruning — PASS.** The proof uses Mathlib's `IsProper` parent instances, the existing quasi-separatedness instance, `HasAffineProperty.iff_of_isAffine`, and `QuasiCompact.compactSpace_of_compactSpace`; all declared proof dependencies remain relevant and no imports can be removed.
5. **DAG and unit agreement — PASS.** The node's proof, dependencies, and proof origin match the Lean proof. The unit `sk-prop-av-pqf-finite` has no realized statement or steps in this checkout, so no unit route is bypassed.

Changed only the report by adding this second-reading record; no Lean repair was necessary.
