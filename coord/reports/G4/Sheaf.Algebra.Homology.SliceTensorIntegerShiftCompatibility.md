## What changed

Proved `CategoryTheory.total_tensor_integer_shift_models`. Existing public signatures, definitions,
and public imports remain unchanged. All new helpers are private and proved.

Mathlib bifunctor shifts give the unsigned first-variable comparison and the coefficient
`(n * p).negOnePow` in the second variable. The proved fixed-tensor shift helper gives
K-flat shift stability. The pure-tensor formulas for the canonical shifts hold for every integer.

Proof imports added: `TensorColimitsIndependentCoefficients` and `KFlatFixedTensorTriangulated`.
The latter exposes its existing proved private shift-stability helper with `import all`.
The DAG records the implemented stability argument and retains the original plan for the
chain and derived compatibility theorems.

## Proved and sorry left

Closed one of the three original holes:
`CategoryTheory.total_tensor_integer_shift_models`.

Two original holes remain:

- `CategoryTheory.slice_tensor_integer_shift_chain`;
- `CategoryTheory.slice_tensor_integer_shift_compatibility`.

Both belong to node `lem-weil-pbc-slice-tensor-integer-shift-compatibility`.
No holes were added or split off. No definition contains `sorry`.
The delivered module compiled against the original dependencies in 50.8 seconds.

Chain and derived proofs were developed in the scratchpad, with separately
checked categorical descent and representative-square arguments. Their complete module
exceeded the 60-second compile limit. Those experimental helpers and definition refactors
are excluded from this delivery; the two original compatibility theorems remain untouched.

## No longer needed

Removed the original proof imports `RingedSliceEvaluationTranspose`,
`SiteDerivedTensorDescentIndependentCoefficients`, and `KFlatHomotopyTriangulated`.
The first two interfaces remain transitively available through unchanged public imports.
The final derived theorem remains unproved, so their planned derived-descent work is not
claimed as globally pruned. For the proved stability clause, the proved
`KFlatFixedTensorTriangulated.shift_kFlat` replaces the planned holed stability result.

The unfinished chain and derived arguments retain their original planned dependencies.
No module is claimed as globally pruned or withdrawn. No upstream declaration is removed,
and the blueprint unit's realized steps are retained.

## Where the brief, the DAG or earlier work was wrong

No statement or definition repair is delivered. The planned derived-shift descent theorem
is specialized to its published tensor presentation, whereas this item quantifies over
arbitrary specified presentations `S,T`; the remaining argument needs transport through
the specified model comparison.

The launcher resumed this sandbox after provider interruptions and a compile-queue pause.
The original claim began 2026-10-23 09:06 UTC, whereas the current budget reference starts
2026-10-23 16:44:30 UTC. The worker did not alter that metadata. No earlier delivery was
started.

## Second reading by G4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
