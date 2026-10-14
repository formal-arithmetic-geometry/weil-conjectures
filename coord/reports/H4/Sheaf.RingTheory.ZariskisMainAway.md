## What changed

The item module already contains a complete proof of `Algebra.zariskisMainProperty_of_isQuasiFiniteAtPrime`; it was copied into the sandbox unchanged and compiled successfully. No source changes are required.

## Proved and sorry left

`Algebra.zariskisMainProperty_of_isQuasiFiniteAtPrime` is proved. No `sorry` remains in the item module, and no new holes were added.

## No longer needed

None. The existing imports are used by the proof or its public statement.

## Where the brief, the DAG or earlier work was wrong

The repository already contains the completed proof (from earlier landing), so this dispatch had no remaining open obligation to implement.


## Second reading by H4

1. The delivered module was compared with `lean/Sheaf/RingTheory/ZariskisMainAway.lean`; the theorem signature and all public declarations are byte-for-byte unchanged. The only proof change removes a redundant `change` command.

2. The sandbox module compiles cleanly with `lcompile.py`; it contains no `sorry`, `axiom`, `unsafe`, `opaque`, `implemented_by`, or `extern`. The proof uses only the existing Mathlib conversion theorem and the imported fibre hypothesis.

3. No statements were split off or added. The existing theorem is exactly the required fibre-to-`QuasiFiniteAt` conversion, and no duplicate or weaker statement was introduced.

4. The proof follows the node route through the fibre homeomorphism and `QuasiFiniteAt.of_isOpen_singleton_fiber`; the existing imports remain necessary and no pruning is available.

5. The DAG node and unit route remain consistent with the unchanged theorem and proof dependencies. No node edits are needed.

Changed: removed the unnecessary `change` line from the proof and recorded this second reading.
