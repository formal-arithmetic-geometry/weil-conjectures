## What changed

`Sheaf.Paper.WeilKoszulJoinBijective` now proves the target theorem by a grading
split. The positive-degree branch is proved using zero terms of the extended
Koszul complexes and the coproduct description of the tensor term. The
nonpositive branch is isolated in the new theorem
`koszulJoinGraded_bijective_of_nonpositive`, whose ordered-subset exterior basis
argument remains for a follow-up worker. The two new theorem modules are
imported privately by the target module.

## Proved and sorry left

Closed the sorry in `koszulJoinGraded_bijective`.

Closed the positive-degree substatement
`koszulJoinGraded_bijective_of_pos`.

One sorry remains in the new declaration
`koszulJoinGraded_bijective_of_nonpositive`, node
`new-weil-pbc-koszul-join-graded-nonpositive`. This is strictly smaller because
it is restricted to `i ≤ 0` and contains only the ordered-subset basis step.

## No longer needed

None. The original graded join definition remains the sole proof dependency;
the positive branch uses its extension and coproduct structure, while the
nonpositive branch retains the exterior basis dependency from the DAG plan.

## Where the brief, the DAG or earlier work was wrong

The original node bundled positive-degree zero-object reasoning with the
nonpositive ordered-basis decomposition. The former is independent and has
been proved here; the latter is now recorded as a separate, strictly smaller
statement.

## New nodes

`new-weil-pbc-koszul-join-graded-positive` records the proved positive-degree
zero-object argument.

`new-weil-pbc-koszul-join-graded-nonpositive` records the remaining
nonpositive-degree ordered-subset basis argument.

## Second reading by E3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
