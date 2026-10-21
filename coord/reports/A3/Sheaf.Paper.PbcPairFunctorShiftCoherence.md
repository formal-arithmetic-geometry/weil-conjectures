## What changed

Proved `AlgebraicGeometry.Scheme.pbcPairFunctorShiftCoherence` with unchanged statement
and unchanged `PairFunctorShiftCoherenceSpec`. All changes are confined to its module
and node. Added proved private helpers for the generic stage-system argument, adapting
the existing private construction in `Sheaf.Paper.PbcDescentFunctors` without importing
its triangulated-category infrastructure or changing that module.

The stage comparisons form a compatible `Morphism.Hom`; its descended natural
transformation supplies naturality. Images of the stage comparison isomorphisms give
inverse components. The zero and addition laws follow by applying the stage inclusion
to the corresponding stage laws. The existing identity-component inclusion comparison
commutes with these shifts. Heterogeneous functor extensionality identifies the prescribed
`G` with `A.functor` from its object and representative formulas.

The generic private theorem avoids expensive unfolding of concrete PBC quotient types:
the first direct concrete argument timed out, whereas the completed generic argument
and its PBC specialization compiled together in 5.3 seconds through `lcompile.py`.
The proof works for all integer shifts, including zero, negative and opposite degrees;
it assumes neither distinguished-triangle preservation nor faithfulness of transitions.
No public declarations, definitions or imports were changed.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.Scheme.pbcPairFunctorShiftCoherence`
(node `lem-weil-pbc-pair-functor-shift-coherence`).
Added 0 holes; split off 0 statements. No `sorry` remains anywhere in the delivered module.
The proof uses the supplied canonical common-stage structures and their existing dependencies.

## No longer needed

Removed the unused private imports `Sheaf.Paper.PbcScalarExtension` and
`Mathlib.CategoryTheory.Triangulated.Functor`. The scalar-extension module remains a
transitive dependency of the canonical common-stage structures, so no module is withdrawn.

Removed `prop-weil-pbc-scalar-extension` as a separate proof dependency of this node:
the proof does not need to calculate repeated-field scalar units or deduce identity
shift comparisons from them. The existing stage-system morphism descent machinery and
canonical common-stage shift already supply the needed formulas. That node remains a
statement dependency and is not claimed globally pruned. The finite-stage pair-category
and common-stage-calculus dependencies are both retained. No unit route is bypassed.

## Where the brief, the DAG or earlier work was wrong

The planned repeated-field normalization and iteration of the degree-one shift are
unnecessary. The canonical common-stage structure already provides coherent shifts
for every integer directly. The existing private proof in `PbcDescentFunctors` supplies
the exact generic construction needed here; only the prescribed-functor equality is
additional. The DAG proof now follows these actual Lean steps. No statement or definition
repair was necessary, and no source-library module was edited.

Preflight requested a visible-command/import change record for the private helper
construction and removal of the two proof-only imports. Added
`coord/changes/PbcPairFunctorShiftCoherence.md`; downstream analysis found zero
external importing modules and only the item itself references its public theorem.

## Second reading by A3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
