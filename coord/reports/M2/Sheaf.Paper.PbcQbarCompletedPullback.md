## What changed

Closed `AlgebraicGeometry.Scheme.pbcQbarIntegralPull_mem` in
`Sheaf.Paper.PbcQbarCompletedPullback`, preserving its full statement and the
existing family and pair-category constructions.

The proof follows the declaration's finite-reduction argument. Specialize to
`pbcFiniteField l Ω E`, obtain a common interval and constructible cohomology
from `pbcUniformReductionCriterion`, and reflect the cohomology bounds through
exact scalar restriction. Restriction faithfulness is proved locally from the
presheaf restriction functor. Apply the existing
`pbc_constructible_reduction_pullback`, then
`pbc_constructible_reduction_criterion` to recover the uniform local models and
compatible etale origins on the strict-tower output. Finally transport membership
along the already specified `pbcActualCompletedPullback_tower` comparison, using
isomorphism closure of the integral constructible predicate.

Added private proof imports of `PbcConstructibleReductionPullback`,
`PbcConstructibleReductionCriterion`, and `PbcUniformReductionCriterion`; all
three supply declarations used by the proof. Existing imports are retained.
A declaration-scoped unused-section-variable linter setting retains the published
hypotheses although this proof does not need all of them. In particular it adds
no base-field invertibility or nonemptiness assumption, and retains the separate
scheme and algebraic-closure universes.

Removed unused private imports of the item from `CompletedPullbackReduction` and
`SbcCompletedOperations` to make this proof dependency acyclic. Both now import
`PbcFiniteCompletedCoefficientMap` directly to preserve the required sheafification
and locally-bijective instances in the PBC coefficient universe. Their proofs and
definitions remain unchanged.
A fresh output-producing compile of the three delivery files passed through
`lcompile.py`: `CompletedPullbackReduction` (35.9 s), the item (18.9 s), and
`SbcCompletedOperations` (31.9 s). The immediate proof consumer
`PbcConstructibleReductionPullback` also compiled against the rebuilt auxiliary
modules (11.0 s), followed by the item (26.5 s). Its verification-only source copy
is excluded from the delivery.
A source-graph check found no cycle back to the item.

No public imports, definitions or theorem signatures change. See
`coord/changes/M2-completed-pullback-private-import-cycle.md`.

## Proved and sorry left

Closed one hole: `AlgebraicGeometry.Scheme.pbcQbarIntegralPull_mem`
(node `def-weil-pbc-completed-pullback`).
The item now has zero direct `sorry` holes; no holes were added or split off.
`pbcQbarPullFamily_existsUnique` remains proved by its existing proof, and the
family and common-stage pullback definitions remain unchanged. Existing holes
in the auxiliary modules and imported dependencies are unchanged, rather than
claimed as closed by this delivery.

## No longer needed

Removed `import Sheaf.Paper.PbcQbarCompletedPullback` from
`Sheaf.Paper.CompletedPullbackReduction` and
`Sheaf.Paper.SbcCompletedOperations`: both imports supplied no declaration used
there and created reverse edges from the finite-reduction theory to its Qbar
application. Both modules now import the finite-coefficient instance module
directly to preserve the elaboration context. No declaration or module is withdrawn;
no mathematical node is claimed pruned. The generic strict-tower interface and its prerequisites remain
needed and are retained.

## Where the brief, the DAG or earlier work was wrong

The recorded proof block of `def-weil-pbc-completed-pullback` describes the generic
`CompletedPullback` exactness and completeness equivalence, rather than the
remaining Qbar membership theorem. The membership theorem's own docstring gives
the applicable argument, and the library already packages its finite-reduction
and reconstruction steps. This delivery implements that same argument without
new statements or a departure from the unit route; the generic proof record and
its still-needed dependencies are retained. Adding the application-level
preservation theorem as a proof dependency of this definition node would create
a metadata cycle, because that theorem already cites the generic completed
pullback definition. No such cyclic dependency has been added.

Searches used `msearch.py` LeanFinder (completed-pullback constructibility), Loogle
(`Functor.IsTriangulated`, no result), and grep, followed by local `rg` over both
library roots. Mathlib's results concern ordinary module pullback, while the
existing project reduction theorems provide exactly the required stronger
complete/constructible statement.

The two reverse private imports supplied elaboration context through the Qbar
application despite using no Qbar declaration. Removing the import without a
replacement makes `sbcOrdinaryModuleIso_naturality` report
`stuck at solving universe constraint u + 1 =?= max (u + 1) ?u.89`.
A direct import of `PbcFiniteCompletedCoefficientMap` supplies its priority-3000
`pbcFiniteStageAbSheafify` and `pbcFiniteStageAbLocallyBijective` instances.
It preserves the existing proofs and definitions while avoiding the
application-level import cycle. Initial output-producing checks timed out while
obsolete item/consumer artifacts remained in the sandbox. Clearing the generated
artifacts and rebuilding the delivery files from the published library passed
within the existing limit; no compiler limit, definition or proof in either
auxiliary module was changed. Neither auxiliary module is held by another group
in the shared claim records.

## Second reading by M2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
