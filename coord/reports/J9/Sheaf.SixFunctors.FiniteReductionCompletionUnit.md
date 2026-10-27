## What changed

Prove `WeilConjectures.GeneratorReduction.finiteReduction_completionUnit` in
`Sheaf.SixFunctors.FiniteReductionCompletionUnit`, with its statement unchanged.
Add private proof imports of `IntegralOperationRoosEffectivity`,
`IntegralDerivedOperationsOnSlices`, and `CompletionUnitFiniteMateComparison`.
Reuse the proved ordinary-tower effectivity helper and the finite-model unit
formula. Four proved private helpers compute the projected Roos augmentation and
cancel its invertible finite adjoint. The public theorem transports that result
from a good representative using the defining completion-unit equation and
naturality. Update the item's node to record this route. No shared interface or
other existing module is changed.

## Proved and sorry left

Closed: `WeilConjectures.GeneratorReduction.finiteReduction_completionUnit`
(node `lem-sf-finite-reduction-completion-unit`), the item's only original hole.
Added: none. Remaining in the delivery: none. No split-off obligations.
The four new private proof helpers are completely proved; a private abelian
instance reuses the existing global-site module instance.
The final file compiled without errors or warnings through `lcompile.py` in
48.5 seconds, with the profiling options removed. The public theorem signature
is unchanged, and the updated dependency graph has no path back to this item.

## No longer needed

No original import is removed: the existing public canonical-bridge import is
retained. No module is withdrawn. The proof does not separately import
`Sheaf.Paper.NormalizedDVRKFlatReductionModel` or
`Sheaf.Paper.NormalizedDVRRoosFiniteReduction`, associated with
`lem-coef-normalized-dvr-kflat-reduction-model` and
`lem-coef-normalized-dvr-roos-finite-reduction`. These are removed from the item's
direct proof dependencies because the already proved ordinary-tower effectivity
argument supplies the required projection invertibility. They remain dependencies
of that argument, so this delivery claims no global pruning of either module.
All other original dependency roles are retained; the node adds the effectivity
and finite-mate comparison dependencies actually used by this proof.

## Where the brief, the DAG or earlier work was wrong

No statement discrepancy was found. The planned construction can be shortened by
reusing the existing private `fromOrdinary` and `finiteModel_unit` proofs via
proof-only `import all`. There is no need to split this obligation again.
The projected composite equals the canonical K-flat finite-model comparison,
which is an isomorphism; it need not be treated as a literal identity in derived
coordinates. The proof works for n = 0 and arbitrary unbounded K, with no extra
completeness or geometric characteristic hypothesis.

## Second reading by J9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
