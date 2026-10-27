## What changed

Proved `evaluation_alpha` using the existing `alpha_eq_localized_singleAlpha` and
private, proved calculations for exact localization of natural transformations.
The proof evaluates the same specified ordinary alpha with all its projectors and
compositors. Public signatures, imports, instances and construction bodies are unchanged.

## Proved and sorry left

Closed one of four original holes:
`AlgebraicGeometry.ProEtale.StrictTower.MateEvaluationScalars.evaluation_alpha`.
Added zero holes and split off zero statements.

The three original holes left, in that namespace, are `evaluation_open_transpose`,
`scalar_alpha`, and `scalar_gamma`. Each retains its original statement, source,
proof docstring and attachment to `lem-cbc-tower-mate-evaluation-scalars`.
Validation: the cleaned module compiled through `lcompile.py` in 42.5 seconds,
exit code 0, within the 60-second per-file limit.

## No longer needed

No imports, modules or nodes are removed. The unit route is preserved.
The evaluation-alpha calculation uses the existing ordinary-arrow descent theorem,
so it does not repeat the lower-level clopen-projector and open-beta calculations.
Those dependencies remain needed by the original unfinished scalar-alpha proof and
by existing definitions and proofs in the module.

## Where the brief, the DAG or earlier work was wrong

The existing `alpha_eq_localized_singleAlpha` already identifies the specified
ordinary arrow with the tower alpha after exact descent. Exact localization of a
noninvertible natural transformation commutes with evaluation, so the clopen factor
calculations need not be repeated in `evaluation_alpha`.

Attempted open-transpose and scalar-gamma proofs were removed after concrete
adjunction and localization conversions exceeded the per-file compile limit.
Their original named holes are retained. No statement or definition was weakened.

Change record: `coord/changes/F3-tower-mate-private-localization-helpers.md`.

## Second reading by F3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
