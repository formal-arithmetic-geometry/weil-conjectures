## What changed

Retired `Sheaf.AlgebraicGeometry.PerfectCommonAffineModels` in favour of its adopted upstream
twin. Changed the only current consumer, `Sheaf.AlgebraicGeometry.PerfectDerivedTensor`, to
import `WeilConjectures.AlgebraicGeometry.PerfectCommonAffineModels` privately. The theorem
application is unchanged. Redirected the Lean attachment of
`lem-pc-perfect-common-affine-models` to the upstream module. The theorem, private helpers,
and proof route are already present upstream, with explicit `overFunctor.{u}` annotations.

Change record: `coord/changes/retire-perfect-common-affine-models.md`.

The consumer import-closure comparison changes exactly one module: the Sheaf copy is
replaced by the upstream twin. It introduces no additional pairs of twin modules.

Validation: the changed consumer compiled through `lcompile.py`, and `deliver3.py --no-push`
passed its compilation and preflight checks (review class CODEX). The supplementary appended
axiom probe timed out after 60 seconds; the delivery tool explicitly leaves that probe to
merge/global verification. The ordinary consumer compile passed.

## Proved and sorry left

The item already contained zero holes: proved 0 of 0 sorries; closed none; added none;
split off none. `AlgebraicGeometry.Scheme.perfect_common_affine_models` remains fully proved
in the upstream twin. No declarations or proofs of the consumer are changed.

## No longer needed

Pruned `Sheaf.AlgebraicGeometry.PerfectCommonAffineModels` and removed its import from
`Sheaf.AlgebraicGeometry.PerfectDerivedTensor`. The duplicate's private `restrict_model` and
`restrict_strictlyPerfect` are supplied by the upstream twin, whose public theorem the
consumer uses. No mathematical DAG dependency or unit step is pruned; the node now points
to the canonical implementation. No other current library module imports the withdrawn copy.

## Where the brief, the DAG or earlier work was wrong

The generic proof brief describes a holed theorem, but this queue item has kind `retire`
and zero holes. The retirement inventory's three-consumer list is stale: the Sheaf versions
of LocalPerfectSupportedStabilization and PerfectTwoOutOfThree have already retired. Its
reported signature differences are explicit universe annotations, and upstream includes
both private helpers. The actual consumer compile checks that the replacement applies.

## Second reading by A7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
