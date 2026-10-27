# Maintenance: NI / lem-pur-weil-tate-datum-transport

2026-10-26. Dispatcher key `lem-pur-weil-tate-datum-transport@ee9296d5e`.

The six reported failures stopped in a live dependency before the retained
stage-2 packet could be checked. They do not establish that the item's statement
or proof plan is wrong.

## Cause and tested repair

`Sheaf.Paper.ScalarEvaluationTransposeExistence.sequenceScalarMate_isIso`
passed a final `hδ` argument to
`WeilConjectures.SequenceModuleEvaluation.sequenceModulePullbackEvaluation_isIso`.
The latter's current signature ends at the comparison isomorphism `d` and
already returns `IsIso`. Commit `54d0ba29b7a` removed the old sectionwise-identity
hypothesis from that theorem. The R6 proof landing `49468471f35` subsequently
introduced a caller still supplying it. The current global-build log reproduced
the same error as NI's failed overlay snapshot
`700e62e5476cfe754a0750479579deed0cae389f95a3a25f819e261e23e2698a`.

The minimal repair removes the final `hδ` argument and names the now unused
private-helper binder `_hδ`. Its type and position, public declarations,
definitions, and mathematical statements are preserved. No new proof or axiom is
introduced. The accompanying `NI-tate-datum-1792999772.patch` contains this repair
against the recovered R6 source.

Validation with `tools/lean_file.sh`, one file per invocation and the normal
60-second acceptance limit:

- Removing the extra argument compiled in 57.8 seconds, with an unused-parameter
  warning.
- The complete two-line repair compiled in 44.7 seconds without warnings.

Before maintenance could commit that source change, automatic recovery commit
`6e7468593d53fa7ced117aa29373d307ea00f1f1` at 07:33:57 UTC took out the R6 landing,
along with the three failing graph-square proof landings. The live scalar module
is therefore the earlier statement-only version. It compiled in 5.7 seconds,
without warnings. Maintenance did not restore a taken-out landing or change
its DAG records. R6's returned proof is being repaired through its normal lane;
the saved patch applies after recovering `49468471f35` as its return instructs.

The original R6 source is retained at
`lean/Sheaf/Paper/ScalarEvaluationTransposeExistence.lean.maint-NI-tate-datum-1792999772.bak`.

## Cached failures

The launcher's compile attachment cache keys the dependency state only by the
published build stamp. A source repair or take-out before another published
build therefore leaves the old failed result reusable for six hours. NI's logs
show repeated cache hits for exactly the failing scompile and dry-run requests.

After checking that no runner for either old key was active, maintenance renamed
these two stale cached results to the same paths plus
`.maint-NI-tate-datum-1792999772.bak`:

- `sbfc5e6e354eeee1d725fafc0-2e62fcea1905ca723de9f559.json`
- `s22b509176810f5bd6c1bc56e-2e62fcea1905ca723de9f559.json`

They are in the launcher's `compile-results` directory. Historical `.last.json`
records and unrelated results were preserved. No launcher, review, landing, or
admission code was modified, and no dispatch limits or pauses were introduced.

The launcher owner should include the live source/overlay revision in stage-2
dependency cache validation, so a source change invalidates a stored failure
even before the next published build. This maintenance makes no change to that
launcher-owned implementation.
