# C2 derived monoidal module maintenance

Item: `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal`, stage 3.

## Cause

The source had seven existing proof holes nested in constructed `def`/`instance` bodies.
The normal stage-3 gate freezes adopted-library construction bodies. The retained C2
repair closed the holes by constructing natural tensor counits and reusing existing
monoidal descent, but it also changed constructed bodies and added public helpers and
imports. The gate rejected those interface changes on every submission. This was a
mismatch between the dispatched source data and the normal proof-only delivery boundary;
rerunning the worker could not resolve it. Earlier maintenance reports requested protected
gate changes and left the incompatible source unchanged.

The latest fresh worker evidence is `scratchpad/dryrun-20261018-0134.log`: its sole
preflight refusal is `(c) stage3 gate`. The refusals include changed construction bodies,
public imports, helper additions and a private helper removal; the refusal was broader
than the last dispatcher's summary of nested proof fields alone.

## Repair

Applied the already-written, complete C2 implementation as an authorized module maintenance
correction. Maintenance did not invent the item's mathematics. The implementation composes
canonical natural transformations for the counits, proves derivability and invertibility,
reuses `Functor.residueDerivedMonoidal`, and provides
`leftDerivedUpperStarTensor_eq_leftDerivedTensorComparison` plus explicit unit compatibility.

All seven old holes are closed; zero new holes and zero local holes remain. Every existing
public signature and visibility is preserved. Existing declaration docstrings are preserved.
The private helper changes and added public construction imports are recorded explicitly.
Local aliases cache existing ambient/pullback/tensor properties, and the existing complex
HasTensor proof directly reuses its graded instance, reducing elaboration work.

Corrected the retained node's invalid blueprint reference to the actual
`sk-def-sfb-module-derived-pushpull` blueprint node. Its declarations and proof dependencies
match the delivered construction. The node is marked DAG-unreachable because it has no
incoming DAG edge; the Lean target import closure still reaches its module.

Server files:

- `lean/WeilConjectures/SixFunctors/ProEtale/ModuleObject/Derived/Monoidal.lean`
- `dag/nodes/sec-six-functors-basics/new-proetale-derived-module-pullback-monoidal.json`
- `coord/changes/C2-derived-module-proof-obligations.md`
- `coord/reports/maintenance/C2-WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal.md`

Each changed file has a `.bak` copy (new records have an initial snapshot). The source's original is
`Monoidal.lean.maintenance-1792257299.bak` beside it. Previous maintenance records and
sandbox artifacts are preserved, not overwritten without backups.

## Validation

- Whole source compiled with `SHEAF_GROUP=maintenance-C2-Monoidal SHEAF_FILE_TIMEOUT=60
  tools/lean_file.sh ...`: **52.5 seconds**, exit 0. The time limit was not raised.
- Read-only stage3 `check_lean` passed; no new forbidden constructs or local holes.
- Public-signature, visibility, declaration-header and docstring comparisons passed.
- Corrected node declarations, signature, dependency union, chapter, unit and strict
  blueprint validation passed.
- The canonical source path compiled again in **47.6 seconds** and emitted its artifact
  into the maintenance group's mirror.
- The standard stage3 axiom probe compiled in **55.0 seconds**, checked **42 declarations**,
  and reported no `SHEAF-AXIOM` or `SHEAF-SORRY` findings. Its appended tool code emitted
  a pre-existing long-line warning; the canonical source compile was warning-free.
- `Derived.UpperStarUnitCoherence` compiled in **37.6 seconds** against the repaired
  module's new artifact in that mirror.

No `lake build` was run. No unrelated process was killed. No protected launcher, gate,
review-service or landing tool was edited. No cap, throttle, admission limit or pause was
introduced. Dispatcher counters/state and unrelated working-tree changes were preserved.

The direct single-file tool and remote worker compiler use different process priorities
(19 and 10 respectively); prior worker timings were therefore not used as the sole
verification. This repair was checked through the requested direct tool.

## Commit

This report accompanies the server maintenance commit; the local final report records its hash.

## Next worker

Refresh the server baseline. This item now has zero source holes; retain the maintenance
implementation and do not resubmit the old construction rewrite against its former base.
The sandbox report identifies the repaired baseline. The normal dispatcher refresh should
recognize the module's completion. Imported modules still carry the project's separate
proof obligations; a zero-hole file does not assert that the entire target closure is
axiom-free. The global build verifies the remaining transitive consumers (207 at inspection).

The source-library freeze and all normal delivery checks remain in force. No launcher change
is required for this repaired module. Experimental proof-field extraction candidates were
never installed in the canonical project.
