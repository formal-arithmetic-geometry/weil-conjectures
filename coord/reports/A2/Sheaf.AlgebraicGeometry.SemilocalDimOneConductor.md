## What changed

The existing declaration `semilocal_dim_one_conductor` keeps its signature byte for byte.
Its proof combines the four conclusions of
`integralClosure.semilocal_normalization_dim_one` with the strictly smaller conductor-power
statement `semilocal_dim_one_conductor_power` in the new module
`Sheaf.AlgebraicGeometry.SemilocalDimOneConductorPower`. No definition changed and no change
record is needed. The existing node's proof and proof dependencies now describe this reduction.

## Proved and sorry left

Hole closed: `semilocal_dim_one_conductor` (node `lem-sc-semilocal-dim-one-conductor`).
Hole added and still open: `semilocal_dim_one_conductor_power`
(node `semilocal-dim-one-conductor-power`). The normalization theorem used by the proof remains
open in the existing library; this delivery does not close it.

This is a decomposition, not a completed proof: one hole closed, one hole added, net zero.
The main theorem and the new theorem both report exactly `propext`, `Classical.choice`,
`Quot.sound`, and `sorryAx` under `#print axioms`. The new theorem's only proof is `by sorry`.
There are no data definitions, arbitrary witness choices, or other holes in these modules.

## No longer needed

Removed the target's direct proof imports
`Sheaf.AlgebraicGeometry.IntegralOverringJacobsonPower` and
`Sheaf.RingTheory.FiniteIntegralConductor`. All four old proof dependencies other than
`lem-sc-semilocal-dim-one-normalization` are no longer direct dependencies of the target:
`lem-sc-finite-generated-integral-subring`, `lem-sc-finite-integral-conductor`,
`lem-weil-pbc-integral-injective-lying-over`, and `lem-sc-integral-overring-jacobson-power`.
They remain dependencies of the split conductor-power argument, so no whole module is pruned
from the target import closure.

In the new module, removed the unused normalization proof import and the public Dedekind
import. Added the public fraction-ring import needed by its signature. Its two remaining
Sheaf imports provide the pending proof dependencies, in accordance with the stage-3 brief.
All proof imports are plain `import`, not `public import`.

## Where the brief, the DAG or earlier work was wrong

The first report described the original target imports as unchanged and did not record the
changed DAG route. The original split docstring omitted the fraction-field justification and
extension-of-ideal-power calculation. Its node did not mention the extra finiteness hypothesis
in the Lean signature and had an empty blueprint ancestry. These are repaired.
The explicit integrality instance hypothesis was redundant: integral closure already provides
it, and compilation succeeds without it. The finite maximal spectrum of the integral closure
is still an explicit hypothesis of the smaller theorem; the target supplies it from normalization.

## New nodes

`semilocal-dim-one-conductor-power`, in
`dag/nodes/sec-curve-estimates/semilocal-dim-one-conductor-power.json`, isolates only the
conductor conclusion, retaining the source's nonzero hypothesis and adding the available
semilocality of the normalization. Its proof follows the finite-intermediate-ring argument of
[Stacks Tag 09N2](https://stacks.math.columbia.edu/tag/09N2). The docstring gives the complete
argument and specifies the positive exponent. Searches were rerun through `msearch.py` with
LeanSearch, LeanFinder, Loogle, and grep and recorded in `searches.jsonl`; no existing matching theorem was
found. LeanSearch returned Internal Server Error, recorded as unavailable without a verdict;
the other services and grep completed. No change records and no forced adaptations.

## Second reading by A2

1. Compared every delivered module against the repository. The existing module differs only
   in two removed private imports, one added private import, and its proof. Its declaration
   signature is byte for byte unchanged. The other module is new. No definitions or existing
   statements change. Verdict: pass after repairs.
2. Compiled both modules in dependency order with `lcompile.py --all`, with no errors or
   warnings. Compiled scratch copies with `#print axioms` for both declarations: only the three
   standard axioms plus `sorryAx`. Scanned the delivered sources for forbidden declarations
   and holes: the sole new hole is the named public theorem, with its source and proof docstring.
   Verdict: valid reduction, still dependent on open theorems.
3. Checked the split statement against Stacks 09N2 and its full natural-language proof.
   `y = 0` permits `n = 1, b = 0`; when `B` is already normal, `n = 1` and `b = x*y` work;
   in the localized cusp `k[t^2,t^3]_(t^2,t^3)` with normalization `k[t]_(t)`, the conductor
   contains `t^2`, consistently with the power assertion. A field fails the dimension-one
   hypothesis. The argument even allows `x = 0`, but the stated nonzero source hypothesis
   is retained. Fresh searches found generic conductor and integral-extension results, not
   this assertion; local searches found only the existing lower dependencies. Closing this
   hole requires finite-subalgebra/tower construction and ideal-map glue, beyond a short
   lemma application; it remains isolated. Verdict: true, needed, strictly smaller.
4. The target takes its normalization conclusions directly from the existing node and uses
   only the remaining conductor conclusion as the split. Private proof imports were pruned.
   The four former direct dependencies are all listed above and retained transitively for
   the open argument. `dag/units/sk-thm-curveestimate.json` realizes its statement by
   `thm-sc-proper-cohomology` and has no realized steps; this item lies below that unit and
   the route is unchanged. Verdict: pass, decomposition with no net hole reduction.
5. Updated the parent node's proof, proof_deps, and proof_origin to the two applications in
   Lean. The new node records its exact Lean signature, hypotheses, complete proof steps,
   dependency union, source, provenance, chapter/unit, creation fields, and real search records.
   Its blueprint ancestry now passes through the parent. Verdict: pass after repairs.

Second reading changed imports, removed a redundant hypothesis from the new theorem, completed
its docstring proof and node metadata, updated the parent DAG route, and corrected the report's
progress accounting. The existing proof itself was retained.
