## What changed

Repaired `Sheaf.Paper.CechCupPullbackCompat` proofs and pruned the obsolete
`CechComparisonMapNaturality` import. The Cech module public signatures are unchanged.

## Proved and sorry left

The two target declarations remain proved with no direct `sorry` in the item's module:
`moduleCup_coefficient_naturality` and `moduleCup_pullback_naturality`. No new holes are
added. Closed the two existing direct holes named above; added zero holes. The
coefficient naturality theorem uses only `propext`, `Classical.choice`, and
`Quot.sound`. Pullback naturality still depends on existing upstream `sorryAx`.
Scratch `#print axioms` checks of all seven public theorems found no other axioms.

## No longer needed

The prior delivery's removed `CechComparisonMapNaturality` import remains pruned. No
additional proof dependency was removed. The removed proof dependency is
`lem-sc-cech-comparison-map-naturality`, module `Sheaf.Paper.CechComparisonMapNaturality`.

## Where the brief, the DAG or earlier work was wrong

No mathematical error was found. The earlier delivery had already removed the obsolete
comparison-map import; this reading confirms that pruning and the direct resolution-map
proof route.

## Second reading by Y3

1. Compared the delivered Cech module with the repository version. Existing public
   theorem signatures are unchanged. Verdict: pass.
2. Compiled the sandbox Cech module with `lcompile.py`; it compiles without warnings.
   The target proofs contain no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or
   `implemented_by`. Verdict: pass.
3. Checked the proof route and resolution-map dependencies against the DAG. Cycle
   lifting, Leibniz construction, and cycle transport are strictly simpler and do not
   restate the target. Verdict: pass; no split-off statements.
4. The proof uses the available resolution-map route and keeps the unit route. The
   removed `CechComparisonMapNaturality` import is unused. Verdict: pass.
5. The node declarations, proof dependencies, and proof origin agree with Lean.
   Verdict: pass.

Second reading removed the unnecessary normalization-module adaptation and its change
record after the delivery tool verified the original compiles unchanged. No mathematical
statements or proof terms changed in the second reading.
