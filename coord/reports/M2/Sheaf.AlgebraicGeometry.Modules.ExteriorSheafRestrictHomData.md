## What changed

Added a proof-only reduction in `ExteriorSheafRestrictHomData` and a new intermediate theorem module `ExteriorPresheafOpenPullback`. The target theorem now combines the presheaf comparison with `SheafOfModules.sheafificationCompPullback`, `restrictFunctorIsoPullback`, and `PresheafOfModules.sheafification`.

## Proved and sorry left

The target theorem `exteriorSheaf_restrict_hom_data` is reduced to the named intermediate theorem. The intermediate theorem `exteriorPresheaf_open_pullback` remains sorry because its componentwise exterior-power construction and naturality require a substantial presheaf calculation.

## No longer needed

None.

## Where the brief, the DAG or earlier work was wrong

The DAG omitted the presheaf-level comparison needed to make the sheafification argument concrete; it is added as a new node.

## New nodes

`lem-sc-exterior-presheaf-open-pullback`: `lean/Sheaf/AlgebraicGeometry/Modules/ExteriorPresheafOpenPullback.lean`.

## Earlier second reading (a previous round; superseded)

The target proof has unchanged signature and uses the intermediate node exactly as stated; the new statement is a strict presheaf-level subproblem.

## Second reading by M2

1. Compared the delivered item module against the repository version. The theorem signature is byte-for-byte unchanged; only a proof-only import and proof body were added. Verdict: pass.

2. Compiled both delivered modules with `lcompile.py --all`; both compile without errors. The only remaining `sorry` is the named intermediate theorem `exteriorPresheaf_open_pullback`, and it has a split node and proof docstring. No forbidden declarations or hollow definitions were introduced. Verdict: pass.

3. Checked the split-off statement against its presheaf construction and edge cases (including n = 0 and empty opens) and searched the library and Mathlib search tools. It is a strict presheaf-level reduction and is needed by the target proof. Verdict: pass.

4. The target proof follows the sheafification route and retains the unit route; no imports were removable because the added import supplies the split theorem. Verdict: pass.

5. Updated the target node proof and proof dependencies to record the intermediate presheaf comparison used by the Lean proof. Verdict: pass.

Changed: added the second-reading record and synchronized the target DAG node with the delivered proof route.
