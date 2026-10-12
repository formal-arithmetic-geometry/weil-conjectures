## What changed

Proved `AlgebraicGeometry.affine_algebra_stalkMap_flat` with its original signature unchanged.
Added the proof-only import `Sheaf.AlgebraicGeometry.AffinePushforwardStalkLocalization`.
The new module proves `AlgebraicGeometry.affine_pushforward_stalk_isLocalization` directly
from Mathlib using affine basic opens, fractions in their section rings, and germ equality.
Updated the original DAG proof to match the scalar-tower and localization-flatness argument.
No definitions, existing statements, or visibility changed. Both modules compile cleanly.

## Proved and sorry left

Closed the original hole `AlgebraicGeometry.affine_algebra_stalkMap_flat`
(node `lem-sc-affine-algebra-stalk-flat`): 1 of 1 original holes closed.
Also proved the new helper `AlgebraicGeometry.affine_pushforward_stalk_isLocalization`
(node `lem-sc-affine-pushforward-stalk-localization`). No holes added and no `sorry` left
in either delivered module. This is a proof, not a decomposition. The proof uses no
unproved project theorem: the new helper is proved entirely from Mathlib.

## No longer needed

None. No original import is removed, and all three original proof dependencies remain
needed: `pqf-def-affine-morphism`, `lem-weil-pbc-affine-open-stalk-localization`, and
`lem-weil-pbc-localization-flat` (all supplied by Mathlib). No planned node or module is
pruned. The proof uses Mathlib's flatness descent across a localization, so it does not
need a separate identification of the final stalk map as a further localization.

## Where the brief, the DAG or earlier work was wrong

The plan was correct but its stated affine-open stalk lemma describes the ordinary
scheme stalk, not the pushforward stalk. The new, fully proved helper supplies that
calculation. Germ compatibility proves the scalar tower directly; flatness descent
avoids additional localization-of-localization transport. The unit record has no
realized node at this level, and no unit statement or route is bypassed.
LeanSearch returned Internal Server Error; LeanFinder, Loogle, and source grep ran
successfully, with all searches recorded by msearch.py.

## New nodes

`lem-sc-affine-pushforward-stalk-localization` in
`dag/nodes/sec-picard-framework/lem-sc-affine-pushforward-stalk-localization.json`,
realized by `Sheaf.AlgebraicGeometry.AffinePushforwardStalkLocalization`. It is fully
proved and records precisely the pushforward-stalk step of Tag 0AVW. Its proof covers
an empty source or inverse image (zero section and stalk rings) without a nonempty
assumption. No change record is needed.

## Second reading by C2

1. **Visibility and statements.** Compared the delivered `AffineAlgebraStalkFlat.lean` declaration with the repository version byte for byte; the target signature and all existing declarations are unchanged. The helper is a new declaration with its own node and module. Verdict: pass.
2. **Proof and axioms.** Compiled both modules with `lcompile.py --all`; both compile without warnings or `sorry`. A scratch import reports only `propext`, `Classical.choice`, and `Quot.sound` for each theorem. No forbidden declarations or hollow definitions occur. Verdict: pass.
3. **Split-off statement.** Checked the helper's localization statement against the affine basic-open and stalk definitions, including the empty inverse-image case. It is strictly the missing pushforward-stalk calculation, is used by the target proof, and is not duplicated in the library. Verdict: pass.
4. **Pruning and route.** The target proof uses the affine pushforward localization helper, affine-open stalk localization, and localization flatness; no old proof dependency is unused and no unit route is bypassed. Verdict: pass.
5. **DAG agreement.** Updated target-node proof steps and dependencies to match the Lean proof, and added the helper node with source, proof, searches, Lean record, and unit/chapter metadata. Verdict: pass.

Changed only the target proof, the proof-only helper import, the new helper module/node, and the corresponding target-node proof metadata. No statements or definitions were changed.
