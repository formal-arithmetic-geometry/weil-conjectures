## What changed

Proved the étaleness witness for `p'` by transporting étaleness of the pullback projection across the isomorphism `ι`. The remaining displayed unit compatibility equality is isolated in the new module `Sheaf.Paper.EtaleRestrictionPullbackUnitEq` as a named intermediate theorem with `sorry`, and the target theorem applies it.

## Proved and sorry left

`AlgebraicGeometry.etale_restriction_pullback_unit` is proved up to the split intermediate theorem. The new declaration `AlgebraicGeometry.etale_restriction_pullback_unit_eq` remains `sorry` (node `lem-weil-pbc-etale-restriction-pullback-unit-eq`).

## No longer needed

No stated proof dependency was removed; the parent theorem now additionally imports the split equality module.

## Where the brief, the DAG or earlier work was wrong

The five-step equality proof is substantial and could not be completed within this item; it is represented as a strict intermediate theorem after the independent étaleness witness is proved.

## New nodes

`lem-weil-pbc-etale-restriction-pullback-unit-eq` records the equality portion of the parent argument with an explicit `Etale p'` witness.

## Earlier second reading (a previous round; superseded)

A second worker should verify that the transported étale instance uses the arrow isomorphism induced by `ι`, and that the split equality has exactly the parent theorem's displayed conclusion.

## Second reading by E1

1. Compared the delivered parent module with the repository version. The theorem statement is byte-for-byte unchanged; only its proof and an import were added. Verdict: pass.
2. Compiled both delivered modules with `lcompile.py --all`; they compile without errors. The only remaining `sorry` is the named split theorem `AlgebraicGeometry.etale_restriction_pullback_unit_eq`, with its DAG node. No forbidden declarations or hollow definitions were introduced. Verdict: pass.
3. Checked the split statement against the parent display and tested the transported `Etale p'` construction through `MorphismProperty.arrow_mk_iso_iff`; the split theorem fixes the witness and is strictly stronger than the existential parent conclusion. Searches found no duplicate declaration. Verdict: pass.
4. The proof follows the shortest available route for the proved portion: base-change étaleness transported across `ι`, then the explicitly named equality theorem. The parent node proof and dependencies were updated to match the Lean proof. The unit route is retained because the parent node remains the realized theorem. Verdict: pass.
5. Imports were reviewed: `UpperLowerStar.Defs` is public because the theorem signatures use its declarations; no proof-only stated dependency was removed. Verdict: pass.

Changed the report, made `UpperLowerStar.Defs` public in both modules, and synchronized the parent DAG node's proof, dependencies, and origin with the Lean proof.
