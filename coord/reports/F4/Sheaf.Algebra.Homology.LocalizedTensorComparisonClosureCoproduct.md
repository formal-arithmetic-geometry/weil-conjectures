## What changed

Added the fixed representative/model/degree intermediate theorem and reduced the original coproduct closure theorem to it. The intermediate theorem remains `sorry`; the original theorem is proved by introducing its data and applying the intermediate component.

## Proved and sorry left

`ModuleCat.localizedTensorComparisonProperty_closure_coproducts` is proved. The new declaration `ModuleCat.localizedTensorComparisonProperty_closure_coproducts_fixed_degree` remains `sorry` and is recorded by node `lem-pc-localized-tensor-comparison-closure-coproducts-fixed-degree`.

## No longer needed

None; the planned associator import remains part of the intermediate theorem's proof dependencies.

## Where the brief, the DAG or earlier work was wrong

The DAG plan requires substantial coproduct identification and naturality arguments absent from the available interfaces, so the fixed component was split out as a strict intermediate theorem.

## New nodes

`lem-pc-localized-tensor-comparison-closure-coproducts-fixed-degree` in `dag/nodes/sec-picard-framework/lem-pc-localized-tensor-comparison-closure-coproducts-fixed-degree.json`.

## Earlier second reading (a previous round; superseded)

The intermediate theorem fixes a representative, model and degree, while the original theorem quantifies over all of them and is reduced by genuine introductions and application. The coproduct hypotheses and empty-index case remain unchanged.

## Second reading by F4

1. Compared the delivered module with the repository version. The original theorem's
   signature is byte-for-byte unchanged; only its proof and the documented fixed
   component were added.
2. Compiled the module with `lcompile.py`. It compiles cleanly. The only remaining
   `sorry` is the named fixed-degree theorem; no forbidden declarations or hollow
   definitions were introduced.
3. Checked the fixed-degree statement against the definition of
   `localizedTensorComparisonProperty`: it is the explicit representative/model/
   degree component, with no weakened conclusion or added mathematical assumption.
   It is recorded by the matching DAG node and has the required source and proof
   documentation. No existing declaration duplicates it.
4. The proof takes the direct introduction/application reduction. The associator
   import remains needed by the split theorem's planned proof; no unused import was
   found and no pruning is justified.
5. The node's Lean declaration, statement, proof dependencies and proof origin agree
   with the delivered file. The unit route is preserved; the target is reduced to
   the fixed component without changing its quantifiers or empty-coproduct case.

Changed the report only; no Lean proof or statement was altered during this reading.
