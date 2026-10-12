## What changed

Added a proof of `etaleSmallGenerator_sections_small` from a named auxiliary theorem asserting the required small-model surjection. Added the auxiliary module and DAG node; the auxiliary theorem remains a documented proof obligation.

## Proved and sorry left

`AlgebraicGeometry.Scheme.etaleSmallGenerator_sections_small` is proved by `small_of_surjective`.
`AlgebraicGeometry.Scheme.etaleSmallGenerator_sections_surjective` remains `sorry`; it is the strict intermediate cardinal construction described in its docstring and DAG node.

## No longer needed

No imports or planned nodes were pruned.

## Where the brief, the DAG or earlier work was wrong

The original plan requires the substantial affine-model and covering cardinal construction, which cannot be discharged from the currently available declarations in this session. It was split into the explicit surjection theorem.

## New nodes

`lem-sc-etale-small-generator-sections-surjective`.

## Earlier second reading (a previous round; superseded)

The main theorem is checked against the auxiliary theorem and `small_of_surjective`; the remaining sorry is the affine-model cardinal construction.

## Second reading by T2

1. **Visible changes and statements.** Compared the delivered module with the repository version. The theorem signature of `etaleSmallGenerator_sections_small` is byte-for-byte unchanged; the only interface addition is the explicitly documented auxiliary theorem and its new split node.

2. **Compilation and proof.** Compiled both sandbox modules with `lcompile.py --all`; both compile cleanly. The main theorem is proved by `small_of_surjective`; the only remaining `sorry` is the named auxiliary theorem `etaleSmallGenerator_sections_surjective`, and no definition contains `sorry`.

3. **Split statement.** The auxiliary surjection statement is strictly simpler than the target, has a source, docstring proof plan, and matching DAG node. It is not duplicated by an existing declaration found in the imported library.

4. **Pruning and route.** The proof uses the auxiliary surjection and `small_of_surjective`; no prior proof dependency or import can be removed without losing the route. The unit route is retained through the target node and its stated dependency.

5. **DAG agreement.** The target node records the auxiliary node in `proof_deps` and the proof step matches the Lean proof. The auxiliary node records its declaration, source, proof plan, and split status consistently.

**Changes made:** added this second-reading report section; no code or DAG repairs were needed after compilation and comparison.
