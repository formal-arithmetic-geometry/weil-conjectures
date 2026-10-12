## What changed
Added the required public import of `DerivedPullbackMonoidalModel` (its type
appears in a public intermediate theorem) and reduced
`exists_canonicalPullbackTensorComparison` to the strictly stronger-hypothesis
transport theorem `exists_canonical_from_model`. The transport theorem remains a
named sorry for the K-flat descent argument.

## Proved and sorry left
The target existence theorem is proved from `exists_derivedPullbackMonoidalModel`
and `exists_canonical_from_model`. Sorry remains in
`exists_canonical_from_model` (node
`def-pc-derived-pullback-tensor-comparison-model-transport`) and in
`IsCanonicalPullbackTensorComparison.unique` (the existing target node).

## No longer needed
No imports were pruned; all original imports remain used by the definitions and
predicate. No existing nodes were bypassed.

## Where the brief, the DAG or earlier work was wrong
The DAG omitted the intermediate transport statement needed to connect the
already available monoidal-model descent theorem to the canonical predicate.

## New nodes
`def-pc-derived-pullback-tensor-comparison-model-transport` records the strict
intermediate theorem used by the existence proof.

## Second reading by T3

1. Compared the delivered module with the repository version. Existing declaration
   signatures and definitions are byte-for-byte unchanged; the only interface additions
   are the documented transport theorem and its required public import.
2. Compiled the module with `lcompile.py`; it succeeds with the two explicitly reported
   named `sorry` declarations and no forbidden declaration forms. The remaining sorry in
   `IsCanonicalPullbackTensorComparison.unique` is the pre-existing target hole.
3. Checked the split statement and node. `exists_canonical_from_model` is a true strict
   intermediate consequence needed to transport the model, with hypotheses stronger than
   the target; its docstring, source, declaration, and DAG node agree. No duplicate library
   declaration was found.
4. Checked the proof route and imports. The target now applies the available
   `exists_derivedPullbackMonoidalModel` theorem and the transport theorem. The public
   import is necessary because the intermediate theorem exposes `IsDerivedPullbackMonoidalModel`;
   no unused imports or bypassed unit steps were found.
5. Checked the DAG metadata and unit route. The new node records the transport step and
   keeps the existing unit route; proof dependencies match the proof as written.

Changed only the report after this reading; no further Lean or DAG changes were needed.

