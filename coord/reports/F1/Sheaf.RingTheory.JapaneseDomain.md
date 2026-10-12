## What changed

Replaced the sole `sorry` in `lean/Sheaf/RingTheory/JapaneseDomain.lean`, in
`isN1_of_isN2`, with `exact h K`. This specializes the N-2 hypothesis to the trivial
finite extension K/K; Mathlib supplies the self-algebra, scalar tower and finite-dimensional
instances. Both definitions and the theorem signature are unchanged. The proof follows the
node's stated argument. The second reading records that argument explicitly in the DAG proof metadata, without changing the route.

## Proved and sorry left

Closed: `isN1_of_isN2` (node `def-weil-pbc-japanese-domain`).
One of one original holes is proved, with no holes added or split off.
No `sorry` remains in the module. The single-file compile passed without warnings.

## No longer needed

None. All three existing public imports supply notions used in the definitions and signatures:
integral closure, fraction fields and finite-dimensional extensions. There were no proof-only
imports or proof-dependency nodes to prune, and none were added.

## Where the brief, the DAG or earlier work was wrong

None. This item's sole proof is the definitional specialization L = K already stated in the
node and docstring; it does not require the longer decomposition workflow. The unit's route
is preserved. Searches of the source library and Mathlib found no existing N-2-to-N-1 theorem;
no additional finiteness theorem is necessary.

## Second reading by F1

1. PASS: compared the sole delivered Lean module with the repository using `diff -u`.
   The only difference is `sorry` replaced by `exact h K`; every existing signature,
   definition, docstring and import is byte for byte unchanged. No change record is needed.
2. PASS: the prescribed single-file local compiler completed without errors or warnings.
   A scratch copy with `#print axioms` for `IsN1`, `IsN2`, and `isN1_of_isN2` showed
   only `propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx`.
   The printed theorem term is `fun ... h ↦ h K`. There are no remaining holes,
   forbidden declarations, or data chosen from unproved existence theorems.
3. PASS: no statements were added or split off. Checked the trivial extension K/K:
   its dimension is one, its self-algebra and R/K/K tower are canonical, and its
   integral closure is exactly the object used by `IsN1`. Thus the proof applies to
   every domain and fraction field in the unchanged signature. Independent searches
   in `lean/Sheaf` and `lean/WeilConjectures` found no alternate existing N-2-to-N-1
   theorem; an additional Mathlib grep searched self-finiteness and scalar towers.
4. PASS: direct specialization is the shortest route. Each public import supplies
   notions used in public definitions: integral closure, fraction fields, and
   finite dimensionality. There are no old proof dependencies to prune. Inspected
   `dag/units/sk-thm-p1.json` and searched the unit records: this definition is not
   a directly realized unit step, and the existing unit route is preserved.
5. PASS after metadata repair: the node is a definition whose statement already
   includes N-2 implies N-1, but its `proof` was empty and `proof_origin` was null.
   Recorded the elementary K/K specialization and its Stacks source, retaining
   empty `proof_deps`. No node statement, Lean record, or unit record changed.

Second reading changed only the existing node's proof metadata and this report.
The Lean proof was correct and is retained unchanged. Closed one original hole
(`isN1_of_isN2`); added zero holes; no decomposition or pruning.
