## What changed

Proved `AlgebraicGeometry.isSeparated_of_surjective_universallyClosed` in
`lean/Sheaf/AlgebraicGeometry/IsSeparatedOfSurjectiveUniversallyClosed.lean`, preserving its
signature, visibility and docstring. Added the proof-only import
`Mathlib.AlgebraicGeometry.Morphisms.Immersion`.

The proof follows the existing five-step DAG plan without changing its route:
`MorphismProperty.pullbackMap` gives universal closedness of the product map;
`pullback.hom_ext` proves the commuting diagonal square; closedness of the composite follows
from the separated source diagonal and universal closedness; surjectivity identifies its
range with the target diagonal's range; `IsClosedImmersion.of_isPreimmersion` and Mathlib's
diagonal immersion instance give the target's separatedness. All ingredients are Mathlib
lemmas or instances already represented by the node's dependencies. No node update is needed.

## Proved and sorry left

Closed one hole:
`AlgebraicGeometry.isSeparated_of_surjective_universallyClosed`
(node `lem-weil-pbc-surjective-universally-closed-separated`).

No holes remain in the item. No holes were added or split off. The single-file compile
succeeded without warnings; the delivery dry run checks its axioms.

## No longer needed

None. No imports were removed, and all existing proof dependencies remain used. In particular,
`lem-weil-pbc-universally-closed-product-map`, `lem-weil-pbc-diagonal-immersion` and
`lem-weil-pbc-immersion-closed-image-closed-immersion` are used through their recorded Mathlib
matches. The public `Mathlib.AlgebraicGeometry.Morphisms.Proper` import is preserved.

## Where the brief, the DAG or earlier work was wrong

No mathematical or interface error found. The planned dependencies are usable Mathlib
results, so no new intermediate statements, interface changes or forced adaptations are
necessary. The referenced Stacks source files are not present in this clone; the proof was
checked against the existing node and the actual Mathlib statements and instances.

## Second reading by G2

1. Compared the delivered module with the repository version. The theorem signature,
   visibility, docstring, and namespace are byte-for-byte unchanged; the only additions are
   the proof and its proof-only `Mathlib.AlgebraicGeometry.Morphisms.Immersion` import.
   Verdict: pass.
2. Compiled the module with `lcompile.py` and checked `#print axioms`; it has no `sorry`,
   `axiom`, `unsafe`, `opaque`, `implemented_by`, or `extern`, and its axioms are only
   `propext`, `Classical.choice`, and `Quot.sound`. Verdict: pass.
3. Checked the proof against the target node and searched the repository for duplicate
   declarations. The proof closes exactly the target theorem, introduces no split-off
   statements, and uses existing Mathlib declarations and instances. Verdict: pass.
4. Checked the route from the top downward. The pullback map, diagonal square, closed-image
   argument, surjective range equality, and closed-immersion conclusion implement all five
   DAG steps. Imports are minimal for the proof and no old dependency is unused. Verdict:
   pass.
5. Checked the target node's statement, `proof`, `proof_deps`, and `proof_origin` against the
   Lean proof; they agree, and the unit route remains represented. Verdict: pass.

Changed only the proof and the proof-only immersion import; no statements, definitions, DAG
nodes, or dependencies required repair.
