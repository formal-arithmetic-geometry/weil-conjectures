## What changed

Added two proved public API theorems to
`Sheaf.AlgebraicGeometry.GlobalHomAdjunctionIso`:
`AlgebraicGeometry.schemeHomTensorPullbackIso_isCanonical` exposes the canonical
predicate retained by the componentwise reconstruction, and
`AlgebraicGeometry.schemeHomTensorPullbackIso_unique` proves equality of the entire
isomorphism with any other isomorphism satisfying that predicate. The proof uses
`IsCanonicalPullbackTensorComparison.unique`, natural-transformation extensionality
and isomorphism extensionality. No existing signature, visibility, definition,
import or target statement changes. Updated the item's node to record these proofs.

This is a partial repair certificate for the queued tensor-data audit, relative to
the existing shared counit. It is not a claim that the separate counit-normalization
repair is complete. In particular `schemeHomPullbackAdjunction` retains its existing
body; the upstream normalization discussed in `coord/hollow-definitions.md` remains
open. There are no new chosen objects and no new proof holes.

## Proved and sorry left

The supplied checkout already contains zero textual sorries in this module.
Closed existing holes: none. Added holes: none. Newly proved declarations:

- `AlgebraicGeometry.schemeHomTensorPullbackIso_isCanonical`
- `AlgebraicGeometry.schemeHomTensorPullbackIso_unique`

Both belong to `lem-pc-global-hom-adjunction`. The second theorem identifies the
inverse as well as the hom transformation; it is not merely componentwise
invertibility. Its hypothesis uses exactly the existing canonical predicate and
therefore retains the existing counit normalization. Every sorry left in the
item's module or added by this delivery: none.

## No longer needed

None. All existing imports and proof dependencies are retained. No blueprint unit
or proof step is bypassed. The unit has no realized nodes for this item.

## Where the brief, the DAG or earlier work was wrong

The dispatch brief describes a module with sorry, but the current source has none:
the previous Q3 repair is already present. `coord/repairs.txt` still lists the module
for undetermined adjunction/tensor data. The prior Q3 change record explicitly leaves
adjunction normalization open. This delivery supplies a checked whole-isomorphism
uniqueness certificate at the fixed canonical predicate; it does not resolve the
upstream fresh-counit ambiguity and does not claim net hole-closing progress.
The uniqueness proof is valid for arbitrary schemes and arbitrary canonical tensor
isomorphisms, with no extra geometric hypotheses or edge-case exclusions.

## Second reading by R1

1. Compared the delivered module and node with the repository versions. The existing declaration signatures and definitions are unchanged; only the component reconstruction proof and the two new theorem declarations/node proof metadata differ. Verdict: pass.
2. Compiled the sandbox module set with `lcompile.py --all`; it succeeds. No textual `sorry`, forbidden declarations, or hollow definitions occur in the delivered module. Axioms for the two new theorems are only `propext`, `Classical.choice`, and `Quot.sound`; the target's existing imported `sorryAx` remains outside this proof. Verdict: pass.
3. Checked the two split-off statements against the existing canonical predicate and its `unique` theorem. The first is exactly the chosen witness's specification; the second identifies hom components by that uniqueness and then uses natural-transformation and isomorphism extensionality, so it fixes the whole isomorphism. No duplicate declaration was found in the library, and a Mathlib search found no matching theorem. Verdict: pass.
4. The proof takes the existing monoidal-realization route and preserves the item's canonical predicate and imports; no shorter applicable route was found. No imports or proof dependencies were removed, and no blueprint unit is bypassed. Verdict: pass.
5. The node proof text, proof dependencies, proof origin, and Lean declarations agree with the delivered code. Verdict: pass.

Changed after review: appended this second-reading record and recorded the Mathlib search in `searches.jsonl`; no Lean proof repair was necessary.
