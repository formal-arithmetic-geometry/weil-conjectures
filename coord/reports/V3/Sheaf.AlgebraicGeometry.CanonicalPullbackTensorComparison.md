## What changed

Completed the private `counit_isIso` and `modelMap_isIso` lemmas and the public
`IsCanonicalPullbackTensorComparison.unique` theorem. The canonical-existence
transport theorem remains as its original named `sorry`; the existence wrapper
continues to apply it. Added proof-only imports for K-flat pullback and K-flat
resolution.

## Proved and sorry left

Closed `AlgebraicGeometry.IsCanonicalPullbackTensorComparison.unique`, together
with the auxiliary private isomorphism lemmas `counit_isIso` and
`modelMap_isIso`. The remaining sorry is
`AlgebraicGeometry.exists_canonical_from_model` (node
`def-pc-derived-pullback-tensor-comparison-model-transport`), which is the
K-flat descent construction and is left as the existing named lower hole.

Holes closed: `AlgebraicGeometry.IsCanonicalPullbackTensorComparison.unique`.
Holes added: none. The private auxiliary lemmas are proved and add no holes.

## No longer needed

None of the existing proof-dependency nodes are pruned. The proof uses the
K-flat pullback and K-flat resolution modules, in addition to the module's
existing imports.

## Where the brief, the DAG or earlier work was wrong

The earlier attempt had the uniqueness proof and auxiliary arguments in a
scratchpad but left them disconnected from the delivered module. The target node had no proof route, and the transport node pointed backward to the canonical comparison node; this reading repaired the proof metadata. No statement correction was needed.

## Second reading by V3

1. Compared the delivered module against the repository version. Existing declarations and target statements are unchanged; only proof imports, private proof helpers, and the uniqueness proof differ. Verdict: pass.
2. Compiled the module locally with `lcompile.py`; the scratch axiom copy compiled in 52.5 seconds. `#print axioms` showed only `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx` from existing lower statements (the model-map helper has no `sorryAx`); there are no errors, `sorry` remains only in the named `exists_canonical_from_model` theorem, and no forbidden declarations were added. Verdict: pass.
3. Checked the split-off theorem and existing node. The remaining lower hole is the documented K-flat descent transport theorem, with its source and an expanded explicit counit-comparison proof description; no new split-off statement was added. Searched leanfinder, loogle, and grep using natural-transformation determination and localization-counit queries. Generic derived uniqueness and monoidal invertibility are reused; no exact replacement was found. The zero-complex and identity-morphism cases impose no extra hypotheses, and conjugation by the counit comparison preserves the pinned equation. Verdict: pass.
4. Reviewed the route and imports. The proof uses the shared derived counit, K-flat pullback preservation, and the derived monoidal localization map; the unit route is preserved. No old proof-dependency node can be pruned. Verdict: pass.
5. Updated both existing nodes' proof, proof dependencies, and proof origin to match the implemented uniqueness route and the remaining transport plan; the existing target statement and unit metadata remain unchanged. Verdict: pass.

Changed the unnecessary `synthInstance.maxSize` option and removed two unused simp arguments. Updated the existing DAG proof metadata to record the uniqueness route and removed the transport plan's backward dependency on the canonical comparison node. Expanded the remaining theorem's proof docstring to describe conjugation by the natural counit comparison. No unit realized field changed.
