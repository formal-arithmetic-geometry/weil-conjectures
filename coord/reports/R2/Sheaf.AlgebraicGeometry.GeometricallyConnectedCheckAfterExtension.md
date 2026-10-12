## What changed

Proved `AlgebraicGeometry.geometricallyConnected_iff_of_fieldExtension` without changing
its statement or visibility. The forward implication uses Mathlib's base-change instance.
The converse uses the already proved `Field.exists_common_extension`, constructs the
comparison morphism by `pullback.lift`, and verifies its pullback square by pasting and
cancellation. Connectedness descends along the continuous surjective first projection.
This is the proof of [Stacks, Tag 054N](https://stacks.math.columbia.edu/tag/054N).

Replaced the proof import `Sheaf.AlgebraicGeometry.BaseChangeConventions` with
`Mathlib.AlgebraicGeometry.PullbackCarrier`. Updated the existing node's proof and proof
dependencies to record the direct pullback argument. Public imports are unchanged.

## Proved and sorry left

Closed the single hole in
`AlgebraicGeometry.geometricallyConnected_iff_of_fieldExtension`
(node `lem-weil-geometrically-connected-check-after-extension`).
No holes remain in the item; no holes were added or split off. The used common-extension
lemma is already proved in the current library. The final dry run checks the declaration's
axioms as well as compilation.

## No longer needed

Removed the proof import `Sheaf.AlgebraicGeometry.BaseChangeConventions`.
The proof no longer uses `baseChange_iterated` or any other declaration of that module,
including its unrelated module-pullback, fibre, and section interfaces. Removed
`def-pc-base-change` from proof dependencies, replacing it with the existing Mathlib leaf
`def-pc-fibre-product`; the statement dependency on base change remains unchanged.

Retained `Sheaf.FieldTheory.CommonExtensionFields` and
`lem-weil-common-extension-fields`. The geometric-connectedness definition remains
needed; surjectivity of the projection is supplied by Mathlib's instance rather than
`lem-weil-pbc-surjective-base-change`.
No claim is made that the removed module is globally unreachable from other targets.
The unit's `realized` lists are empty; no unit statement or step is bypassed.

## Where the brief, the DAG or earlier work was wrong

No mathematical error was found. The planned base-change identifications can be expressed
directly with Mathlib's pullback universal property, pasting, and cancellation, so the
large project-specific base-change conventions module is unnecessary for this proof.
The common-extension result is already proved, rather than an outstanding lower hole.

## Second reading by R2

1. **Statements and interfaces.** I compared the delivered module with the repository version. The theorem signature, universes, visibility, and public statement imports are unchanged byte for byte. Verdict: unchanged.

2. **Proof correctness and trust.** `lcompile.py` compiles the module without errors or warnings. The target has no `sorry`; no `axiom`, `unsafe`, `opaque`, `extern`, `implemented_by`, or hollow definition was introduced. Verdict: passes.

3. **Split-off statements and searches.** No new theorem or split-off statement was added. The proof uses existing declarations and Mathlib instances, so no duplicate statement or new node is required. Verdict: no split-off issue.

4. **Pruning and route.** The proof-only import of `Sheaf.AlgebraicGeometry.BaseChangeConventions` is removed because its declarations are unused; `Mathlib.AlgebraicGeometry.PullbackCarrier` supplies the direct pullback API. The DAG proof dependencies now omit the removed project surjectivity lemma and match the implemented common-extension and pullback argument. The unit has no realized entries, so no unit step is bypassed. Verdict: pruning is justified.

5. **DAG agreement.** The node's proof text, dependencies, and origin agree with the Lean proof, including Mathlib's base-change stability of `Surjective`; the hole accounting reports one closed hole and no additions. Verdict: agrees.

I changed the DAG proof dependency text and appended this second-reading section; no Lean statement or definition was changed.
