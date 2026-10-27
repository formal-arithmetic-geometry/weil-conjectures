# Stage-1 delivery: lem-sfb-separable-field-extension-transitivity

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-separable-field-extension-transitivity.json`: existing statement, split into five steps; no Mathlib match for the full, possibly transcendental statement.
- `citations.json`: one verbatim statement quote for each node used in each step.
- `report.md`: this report. `searches.jsonl` is the search command's own log.

New nodes: 0. New Mathlib leaves: 0. The statement and statement dependencies are unchanged.

## Attachments

None. Searches of `lean/WeilConjectures/` for the blueprint tag, separability/transitivity vocabulary, and `IsSeparableExtension` found no declaration giving the item. The existing `Algebra.IsSeparableExtension` is a definition (SeparableExtension.lean:44-46). The project's uses of `Algebra.IsSeparable.trans` concern algebraic separability. A Mathlib theorem is not an attachment.

## WANTED

None. The sources actually needed are available locally.

## Problems found and changes

The imported item had no proof. Its source suggests the correct reduced-tensor route, but an application of Mathlib `Algebra.IsSeparable.trans` would change the notion and exclude transcendental extensions. I retained the two historical searches in the node and appended the six searches actually run with msearch.py in this session. Read hits include Separable.lean:539,549-550,570-572 and SeparableDegree.lean:835-839. The minimal-polynomial definition in those hits forces algebraicity; neither phrasing of the semantic search yielded the item's predicate or a one-line specialization. Loogle reports the project's `Algebra.IsSeparableExtension` as an unknown identifier, accurately recorded as a search result rather than a service outage.

A second potential gap is to apply a separably-generated theorem to an arbitrary separable extension. Steps 2 and 3 instead extract the finitely many field elements in a tensor expression, use the hypothesis on their generated intermediate field, and use flat tensor injectivity to descend nilpotence to that smaller tensor. Both are applications to the actual fields in this tower, with every non-elementary input already a cited node. No standalone general lemma is asserted without proof or citation.

The existing blueprint ancestry has a broken `created.item` chain: `tools/blueprint_refs.py ancestor lem-sfb-separable-field-extension-transitivity` returns None, whereas the inherited place and via list explicitly trace back to `det-thm-sf-ctf-stability-direct-images` paragraph (3). I preserved the existing null `from.node`, filled no invented blueprint id, retained the precise inherited place/via, and documented this in split_report. I read the current `literature/blueprint/latest/.../sk-thm-sf-ctf-stability/_section.md` and `sk-thm-sf-ctf-stability-direct-images.{md,proof.md}`; this is a field-algebra detail below its direct-image/alteration route. Whole-blueprint searches for separable, transitivity and separable.*extension and DAG searches for the tags and concepts found no node stating this complete tower assertion. No chapter or unit file is changed.

## Unfinished work

None in the one-level split. Existing cited nodes retain their own states; no Lean was written or compiled.

## Not duplicates

No new nodes were created. The existing 030U node `lem-weil-pbc-separably-generated-tensor-reduced` is used with its exact, narrower hypothesis (separably generated). The existing 030W node `lem-weil-pbc-geometrically-reduced-extension-separable` supplies the final positive-characteristic implication. I did not duplicate either by creating the full 030U statement or another version of the separability criterion.

## Review by Q156

I read Stacks `algebra.tex`, Tag 030U (`lemma-separable-extension-preserves-reducedness`), including its separate separable and separably-generated cases, and Tag 030W (`lemma-characterize-separable-field-extensions`), including the four equivalent conditions and the proof. I also checked the characteristic-zero assertion in the proof of Tag 00TX (`lemma-characteristic-zero-local-smooth`), the tensor universal property in 00CX (`lemma-tensor-product`), and the tag/label mapping for 030U and 030W. There are no new-node sources to review. The node's proof is marked agent assembly because the transitivity corollary and explicit reassociation are assembled here rather than copied as a theorem from Stacks.

For step 1 I opened `lem-weil-pbc-char-zero-field-extension-separable`: it gives arbitrary field extensions in characteristic zero in the required sense, so it directly applies to L/k. I opened `lem-weil-pbc-algebra-tensor-pushout-universal-property`: its first clause supplies the commutative tensor ring and its multiplication, and the remaining clauses supply the maps used in step 4. Positive characteristic of a field is prime; no perfection assertion is used.

For each of steps 2 and 3 I opened all five cited nodes. The definition of separable field extension quantifies over precisely the finitely generated intermediate fields k(a_i) and K(b_j), respectively. The module-tensor definition explicitly says pure tensors generate; finite sums are consequently enough for each chosen element. `lem-weil-pbc-separably-generated-tensor-reduced` states reducedness for an arbitrary reduced commutative algebra, with the field extension separably generated. At the first application that algebra is E, a field, and at the second it is R = K tensor_k E, already proved reduced but not asserted to be a field. `lem-weil-pbc-module-over-field-flat` makes E flat over k and R flat over K. The *statement* of `lem-trf-flat-tensor-preserves-injection`, not merely a definition of flatness, then supplies the needed injections for K_0 into K and L_0 into L. I checked its source declaration in Mathlib/RingTheory/Flat/Basic.lean:131. The swaps are given and inverted explicitly from bilinearity. The induced maps preserve products on pure tensors, hence nilpotence. Injectivity is used to reflect the equation x_0^n = 0, not to assume a nilpotent lift without justification.

Step 4 cites the module and algebra tensor universal properties whose statements I opened. Its formulas are balanced over the indicated bases, and the inverse identities are checked on pure tensors using K-balancing. Thus the claimed isomorphism is proved in the step, without hiding an identification in a new statement. This is the sole elementary step: it is a direct generators-and-relations calculation. The other steps are marked non-elementary and name every field-algebra theorem or flatness result they use.

For step 5 I opened `lem-weil-pbc-geometrically-reduced-extension-separable`: its hypothesis is reducedness for EVERY extension field of k and positive prime characteristic, with no algebraicity assumption. E was arbitrary in steps 1-4, so exactly these hypotheses hold. I did not use its proof, infer arbitrary-field geometric reducedness from Mathlib's algebraic-field test, or replace a universal quantifier by one extension field.

I tested the argument on k=K, K=L, the trivial tower, empty tensor sums, algebraic separable towers, and purely transcendental towers k subset k(t) subset k(t,u). It uses no finite-generation assumption on K or L. A tensor of two fields can have zero divisors; the proof consistently needs reducedness only. As a negative check, over k=F_p(s), the extension k(s^(1/p))/k has a nonzero nilpotent in its tensor with itself, generated by the difference of the two copies of s^(1/p); it fails the separability hypothesis, as it should. The finite-tensor argument also works for the zero reduced algebra. No new statement with omitted hypotheses or untested finiteness was introduced.

Against delivery-errors B-E: there are no new nodes, no relocated clauses of the item, no source or hypothesis corrections, no SGA citations, and no hidden theorem justified only by a tag. Every cited statement is copied verbatim into citations.json for its step, proof_deps is exactly the union of uses, and every proof step is shorter than 2000 characters. The two off-unit non-leaf uses are generic field-algebra tools, declared in split_report.tool_uses with their roles; the unit has no replacement for them. All edits are confined to this sandbox.
