## Worker report

Files written:

- `dag/nodes/sec-six-functors-basics/lem-sfb-compact-parameter-functional.json`: statement, split; the statement and its statement dependencies are unchanged. Five proof steps use the existing compact-product neighbourhood Mathlib leaf. The full item is not a Mathlib leaf.
- `citations.json`: the statement quotation supporting the sole node citation, in step 2.
- `searches.jsonl`: actual msearch results from this session; all are recorded in the item, alongside the preserved searches from its creation.
- `report.md`: this report and signed direct-delivery review.

New nodes: **0**. New Mathlib leaves: **0**. Reused Mathlib leaf: `lem-sfb-compact-product-open-neighborhoods` (`generalized_tube_lemma`).

Attachments: none. Searched `lean/WeilConjectures/` for the item tag, compact-parameter / contractive-functional terminology, and supremum/function-space terminology. No declaration gives the item's clauses; no upstream sorry declaration is counted as an attachment.

WANTED: a published reference for the exact compact-parameter contractive-functional assertion of `lem-sfb-compact-parameter-functional`, in the generality of arbitrary normed fields and with the displayed quantitative bound and module/naturality identities; the inherited source does not identify a document or theorem number. This delivery supplies an agent-written proof instead. The non-elementary compact-product input is already available as a Mathlib leaf, whose source was read.

What needed repair: the item had no proof. Its source is an agent-extracted analytic auxiliary, not a theorem stated in the blueprint paragraph it serves. The latest direct-images proof paragraph (3) was read: it invokes the open direct-image coefficient theorem, and contains no assertion about a functional on continuous functions. I therefore kept the statement, recorded the actual derivation as `proof_origin.by = agent`, and did not pretend to quote that paragraph as an analytic proof. There is no statement dispute and no change of coefficient hypotheses or unit route.

Nothing mathematical remains unfinished for this one-level split. This item is not the unit's key node, so no unit realization fields are changed.

## Mathlib and duplicate searches

Read the existing node's earlier search results; retained all of them, including the unavailable LeanSearch result with its original verdict. The new msearch log includes LeanFinder and LeanSearch queries for the parameterwise operation, Loogle queries for curry and postcomposition, and Mathlib grep queries for continuous currying, supremum norms, contractivity and postcomposition. Read `ContinuousMap.curry` and `curry_apply` at `Mathlib/Topology/CompactOpen.lean:430–436`, the compact norm and comparison statements at `Mathlib/Topology/ContinuousMap/Compact.lean:182–219`, and `ContinuousLinearMap.compLeftContinuous` at `Mathlib/Topology/ContinuousMap/Algebra.lean:595–598`. The latter only postcomposes a continuous family and is linear over its fixed scalar semiring; it does not alone give the uniform epsilon estimate, the function-ring scalar action or parameter naturality. Thus the full item needs the explicit short argument.

Whole-DAG statement/concept searches for compact-open, supremum norm, uniform continuity, finite subcover and compact-product neighbourhoods located `lem-coef-compact-open-currying`, `lem-sfb-compact-function-space-complete` and `lem-sfb-compact-product-open-neighborhoods`. The complete-function-space node requires a complete target, so using it would add a hypothesis absent here; it is not used. The compact-open currying node would require a separate topology comparison for the desired norm estimate, so it is not needed either. The existing compact-product node states exactly the general compact-neighbourhood fact the proof needs. No duplicate node was created.

`tools/blueprint_refs.py search` was run for curry, compact-open, supremum norm, contractive and compact-parameter. No blueprint node states the full item. `ancestor lem-sfb-compact-parameter-functional` returns `None`; the existing null `blueprint.from.node` and its inherited `via` chain are preserved, and the already specified `from.place` remains intact. `same_as` is `[]`. Read the latest blueprint's `sk-thm-sf-ctf-stability/_section.md`, its direct-images proof, the recorded unit and chapter, and the three-level route policy in SETUP.md.

## Not duplicates

No new nodes. The proof reuses `lem-sfb-compact-product-open-neighborhoods` directly.

## Review by Q135

I read the item's complete statement, its agent-extraction source description, the latest direct-images proof paragraph (3), and every statement used by its proof. I compared the compact-product node with `generalized_tube_lemma` in `Mathlib/Topology/Compactness/Compact.lean:752–759`: it concerns arbitrary topological spaces and compact subsets and assumes only an open set containing their product. It supplies open product neighbourhoods with precisely the inclusions used here; neither a separation condition nor a nonemptiness condition is hidden. There are no new-node sources to review.

Step 1 introduces the actual sections by composition with `x ↦ (p,x)`, and the open set is the preimage of `(-∞, epsilon/2)` under the continuous real norm-difference map. Subtraction is continuous in a normed field, and norm continuity follows from the triangle inequality. This is an elementary construction, with no compact-open/supremum-topology identification asserted.

Step 2 is the only non-elementary step and cites `lem-sfb-compact-product-open-neighborhoods`. I checked its statement, not an argument inside its proof: substituting the two ambient spaces `P, X` and compact subsets `{p0}, X` gives open neighbourhoods `V, O`. The open set from step 1 contains their compact product because the difference is zero on `{p0} × X`. The second neighbourhood is all of `X`, because it is a subset of `X` containing `X`. The displayed pointwise bound follows for every `x`. Singleton compactness was written out from the open-cover definition. The verbatim quotation in `citations.json` includes the full product-neighbourhood conclusion and absence of separation assumptions.

Step 3 uses the supremum's defining upper-bound property, not an extremum-attainment theorem. The difference is a continuous function on the given compact `X`, and its supremum norm is the one in the item's hypotheses. Linearity gives `L(f_p)-L(f_p0)=L(f_p-f_p0)` and the stated contractivity then gives the second bound. I checked the strictness needed for continuity: the bound is at most `epsilon/2`, which is strictly less than the requested positive `epsilon`. This step introduces no completeness or ultrametric hypothesis.

Step 4 uses only the assumed B-linearity, evaluated at the scalar `c(p)`. This proves linearity over the entire ring `C(P,B)`, not just over constant B-valued functions. Continuity of the scalar action is composition, multiplication in the normed field and the projection from the product. Addition, zero and module identities are pointwise. The finite-sum claim is explicitly induction with the zero base case, so the empty index set is included. These elementary identities do not warrant new lemma nodes.

Step 5 writes the precomposed section literally as `f_{u(p')}` and computes both sides at every `p'`; there is no unspecified transport or interchange of limits. Composition gives continuity. The same argument of steps 1–3 applies on `P'` because it is again a profinite parameter space.

I tested the small cases separately: when `P` is empty, the only functions have empty domain, all estimates quantified over its points are vacuous, and all module identities hold by extensionality. For empty `P'`, naturality is equality of empty-domain functions; a map from nonempty `P'` to empty `P` cannot occur. For `T` empty, both sides are zero. For singleton `X` the estimates reduce to contractivity on one scalar-valued section. The zero functional is allowed. The argument works for the ordinary real absolute value, nonarchimedean absolute values and a trivially normed field alike. Nonempty `X` is kept as stated, and no completeness is used.

Against delivery-errors B–E: no new unsplit node contains a proof, no unintroduced object or external tag defines the statement, no duplicate or restated clause was created, every non-elementary input is the statement of its cited node, and that node is already a Mathlib leaf in the item's unit. There is no new dependency path back to the item. All five steps are below 2000 characters. The complete analytical argument is in the item, rather than moved to a new node. The corrected choices during this review were to avoid the completeness-bearing function-space node and to use the existing tube lemma directly; no statement correction was necessary.
