# Stage-1 report: lem-pur-integral-braiding-scalar-extension-square

## Files written

- `dag/nodes/sec-smooth-purity/lem-pur-integral-braiding-scalar-extension-square.json`: statement split with a three-step proof; no Mathlib match.
- `dag/nodes/sec-smooth-purity/lem-pur-integral-signed-scalar-tensor-square.json`: statement-only strict finite-stage lemma; no Mathlib match.
- `citations.json`: verbatim statement quotes for every cited node in every proof step.

## Attachments

None. I searched `lean/WeilConjectures/` for the item id and its braiding/scalar-extension notions; no finished project declaration states the item.

## WANTED

None. The proof follows the available Stacks and Bhatt--Scholze references plus the explicitly recorded normalized coefficient constructions.

## Not duplicates

- `lem-pur-integral-signed-scalar-tensor-square` vs `def-pur-finite-pullback-tensor-braiding`: the existing node defines a signed derived braiding for one coefficient ring; the new node proves its compatibility with a separate scalar-extension tensor map between two coefficient rings.
- `lem-pur-integral-signed-scalar-tensor-square` vs `lem-pur-quotient-scalar-tensor-composition`: the existing node compares successive scalar extensions and tensor associators; the new node compares scalar extension with the signed swap and includes the Koszul sign.
- `lem-pur-integral-braiding-scalar-extension-square` vs `lem-pur-rational-braiding-scalar-compatibility`: the item is the integral completed square before localization; the existing node is the rational localized naturality and scalar square and depends on this item.

## Review by ND

I read the live item and the related definitions `def-pod-integral-tensor-constraints`, `def-weil-derived-complete-integral-detailed`, `def-weil-integral-scalar-extension`, and `lem-pur-integral-operations-scalar-extension`. I also read the statements of `def-pur-ringed-site-signed-tensor-models`, `def-pur-completed-coefficient-tensor-transport-models`, `lem-pc-kflat-resolution`, and `lem-pod-integral-system-reduction-fully-faithful`. The new child node is strictly smaller: it is a chain-level equality for flat-term complexes and a balanced scalar map, checked on each homogeneous generator and quotient transition. In item step 1, the cited resolution and operation nodes provide the representatives and the prescribed scalar comparison, while the tensor-constraint definition says the integral braiding is the coherent-reduction-normalized signed braiding. Step 2 uses exactly the child statement; its generator calculation keeps the same bidegree sign and scalar balancing and therefore applies to every quotient transition. Step 3 uses the cited full-faithfulness statement to lift equality of compatible reductions, then uses the two normalization statements to identify the lifted maps with the displayed composites. I checked the edge cases `L=E`, ramified extensions, zero complexes, and bidegrees `(0,0)` and `(1,1)`; all reduce to the same balanced swap identity. I found no source or statement error and no finished Lean attachment.
- `lem-pur-integral-signed-scalar-tensor-square` vs `lem-integral-braiding-scalar-extension-square`: no such existing id; the current item is the target and its statement is at the completed derived-category level.
- `lem-pur-integral-signed-scalar-tensor-square` vs `def-a1-completed-pullback-universe-transport-data`: the existing definition specifies universe transport and quotient-unit normalization for pullback; the new node is a scalar-extension/tensor swap equality for arbitrary flat complexes.
- `lem-pur-integral-signed-scalar-tensor-square` vs `def-a1-constant-complex-base-change-data`: the existing definition packages finite pullback and Roos data; the new node proves a signed braiding square.
- `lem-pur-integral-signed-scalar-tensor-square` vs `def-a1-constant-complex-quotient-model`: the existing definition constructs quotient towers and reductions; the new node proves scalar compatibility of the Koszul swap.
- `lem-pur-integral-signed-scalar-tensor-square` vs `def-a1-finite-pullback-strict-tower-data`: the existing definition records pullback tower notation and normalizations; the new node concerns coefficient extension and tensor swap without a scheme morphism.
- `lem-pur-integral-signed-scalar-tensor-square` vs `def-a1-pulled-koszul-tower-normalization`: the existing definition normalizes pulled Koszul towers; the new node compares two coefficient rings and has no pullback map.
- `lem-pur-integral-signed-scalar-tensor-square` vs `lem-a1-balanced-finite-tower-generator-comparison`: the existing lemma compares pullback tower generators; the new node compares scalar extension with signed tensor exchange.
- `lem-pur-integral-signed-scalar-tensor-square` vs `lem-a1-balanced-finite-tower-quotient-comparison`: the existing lemma compares finite quotient pullback maps; the new node asserts a Koszul braiding square.
- `lem-pur-integral-signed-scalar-tensor-square` vs `lem-a1-balanced-finite-tower-scalar-comparison`: the existing lemma gives a scalar pullback comparison and its normalization; the new node adds the signed swap and compares both tensor orders.
- `lem-pur-integral-signed-scalar-tensor-square` vs `lem-a1-completed-scalar-exact-base-change`: the existing lemma proves exactness of a completed scalar pullback functor; the new node is a chain-level braiding compatibility and does not assert exactness.
- `lem-pur-integral-signed-scalar-tensor-square` vs `lem-a1-constant-complex-completed-pullback`: the existing lemma constructs completed pullback reduction data; the new node is independent of pullback and proves a signed scalar tensor identity.
- `lem-pur-integral-signed-scalar-tensor-square` vs `lem-a1-constant-complex-finite-pullback`: the existing lemma constructs finite pullback comparisons; the new node compares coefficient scalar extension and Koszul exchange.
- `lem-pur-integral-signed-scalar-tensor-square` vs `lem-pur-integral-braiding-scalar-extension-square`: the existing item asserts the completed derived-category square for all constructible objects; the new node asserts only the underlying flat-complex generator equality before completion and therefore is a proof dependency, not a restatement.
