# NK — lem-pod-canonical-coefficient-pullback-reduction

## Files written

- `dag/nodes/sec-poincare-duality/lem-pod-canonical-coefficient-pullback-reduction.json`: existing statement split into nine steps. No Mathlib match; five additional logged searches, including two semantic phrasings. Statement and ancestry retained.
- `citations.json`: verbatim statement excerpts for every step/node citation.
- No new nodes and no Mathlib leaves. `prepare_split.py` and `searches.jsonl` are sandbox working records.

## Attachments

None. Searched the read-only `WeilConjectures/` source for the exact blueprint id, coefficient/pullback comparisons, inverse-image comparisons and completion. The relevant results are underived or condensed-category operations, and the cohomological-finiteness declarations concern cohomology. None states the actual completed integral cone comparison together with both inverse identities and the specified finite projections.

## WANTED

None. All literature used is present.

## Findings and corrections

The imported statement is retained. Its canonical normalization is stronger than the *statement* of `lem-weil-isomorphism-derived-pullback`, which asserts existence of a natural isomorphism. I did not cite that existence assertion as a proof of the normalization. Instead, I reconstructed the specified multiplication/cone/completeness composite and computed its product coordinates. In particular, I did not infer equality of derived morphisms merely because all finite projections agree: Stacks Tag 08TC explicitly cautions that abstract derived limits are only noncanonically isomorphic.

The canonical strict completeness augmentation is supplied by the **statement** of `lem-weil-finite-free-completed-scalar-comparison`, specialized to L=E, rather than extracted from another node's proof. The inverse-image ring projection square is part of the hypotheses and is also specified in `def-weil-inverse-image-pullback-comparison`. During the source check I corrected the product lemma's tag to 07KC (`derived-lemma-products`); 08U1 is a different lemma.

The chapter and unit are unchanged. This is an auxiliary normalization for the last sentence of Step 7 of `prop-cohomological-finiteness`, as in its existing ancestry through `lem-pod-frobenius-fixes-unit-section`. Generic sheaf and derived-category tool statements from other units are declared individually in `split_report.tool_uses`; none replaces the unit's finiteness argument.

## Unfinished work

None in the one-level split. The cited pre-existing nodes retain their own states; I wrote no Lean and ran no compiler or build.

## Not duplicates

No new nodes. Searches over the entire DAG and blueprint found the existing inverse-image, strict Roos, completeness, reduction comparison and well-definedness nodes used here. The item is more specific than the general natural-isomorphism statement: it identifies actual cone maps and quotient projections. Elementary multiplication, cone-coordinate and cancellation computations remain proof steps.

## Review by NK

I read the current blueprint chapter and `sk-lem-finite` unit, the statement and proof of `prop-cohomological-finiteness` in the main-20261015 snapshot (especially Step 7's final sentence), Stacks `sites-modules.tex` Definition `definition-pushforward` (03D6), and `derived.tex` Definition `definition-derived-limit` (08TC) with `lemma-products` (07KC). I also read Bhatt–Scholze p. 24, Proposition 3.5.1 and Definition 3.5.2, for the intended canonical completeness map. No SGA source is used. There are no new-node sources to audit.

For Step 1 I read `lem-weil-proetale-isomorphism-inverse-image`: clauses 1–3 give site relabelling, exactness, product preservation and natural coefficient isomorphisms. Its constant-module wording is not silently extended: the step explains relabelling of the completed-ring action. The comparison definition explicitly supplies the exact descended completed-module functor. `lem-pc-kflat-resolution` supplies flat terms as required, and `def-pur-integral-derived-operations` states the actual quotient complexes used by the completed pullback.

Step 2 uses the **definition** of sheaf tensor product to write a balanced, restriction-compatible multiplication map and its inverse. I checked the module action against the coefficient-projection square, rather than treating the two coefficient rings as equal. Step 3 uses clause 3 of the inverse-image lemma for ring-reduction naturality. The equality with the inverse coefficient maps follows by multiplying its square by their inverses. Both coordinates of the cone, the minus sign in its differential, and every projection are written explicitly using the cone convention in `def-weil-abstract-derived-category`. Thus this is a direct elementary coordinate calculation, not an uncited cone-transport theorem.

Step 4 cites separate theorems for the non-elementary interpretation of those complexes: countable products are exact for the completed module sheaf by `lem-weil-proetale-countable-products-exact`; clause 2 of `lem-weil-derived-limit-existence` gives derived products. `lem-pur-integral-operations-well-defined` identifies the chosen completed-pullback representative, and `lem-weil-strict-roos-comparison` says the cone construction with its maps and projections descends. The small-site universe and exact-product hypotheses are those supplied by the pro-etale site convention and the cited countable-products theorem. I use no smallness assertion about a larger unspecified index category: all towers are indexed by the positive integers.

In Step 5, clause 2 of `lem-weil-constant-coefficient-objects-constructible` states derived completeness for this precise completed coefficient ring on any scheme. The finite-free scalar-comparison theorem states both the explicit zero-shifted-component augmentation and its invertibility on derived-complete objects. Its L=E specialization therefore applies with no extension-of-coefficients change. This is what makes the actual map eta invertible, rather than merely providing some isomorphism to the cone.

Step 6 uses the exact formula in part (b) of `def-weil-inverse-image-pullback-comparison`. Multiplication sends its tensor-unit component to the original quotient map and its zero coordinate to zero. I checked both composite identities by cancellation of L and F(eta), so they concern the specified kappa and lambda.

In Step 7 I checked K-flatness of the one-term unit directly from the definition and the multiplication tensor unitor. Thus the quasi-isomorphism q has K-flat source **and** target, allowing clause 1 of `lem-pur-derived-change-of-rings` to prove that its actual reduced chain maps are quasi-isomorphisms. The two clauses of `lem-weil-integral-reduction-tower-well-defined` explicitly identify both the maps from the original object and the transitions for these two resolutions. Clause 2 of the constant-coefficient theorem gives the specified canonical reduction to B_n. Naturality of the elementary multiplication from Step 2 supplies the finite pullback square; no theorem about an arbitrary coefficient morphism is inferred from a definition alone.

Step 8 uses the projection identity calculated in Step 3, e_n a=gamma_n from Step 5, and the quotient-arrow identity in Step 7. I wrote the compositions before and after cancelling eta. The coefficient-ring projection square then gives theta's identity. Before taking any limit, the multiplication squares commute with the actual adjacent reductions; the q-tensor comparison also consists of actual chain maps. This checks the tower compatibility requested by the statement, not just isolated finite-level identities. Step 9 reads `def-weil-constant-weil-structure` clauses 1–3 only to identify c_n, c_R and the definition theta=c_R lambda in the Frobenius specialization; the normalization of lambda is proved here using the convention expressly fixed by the item.

I checked the requested B–E failures point by point. There are no statement-only children, new duplicate nodes, relabelled conclusion clauses, invented Mathlib leaves or unlogged new search records. Each cited node was opened and its used assertion is quoted in `citations.json`; proof dependencies are exactly their union. All nine steps are below 2000 characters and the non-elementary existence, descent and completeness assertions cite separate existing statement nodes. The sources do not impose properness, connectedness, smoothness or finite type for the coefficient comparison, and none is used. The empty scheme, identity isomorphism, n=1 and adjacent n+1 to n reductions satisfy the same formulas. In particular the argument never infers a nonempty cohomological support and never divides by a nilpotent element of A_n. All coefficient maps remain semilinear until the specified scalar transport is applied.

Mathlib results were read: `SheafOfModules.pullbackObjFreeIso` and `pullbackObjUnitToUnit` in `Mathlib/Algebra/Category/ModuleCat/Sheaf/PullbackFree.lean` describe underived pullback, not this completed derived cone comparison. The other semantic hits are ordinary adic-completion evaluations or scheme fibre-product identities; they do not state the item. Existing inherited search entries are preserved, and the five new queries are the exact queries in the sandbox log.
