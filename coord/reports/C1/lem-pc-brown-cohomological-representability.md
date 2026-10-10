1. Files written:

- `lem-pc-brown-cohomological-representability.json`: item split into three proof steps.
- `lem-pc-compact-hom-hocolim.json`: new statement-only node for Stacks Tag 094A; Mathlib no match.
- `lem-pc-compact-generators-build-objects.json`: new statement-only node for Stacks Tag 09SN; Mathlib no match.
- `citations.json`: verbatim quotations for every cited node in the item proof.

2. Attachments: none. No declaration in `WeilConjectures/` states this generic Brown representability theorem.

3. WANTED: none. The Stacks source was read in the available checkout `/home/ubuntu/c1-stacks-review/derived.tex`; its corresponding path in the project's `literature/` is recorded on the nodes, although that generated tree is absent in this read-only clone.

4. The item was a statement-only dependency of `lem-pc-brown-representability-right-adjoint`. Stacks Tag 0A8F supplies its proof. The original statement says exactly the source's compact-generation, coproduct, cohomological-functor, and product hypotheses. I added its standalone prerequisites, Tags 094A and 09SN. The zero functor is represented by a zero object; a representable Hom functor returns its representing object, so these small cases are consistent with the construction.

5. Nothing unfinished in the one-level split. The new node remains statement-only for its next worker.

## Not duplicates

Neither Tag 094A nor Tag 09SN occurred in another node's source field. `lem-kun-complex-colimit-hocolim` concerns sequential colimits of complexes of etale sheaves and does not state that compact Hom commutes with a homotopy colimit in an arbitrary triangulated category. No existing node states the general compact-generator construction of Tag 09SN.

## Review by C1

I read Lemma `lemma-brown` (Tag 0A8F), Lemma `lemma-commutes-with-countable-sums` (Tag 094A), and Lemma `lemma-write-as-colimit` (Tag 09SN) in `derived.tex`, including their proofs. The item's statement matches 0A8F clause by clause: the source's direct sums are the stated set-indexed coproducts, and its contravariant cohomological functor transforms them into products. The first new node matches 094A: its countable coproduct and compactness hypotheses, telescope triangle, and Hom-colimit bijection are all present. The second matches 09SN: the source has compact generators and arbitrary coproducts and concludes precisely the sequential cone and homotopy-colimit construction stated. I checked for pre-existing nodes by both tags, by homotopy-colimit/compactness terms across the DAG, and with `blueprint_refs.py`; none states either general result. Mathlib searches using `msearch.py` returned no matching theorem; LeanSearch was unavailable and is recorded as such.

Step 1 uses the definition of triangulated category in `def-weil-triangulated-category` for shifts/coproducts and `def-sp-abelian` for the abelian target. The source explicitly indexes the coproduct by every generator and every element of its H-value, then obtains a natural transformation by Yoneda. Step 2 cites the same definitions for cone triangles and kernels; its stated map from the kernel coproduct and the cohomological lifting are exactly the middle paragraphs of 0A8F. Step 3 cites `lem-pc-compact-hom-hocolim`, whose statement gives precisely the Hom-colimit bijection it uses, and `lem-pc-compact-generators-build-objects`, whose statement gives the final expression of every object by generator coproducts, cones and a homotopy colimit. The two definition nodes supply the triangle and exact-sequence framework. I spelled out surjectivity, successive kernel killing, closure of the isomorphism locus under triangles, coproducts and their homotopy colimits, and its equality with C using Tag 09SN. The small cases were checked above. I corrected the initial telescope step after rereading the source: it now includes the lift of the compatible elements to H(X), and I added Tag 09SN after noticing the last inference needed its statement.

## Second reading by C1

- Item statement: checked Tag 0A8F, `lemma-brown`, hypothesis by hypothesis; verdict: correct after making compact generation and cohomological-functor meanings explicit.
- Step 1: checked Tag 0A8F construction of `X_1` and the Yoneda invocation; verdict: correct, with the missing citation repaired.
- Step 2: checked the kernel coproduct, cone triangle, and lift against Tag 0A8F and Hom-triangle exactness; verdict: correct, with the exactness citation repaired.
- Step 3: checked the telescope, compact-Hom colimit, kernel killing, five-lemma closure, and generator construction against Tag 0A8F; verdict: correct, with Hom exactness and five-lemma citations repaired.
- `lem-pc-compact-hom-hocolim`: checked Tag 094A; verdict: correct, now explicitly citing compactness.
- `lem-pc-compact-generators-build-objects`: checked Tag 09SN; verdict: correct, now explicitly citing compactness and generation.
- `def-pc-compact-object`: checked Tag 07LS; verdict: exact statement-only definition.
- `def-pc-generators`: checked Tag 09SJ; verdict: exact weak-generator formulation.
- `def-pc-compactly-generated`: checked Tag 09SQ; verdict: exact statement-only definition.

Changes: added three self-contained definition leaves; added Yoneda, Hom-triangle exactness, and five-lemma citations; updated statement dependencies and citation quotes. Existing Mathlib and blueprint searches were retained; no Mathlib declaration states these results.
