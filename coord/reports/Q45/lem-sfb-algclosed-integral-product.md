# Q45 stage-1 delivery: lem-sfb-algclosed-integral-product

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-algclosed-integral-product.json`: existing statement, now split in four steps. Its statement and statement dependencies are unchanged. No exact Mathlib match: the pullback-integrality instances require geometric integrality, and the search hits do not supply that missing hypothesis from algebraic closedness and integrality.
- `citations.json`: a verbatim statement quotation for every node cited by every proof step.
- `report.md`: this report. `searches.jsonl` is the search command's unmodified log.

There are **0 new nodes and 0 new Mathlib leaves**. Every ingredient was already in the DAG. The retained older searches belong to the imported item record; the new Q45 searches were actually run with msearch.py and their hits read. Both the direct scheme-product question and a second question about geometric integrality were searched, as was the affine tensor-domain formulation. Loogle and the grep of AlgebraicGeometry/Geometrically/Integral.lean confirm that the promising product instance has an additional GeometricallyIntegral hypothesis. LeanSearch instead found linear-disjointness results with additional hypotheses, not the requested result. Project source searches by blueprint tag and integral-product/algebraically-closed terminology found no completed whole-item declaration. The source file WeilConjectures/Mathlib/AlgebraicGeometry/Geometrically/Integral.lean only supplies composition results assuming geometrically integral fibres, so it is not an attachment.

## Attachments

None.

## WANTED

None. The proof uses the local Stacks source, not SGA.

## Problems found and repaired

The imported item had no proof. Stacks 05P3 says to reduce to integral affine product charts and cites the reducedness and irreducibility cover criteria. The irreducibility criterion explicitly requires the product charts to intersect pairwise; I supplied that argument rather than assuming that two nonempty scheme factors have a Cartesian product of their spaces. Surjectivity of a morphism to Spec k is immediate for a nonempty source, and its base change is surjective by the existing 01S1 node.

I did not create an affine tensor-domain node: `lem-weil-pbc-algclosed-finite-type-tensor-domain` already says the needed statement, more generally allowing the first algebra to be arbitrary. Likewise `lem-per-integral-affine-cover-criterion` already gives exactly the assembly criterion. Both are declared generic tool uses in split_report because they belong to other units; neither replaces this item's affine-cover route.

The blueprint ancestor command returns None. I preserved the live item's existing null ancestor and full via list, and its already specified place in the Milne Proposition 4.1 boundary argument. I read the current `literature/blueprint/latest/` sk-thm-sf-ctf-stability statement and proof (snapshot ef6f9619fdbffa59e88528fb56483d76c70258c8). This item is an auxiliary scheme-theoretic fact deep in its inherited chain, not a claim to realize a separate unit step. Whole-blueprint searches for product of varieties, integral schemes, affine open covering, and Nullstellensatz found no node stating the whole integral-product result. No unit or chapter file was changed.

## Not duplicates

No new nodes were created. In particular the affine algebra and affine-cover results were cited under their existing ids instead of duplicated.

## Review by Q45

I read Stacks `varieties.tex`, Tag 05P3, label lemma-product-varieties, including the affine tensor-product proof, and its preceding counterexample over Q. I also read `properties.tex` Tags 01OL, 01OM and 01ON (lemma-characterize-reduced, lemma-characterize-irreducible, lemma-characterize-integral), the affine fibre-product formula in `schemes.tex` Tag 01I4 (lemma-fibre-product-affine-schemes), open-immersion base change in Tag 01JY (lemma-base-change-immersion), and `morphisms.tex` Tag 01S1 (lemma-base-change-surjective). For the existing algebraic tool I opened the full node and read its cited algebra.tex Tag 00I7, label lemma-separably-closed-irreducible, whose closed-fibre argument is another source of this affine-domain input. No new node needs a separate source review.

For step 1 I opened def-weil-finite-type-morphism and def-pc-integral-scheme. The former explicitly permits a finite affine cover with finitely generated coordinate algebras, and the latter explicitly says that each nonempty affine open has a domain coordinate ring. Deleting empty members and observing that both index sets remain nonempty are elementary. This uses finite type, not merely an unjustified finiteness assertion about arbitrary affine opens.

For step 2 I opened def-pc-fibre-product, def-weil-open-immersion, lem-weil-pbc-open-immersion-base-change, lem-weil-pbc-fibre-product-affine-spectra and lem-weil-pbc-algclosed-finite-type-tensor-domain. Their statements supply respectively the universal property, the identification with an open subscheme, stability of openness under the required base changes, the affine tensor-ring formula with its structure maps, and the domain conclusion. I wrote out the factorization condition showing that the product chart is exactly the intersection of two inverse images. These opens cover because both factor families cover. The tensor-domain hypotheses hold: k is algebraically closed and each S_j is a finite-type domain; each R_i is a domain. No geometric integrality, smoothness, or normality is presumed.

For step 3 I opened def-pc-integral-scheme, def-weil-irreducible-components, def-weil-affine-spectrum, lem-weil-pbc-surjective-base-change and def-pc-fibre-product. The first two justify nonempty intersections in each factor, with the closed-complement argument explicitly written. The spectrum definition states that Spec k has one point. Thus U to Spec k is surjective for nonempty U. The 01S1 node explicitly supplies surjectivity of the projection after base change along V to Spec k, with no finite-type, affine, or separatedness assumption. Its target V is nonempty. The universal property and the preceding inverse-image description identify this nonempty fibre product with the chart intersection. In particular I never use the false identification of underlying fibre-product spaces with set-theoretic products.

For step 4 I opened lem-per-integral-affine-cover-criterion. Its statement asks for a nonempty indexing set, affine chart rings that are domains, and pairwise nonempty overlaps, precisely the data supplied in steps 1 to 3. It concludes integrality of P. I checked its proof dependency closure and that of the tensor-domain tool: neither reaches this item (14 nodes inspected in their combined dependency closure), so these citations introduce no cycle. Each step's uses list has a corresponding verbatim quotation in citations.json, and proof_deps is their exact union.

For small cases I checked A=B=Spec k, one point factor with an arbitrary allowed variety, and products of affine lines. The argument allows singular integral varieties, for instance the cusp Spec k[t^2,t^3], and never invokes regularity or smoothness. Empty schemes are excluded by the actual hypotheses; explicitly discarding empty affine charts does not discard every chart. Algebraic closedness is essential: the source's Q(i) tensor_Q Q(i) splits and gives a reducible product if it is removed. Disconnected/reducible factors are excluded by integrality; domain rings, rather than merely reduced rings, are what the algebra input needs. All four steps are shorter than 2000 characters, with total assembly text 2224 characters. I checked delivery-errors B to E against the node and the opened sources: no new hollow, duplicate, or clause-restatement node, no citation of a proof in place of its statement, no unstated non-elementary fact, no omitted cover-overlap condition, and no statement correction was necessary.

## Unfinished work

No mathematical work remains for this stage-1 item. The two generic tool nodes are existing DAG work, not newly deferred clauses of this statement. Required dry run and delivery results are recorded by the delivery command.
