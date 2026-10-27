# Stage-1 worker report

Group Q97; item lem-trf-lci-residue-chart-cover-extension; 2026-10-23.

## Files written

- dag/nodes/sec-trace-formula/lem-trf-lci-residue-chart-cover-extension.json: existing statement node, now split into five steps. Mathlib verdict: no exact match; the complete-intersection assertion is not in Mathlib. No new nodes and no new Mathlib leaves.
- citations.json: seven entries, one for every step/node citation, copied verbatim from the cited statements.
- report.md: this report. searches.jsonl is maintained by the required msearch.py commands.

## Attachments

None. Searched lean/WeilConjectures/ for the exact blueprint tag and for residue-chart, chart-cover and complete-intersection terms. The project contains complete-intersection definitions and specialized results, but no declaration gives every clause of this item's chart-cover statement. Nothing was compiled or written to Lean.

## WANTED

None. All sources used are present in literature/stacks-project/.

## Findings and changes

The imported item was a statement-only auxiliary node extracted from lem-trf-syntomic-geometric-fibres-affine-criterion. Its statement is correct as written and is retained without weakening. Its proof can be assembled using existing nodes: open subschemes of a fibre product, affine-spectrum fibre products, and local-complete-intersection field extension. No new helper is warranted. The pointwise covering and explicit tensor comparison are elementary steps, rather than new nodes repeating clauses of the item.

I read the chapter, unit record and newest blueprint files for sk-i-curve-zero and lem-trf-local-term-locality. The newest blueprint takes the contracting-correspondence route, so the item remains accurately described as historical local-equation auxiliary material rather than a new replacement for that route. No unit or chapter is changed. The generic algebra theorem lem-weil-pbc-lci-field-change is declared as a tool use in split_report; it supplies field extension stability and does not replace any unit step.

The initial source list also mentions 01UG; the actual proof needs only the affine-chart facts 01JR/01I4/01JQ, field extension 00SJ, and the definitions of complete intersection and local finite type. The proof therefore does not cite 01UG for a result that its statement would not supply. The statement dependencies, old citations and Mathlib searches have been retained; the actual additional searches are appended with their logged results.

## Not duplicates

No new nodes. The potentially duplicated facts were found and reused as lem-weil-pbc-open-fibre-product, lem-weil-pbc-fibre-product-affine-spectra and lem-weil-pbc-lci-field-change. I also read lem-weil-pbc-open-preimage-fibre-product (only the one-open case), lem-sbc-affine-fibre-sections-tensor (only residue fibres), lem-pc-affine-pullback-chart-tensor-sections (module sections), lem-trf-lci-affine-open-locality (locality on an existing scheme), and lem-weil-pbc-lft-affine-pairs (the all-affine-pairs criterion); none is needed as a new helper. Whole-DAG tag/keyword searches and blueprint_refs searches for complete intersection, residue-fibre complete-intersection and fibre product affine found no blueprint node stating the full item.

## Review by Q97

I checked delivery-errors B--E against the actual statements and the local Stacks source. For the item I read schemes.tex lemma-open-fibre-product (01JR), lemma-fibre-product-affine-schemes (01I4), and the following lemma-fibre-product-affines (01JQ); algebra.tex lemma-lci-field-change (00SJ), including both directions and its hypotheses; morphisms.tex definition-finite-type (01T1), lemma-locally-finite-type-characterize (01T2), and lemma-local-complete-intersection (01UG). The precise meanings, including the zero-ring convention, are in the cited existing complete-intersection and finite-type definition nodes. There are no new nodes requiring further sources.

Step 1 uses def-pc-fibre-product only for the projection equation. For every point z, f(pi(z)) lies in V because t factors through V, hence pi(z) lies in one of the assumed U_b. This proves the covering without assuming surjectivity of pi, a nonempty fibre or any finiteness property of f. Openness is simply inverse-image openness for a scheme morphism. The statement of the definition explicitly gives the equation used.

Step 2 uses the full statement of lem-weil-pbc-open-fibre-product, which identifies the image of the open product with the intersection of the two inverse images and gives compatibility with projections. With the second open equal to all of Spec K, that intersection is exactly W_b. The hypotheses that U_b maps into V and that t factors through V are explicit in the item. The statement of lem-weil-pbc-fibre-product-affine-spectra gives not just affineness but the tensor-product spectrum and both specified projection ring maps. Thus this citation supplies every map asserted here, and no part is taken from its proof.

Step 3 is a direct balanced-tensor calculation, with no non-elementary theorem being invoked. I checked A-balancing for both formulas, k-balancing for the iterated tensor, K-linearity, multiplication, the unit and both inverse composites on generators. Both A-actions on K are the specified composite A to k to K. This argument applies equally when B tensor_A k is zero, when K/k is transcendental, and for arbitrary characteristics.

Step 4 uses precisely the ascent direction and the finite-type clause of lem-weil-pbc-lci-field-change, whose statement I opened. Its hypotheses are exactly the fields k and K, the extension k to K, and finite type of S_b, all given. It requires no flatness of B_b over A and no condition on any other residue prime. I read def-weil-pbc-complete-intersection-over-field to check invariance under the actual K-algebra isomorphism: images of generators and localized polynomial presentations preserve the complete-intersection cover, and inverse image of prime ideals preserves strict chains and hence dimension. This is an elementary use of the defining presentations, not a new descent theorem.

Step 5 uses def-weil-finite-type-morphism for the cover criterion and def-weil-pbc-complete-intersection-over-field for the zero ring. Spec K has only two opens, itself and the empty open, so the displayed cover verifies the stated definition on every affine target open. An empty index set forces X_K empty by step 1. If a chart fibre is empty, its tensor ring and all its further extensions are zero; the stated formulas and zero-ring convention still apply. No quasi-compactness or global finite-type conclusion is asserted for an infinite chart family.

For B1--B10 I checked self-contained hypotheses and definition citations, source tags with their .tex labels, single TeX escaping and blueprint ancestry. No unsplit helper contains proof material, because none is created. For C1--C8 every non-elementary input is one of the existing cited nodes, their statements give the claimed result, and citations.json contains the literal statements. The only off-unit non-Mathlib theorem is explicitly declared as a generic tool. For D1--D5 the five steps carry the assembly and the explicit algebra calculation; no clause has been relabelled as a new node. For E1--E7 I checked empty schemes, zero algebras, infinite chart families, nonflat/non-finitely-presented f and arbitrary field extensions. There is no source or statement dispute. Every step is shorter than 2000 characters.

I ran LeanFinder with two distinct phrasings, Loogle, LeanSearch and the required Mathlib grep through msearch.py. I read the actual hits: the only grep occurrence is a comment about presentation dimension at Extension/Presentation/Basic.lean:103, and Algebra.FiniteType.baseChange at FiniteStability.lean:42 supplies only finite type. The remaining hits concern smooth or standard-smooth algebras, residue fields and fibre maps, not local complete intersections. Recorded searches reproduce the tool/query text and the JSON records actually written by msearch.py; no unavailable service was represented as an empty successful search.

## Unfinished work

None in the stage-1 split. Existing dependency nodes remain the maintainer's independent items. Dry-run and delivery results are recorded below once available.
