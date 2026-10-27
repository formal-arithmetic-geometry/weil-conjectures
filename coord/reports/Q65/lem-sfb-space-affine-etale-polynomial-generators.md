# Stage-1 report: lem-sfb-space-affine-etale-polynomial-generators

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-space-affine-etale-polynomial-generators.json: statement split into seven proof steps; retains the complete original statement, provenance, prior Mathlib searches, and blueprint ancestry. Additional actual searches are recorded.
- citations.json: one verbatim statement quotation for each node cited in each step.
- report.md: this report.

New nodes: 0. New Mathlib leaves: 0. Every non-elementary input is already in the DAG. The finite second-factor extraction and polynomial lifting computations are written in the item rather than made into nodes.

## Attachments

None. Searched the project library WeilConjectures/ for the exact blueprint tag and for polynomial generators, affine etale charts and algebraic-space pushforward. No declaration proves this statement. The existing Sheaf algebraic-space pushforward theorem has `sorry` and is only a prerequisite, not an attachment.

## WANTED

None. All sources needed for the proof are present in literature/stacks-project/.

## Problems found and changes

The item was unsplit, with no previous sandbox proof or report. Its statement is correct as written, including its explicit absolute-base convention. The proof of Stacks 07V6 applies before its cohomology argument: neither H^1 vanishing nor finite type of X over V is used here. I have not imported the later global-section lifting step, which really does need H^1 vanishing.

The source has a harmless variable-count slip: it chooses g_1,...,g_m and then writes a polynomial ring with n variables. The split consistently uses m. No statement correction was necessary.

Whole-DAG and blueprint searches found existing nodes for the affine overlap, tensor-product spectrum, affine morphism of affine schemes, affine locality, quasi-coherent pushforward, etale finite presentation, small-etale pushforward restriction, cover permanence, affine-open basis, open immersions being etale, local surjectivity, and quasi-coherent kernels and sums. Searches with blueprint_refs.py for 'polynomial generators', 'etale finite presentation', '07V6', and 'separated affine chart' found no blueprint statement to attach to this item. The nearest blueprint ancestor command reports None, as already recorded in the item's existing ancestry; that ancestry and its detailed place are retained. Read the latest blueprint unit and its direct-image proof, including paragraph (3), alongside the stored chapter/unit records. This is a generic Stacks affineness input below that route, not a replacement of the unit route. All off-unit generic inputs are declared in split_report.tool_uses.

The actual msearch calls used two semantic phrasings, Loogle, LeanSearch and grep. They returned ring-level etale presentations, algebra finite-presentation results, and scheme separation results; none states this algebraic-space sheaf conclusion or gives it by a one-line specialization. The grep for AlgebraicSpace and the relevant polynomial/pushforward expression returned no hits. In particular Algebra.Etale.finitePresentation alone does not address the sheaf algebra or its kernel. The queries and their returned declaration lists are retained in searches.jsonl and mathlib_searches.

## Unfinished

None in this stage-1 split. No Lean was written or compiled. Existing cited unsplit nodes remain work items of their own.

## Not duplicates

No new nodes are created, so there are no new/existing same-tag pairs to distinguish. Existing more general inputs are cited directly rather than duplicated.

## Review by Q65

I read Stacks spaces-cohomology.tex, Tag 07V6, from the choice of U through restriction of the polynomial map to U. I also read spaces-properties.tex 03LX/03LV and 03M1; spaces-morphisms.tex 03M9 and 03WG; schemes.tex 01I4/01JQ; morphisms.tex 01QO, 01SH, 01S7 and 02GJ; algebra.tex 00U1; and sites.tex 00WM/00WN. The change-of-base statement 04SG was checked against the item's explicit convention. There are no new nodes whose sources need separate review.

For step 1 I opened the statements of lem-trf-space-separated-affine-chart-overlap, lem-weil-pbc-fibre-product-affine-spectra and def-weil-closed-immersion. The first really supplies the affine scheme overlap and its closed immersion without assuming X quasi-compact; the second supplies the tensor product AND its two projection maps; the third includes the affine quotient characterization. Thus the surjection is from B tensor_A B, not from a fibre ring over a point. All maps are over Spec Z, where the given f has the required closed diagonal.

For step 2 I opened lem-weil-pbc-morphism-affine-schemes-affine, lem-sfb-space-affine-locality, def-trf-space-quasi-coherent-module and lem-trf-space-qc-separated-quasi-coherent-pushforward. The first applies to R and U, which step 1 made affine. The second applies to phi using the same surjective etale U-chart on its target and gives quasi-compactness and separatedness. These are exactly the hypotheses of the pushforward node; O_U has its free one-generator presentation. This avoids applying the pushforward theorem to phi merely because phi is etale, which would not suffice for its quasi-compactness hypothesis.

For step 3 I opened lem-weil-pbc-etale-algebra-finite-presentation-localization and used its first clause, for the affine scheme projection p_0: R -> U. The etaleness is given by step 1. The statement gives finite presentation and explicitly finite algebra generation, with no Noetherian assumption. Step 4 is an elementary finite calculation: lift finitely many generators through the quotient, express the lifts as finite tensor sums, and collect their second factors. It is not a new lemma. The first and second B-actions are kept distinct throughout.

For step 5 I opened def-trf-space-etale-module-functors and lem-trf-space-etale-module-pushforward-restriction, and reread the affine-spectrum product node. The definition supplies compatible chart cones; I spelled out how a function on the source defines a global section and how the identity chart recovers it. The restriction node really states equality on compatible sections and their naturality, not only a bare module isomorphism. Hence g_i restricts as s(g_i), with coefficients acting through t. For an affine etale test with ring D its target sections are C tensor_{B,t} D. Finite sums of pure tensors and the generating polynomials explicitly give lifts. No assertion that arbitrary sections of a tensor sheaf are globally pure tensors, or that taking sections of an arbitrary sheaf epimorphism is surjective, occurs.

For step 6 I opened lem-trf-space-fibre-products-etale-covers, lem-trf-space-chartwise-etale-permanence, lem-weil-pbc-affine-opens-basis, lem-weil-pbc-open-immersion-etale and lem-weil-pbc-site-sheaf-sets-epi-locally-surjective. They respectively supply the covering scheme after base change, etale composition and covering composition, affine opens covering that scheme, etaleness of their inclusions, and the local-lifting criterion. All these sites are the same small-etale sites. I added the last two geometric citations during review rather than leaving their facts tacit. The final algebra epimorphism assertion is checked from local lifts and the sheaf condition.

For step 7 I opened def-trf-space-quasi-coherent-module and lem-sfb-space-qcoh-kernels-colimits. The latter explicitly states both arbitrary small direct sums and kernels in ALL module sheaves. The monomial set for finitely many variables is small. Thus the polynomial module and its target are quasi-coherent before applying the kernel assertion. No hypothesis of coherence, Noetherianness, finite presentation of the kernel, or vanishing of cohomology enters.

I checked the statement on the empty chart/empty space, on the identity chart of an affine space, and on a disjoint finite union of affine charts. The zero ring and m=0 are allowed. If C is generated by coefficients, the empty list of second factors is valid. Nothing assumes B is finite type over A: finite generation is only C over the projection copy of B. The section on an arbitrary test is lifted after the stated etale/affine covering, which is the exact surjectivity conclusion required.

I checked delivery-errors B through E against the actual node and cited statements. There is no new unsplit node hiding a proof, no claim restated as a new node, no cyclic return to the Serre criterion, and no source-only citation in place of a non-elementary node. citations.json uses actual verbatim statement text. Every proof step is below 2000 characters, and the finite extraction and base-change calculation remain explicit elementary arguments rather than hidden comparison lemmas. The only definition citations provide their stated data or local presentations. This review is my signature under the split.
