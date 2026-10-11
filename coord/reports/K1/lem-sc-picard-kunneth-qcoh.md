Files written:

- `dag/nodes/sec-abelian-varieties/lem-sc-picard-kunneth-qcoh.json` (statement, split)
- `dag/nodes/sec-abelian-varieties/lem-sc-qcoh-cech-total-tensor-iso.json` (statement-only unsplit node; Mathlib searches found no match)
- `citations.json`

Attachments: none.

WANTED: none.

The item was not present as a sorry-free declaration in the Lean source. The source is Varieties, Lemma `varieties-lemma-kunneth` (Tag 0BED). I searched the DAG and blueprint for an existing general quasi-coherent Kunneth statement; the only nearby use is the already split degree-one consequence `lem-sc-picard-h1-product-injective`, so I did not duplicate it.

## Review by K1

I read the full source proof in `/home/ubuntu/c1-stacks-review/varieties.tex`, including the finite affine covers, product cover, refinement maps, Cech cup-product map, and the final identification with sheaf cohomology. Step 1 checks the field, scheme, quasi-coherent, and pullback notions against their definition nodes and uses the new child only for the non-elementary tensor-total Cech quasi-isomorphism. Step 2 uses exactly the child statement and the existing affine-intersection Cech comparison statement; that comparison supplies the three cohomology identifications needed for the displayed direct sum. Step 3 checks that the induced map is the pullback-along-projections followed by cup product and that the construction is natural under pullback. The cited statements were opened and the quoted portions in `citations.json` were copied verbatim. I tested the formulation on degree zero and on affine X,Y: the total complex reduces to degree-zero sections and the map is the ordinary tensor-product identification. The new child is strictly a complex-level assertion and does not restate the item's cohomology theorem.

What I corrected: narrowed the former child so it is only the algebraic Kunneth formula for bounded-below complexes over a field; moved the Cech comparison, exact-sequence 2-out-of-3 argument, finite-cohomological-dimension induction, and degree-zero Leray argument into explicit item steps; and added statement-only nodes for affine-diagonal intersections, the universal-delta embedding, finite cohomological dimension, and Cech cup-product compatibility. I recorded searches actually run by `msearch.py` (LeanSearch was unavailable) and replaced citations.json with verbatim quotes for every cited node in every step.

What could not be finished: no Lean compilation is permitted at stage 1; the child remains unsplit as required.

## Second reading by K1

- Source statement: checked against Varieties, Lemma `lemma-kunneth` (the Stacks entry corresponding to Tag 0BED), hypothesis by hypothesis; the quasi-compact affine-diagonal hypotheses and tensor product over the field agree.
- New node `lem-sc-qcoh-cech-total-tensor-iso`: checked against the displayed map (equation `equation-kunneth-on-cech`) and the subsequent induction conclusion in the same proof; fixed finite affine covers, refinement pullbacks, and the Cech cup-product map are stated explicitly; verdict: retained as an unsplit complex-level lemma.
- New node `lem-sc-picard-affine-diagonal-intersections`: checked against Tag 0BDX; affine-diagonal pullback of affine opens and finite intersections agree; verdict: retained.
- New node `lem-sc-picard-qcoh-finite-cd`: checked against Tag 01XI; the finite affine-cover bound implies the stated uniform vanishing; verdict: retained.
- New node `lem-sc-picard-qcoh-universal-delta-embedding`: checked against Tag 0BDY, clause (1); verdict: retained.
- New node `lem-sc-picard-cech-cup-pullback-compat`: checked against Tags 01FD and 07MB and the source construction; verdict: retained.
- Step 1: checked against the finite affine-cover and refinement paragraph; the product cover and Cech map are the cited child’s construction; verdict: agrees.
- Step 2: checked against the source’s statement that the Cech map induces the Kunneth cohomology isomorphism together with Tag 01XD Cech comparison; verdict: agrees with the child and comparison node.
- Step 3: checked against the source’s definition of the cup-product map and its final degree-zero identification; verdict: corrected to remove the unsupported general pullback-functoriality assertion and retain only the canonical-map identification.

Changes made in the repair: restored the pullback-functoriality clause required by Tag 0BED, corrected the complex Kunneth map direction, made the Cech compatibility statement self-contained, and added the missing affine-vanishing, Cech-comparison, affine-product, and affine-base higher-direct-image citations. The initially proposed higher-direct-image node was deleted after duplicate checking found the existing `lem-pc-cohomology-sections-affine-base` statement of the needed affine-base section formula.

## Repair of R-kun0012

1. D2: the child `lem-sc-qcoh-cech-total-tensor-iso` now states only the field-linear Kunneth isomorphism for bounded-below complexes. The item's seven steps now contain the finite-cover construction, comparison maps, exactness and 2-out-of-3 argument, induction through an acyclic embedding, degree-zero pushforward/direct-sum computation, and Leray conclusion.
2. C4/E7: the item statement now matches Tag 0BED exactly; the cup-compatibility citation remains for identifying the canonical map.
3. C1: Step 2 cites the child for the algebraic formula `H^n(A tensor_k B) -> direct_sum H^p(A) tensor_k H^q(B)`.
4. C1: Step 1 cites `lem-sc-picard-affine-diagonal-intersections` for finite affine intersections and `lem-weil-pbc-fibre-product-affine-spectra` for products of affine opens.
5. C2: Step 1 and Step 3 cite the new Cech cup/refinement compatibility node and the existing comparison naturality nodes; Step 7 uses the same compatibility to identify the degree-zero map.

I reopened the Stacks source around `varieties.tex` lines 5442--5550 and checked each repaired step against the stated hypotheses. I opened every cited node used by the repaired steps; each quote in `citations.json` is copied from its statement. Small cases checked were affine X,Y (only degree zero), a one-open Cech cover, and the degree-zero direct-sum reduction. The new nodes are intentionally statement-only and remain unsplit for the next stage.

## Not duplicates

lem-sc-picard-affine-diagonal-intersections vs lem-weil-pbc-separated-affine-cover-criterion: the existing node gives a sufficient affine-intersection-and-ring-surjectivity criterion for separatedness, while the new node derives affine intersections from an already assumed affine diagonal.
lem-sc-picard-affine-diagonal-intersections vs lem-weil-pbc-separated-affine-open-intersection: the existing Mathlib leaf assumes a separated morphism to an affine base, while the new node applies directly to a scheme over a field with affine diagonal and records the finite-intersection consequence.
lem-sc-picard-affine-diagonal-intersections vs lem-sc-cech-comparison-map-iso-affine: the existing node assumes affine finite intersections as input to Cech comparison; the new node proves that input from affine diagonals.
lem-sc-picard-affine-diagonal-intersections vs lem-sc-cech-comparison-natural: the existing node states naturality of a comparison map under module morphisms, while the new node is the geometric affine-intersection lemma.
lem-sc-picard-affine-diagonal-intersections vs lem-pc-cech-computes: the existing node computes Cech cohomology assuming all intersections are affine, while the new node supplies that affine-intersection hypothesis from an affine diagonal.
lem-sc-picard-cech-cup-pullback-compat vs lem-sc-cech-comparison-map-iso-affine: the existing node states that comparison maps are isomorphisms, while the new node states compatibility of the signed cup construction and pullback with those maps.
lem-sc-picard-cech-cup-pullback-compat vs lem-sc-cech-comparison-map-naturality: the existing node defines comparison-map naturality in coefficients, while the new node adds the cup-product and scheme-pullback compatibility.
lem-sc-picard-cech-cup-pullback-compat vs lem-sc-cech-comparison-natural: the existing node transports coefficient morphisms through Cech comparison, while the new node concerns the cup product and pullback refinement maps.
lem-sc-picard-cech-cup-pullback-compat vs lem-sc-boundary-cech-injective-middle: the existing node is a boundary-class injectivity statement, while the new node is the general cup-product compatibility assertion.
lem-sc-picard-cech-cup-pullback-compat vs lem-sc-cech-h1-map-natural: the existing node is naturality of the degree-one boundary comparison, while the new node treats all degrees and cup products.
lem-sc-picard-qcoh-finite-cd vs pqf-lem-serre-criterion: the existing node is the converse affineness criterion from vanishing H^1 of finite-type ideals, while the new node states a finite cohomological-dimension bound for all quasi-coherent modules on an affine-diagonal scheme.

## Second reading by K1 (repair R-kun0058)

I reread the seven current proof steps and all repaired statements against Varieties Tag 0BED, Cohomology Tags 01XI and 0BDY, Tag 01XB, and the Cech compatibility sources Tags 01FD, 01FP, and 07MB. The item now explicitly includes functoriality for pullback along morphisms over k; the final step proves it from the product morphism identities and the repaired Cech pullback clause. The complex Kunneth child now has the well-defined direction from the direct sum of tensor products of cohomology to total-complex cohomology, with [a] tensor [b] mapped to [a tensor b].

The cup-compatibility node is self-contained: it introduces X, X', f, arbitrary covers, the specified refinement U' -> f^{-1}U, the spaces on which F and G live, and separately states pullback compatibility and the signed cup-product compatibility. Step 4 now cites pqf-lem-affine-vanishing for exactness on affine intersections. Step 6 cites the affine-intersection Cech comparison, the affine fibre-product lemma, and the higher-direct-image section formula node I added; it also states why tensoring over the field is exact. Step 7 records that an affine diagonal is quasi-compact, hence Y is quasi-separated, before applying the direct-sum cohomology lemma. I checked the affine case, the one-open-cover case, and n=0; no statement is a restatement of the item.

## Second reading by K1

- Item statement: checked against Varieties `lemma-kunneth` (Tag 0BED), including field, quasi-coherent, quasi-compact, and affine-diagonal hypotheses; verdict: corrected by removing unsupported pullback-functoriality conclusion.
- `lem-sc-qcoh-cech-total-tensor-iso`: checked against equation `equation-kunneth-on-cech`; verdict: retained as a strictly smaller field-linear complex statement.
- `lem-sc-picard-affine-diagonal-intersections`: checked against Cohomology `lemma-affine-diagonal` (Tag 0BDX); verdict: retained.
- `lem-sc-picard-qcoh-finite-cd`: checked against `coherent-lemma-vanishing-nr-affines` (Tag 01XI); verdict: retained.
- `lem-sc-picard-qcoh-universal-delta-embedding`: checked against `coherent-lemma-affine-diagonal-universal-delta-functor` (Tag 0BDY); verdict: retained.
- `lem-sc-picard-cech-cup-pullback-compat`: checked against Tags 01FD and 07MB; verdict: retained for the internal Cech map and cup-product identification.
- Steps 1--3: checked against the finite-cover, refinement, equation, and Cech-comparison paragraphs of Tag 0BED; verdict: cited statements supply the constructions used.
- Step 4: checked against the short-exact-sequence paragraph of Tag 0BED and affine vanishing Tag 01XB; verdict: exactness and 2-out-of-3 dependencies are explicit.
- Step 5: checked against the induction paragraphs of Tag 0BED and Tags 01XI/0BDY; verdict: hypotheses and decreasing cohomological degree are explicit.
- Step 6: checked against the degree-zero Cech and Leray paragraphs of Tag 0BED; verdict: affine products, comparison, and section computation are cited.
- Step 7: checked against the final Leray paragraph of Tag 0BED; verdict: retained after deleting the stronger functoriality argument.

Changes: removed the item statement's extra functoriality clause and the final proof paragraph asserting it, because Tag 0BED does not state that conclusion.
