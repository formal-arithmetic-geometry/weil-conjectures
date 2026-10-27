## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-space-universal-fibre-transcendence-bound.json: statement, split; no Mathlib match for the full algebraic-space uniformity assertion.
- citations.json: verbatim statement quotations for every proof-step citation.
- report.md: worker report and review.

No new DAG nodes; zero new Mathlib leaves.

## Attachments

None. Searched lean/WeilConjectures for the exact blueprint tag, transcendence, uniform bounds, and bounded fibre dimensions. The project has related scheme and algebra declarations, including ArtinVanishing/Algebra.lean and ClosurePointDimension.lean; none states this item for algebraic spaces, all scheme base changes and arbitrary etale charts. The available algebra generator bound is already attached as the existing Mathlib leaf lem-sfb-algebraic-adjoin-transcendence-bound.

## WANTED

None.

## Findings and changes

The item had a complete statement but no proof. Its source, Stacks spaces-flat.tex Tag 0CX1 (theorem-flat-dimension-n-representable), only asserts bounded fibre dimensions in the paragraph beginning “In particular the situation is local”. The split expands that omitted argument rather than treating the paragraph as a theorem proving all chartwise clauses. The atlas generator count is fixed before any base change; arbitrary base rings do not require a new finite-type hypothesis. The quasi-compact diagonal assumption is retained, though the proof does not require it. The contextual module hypotheses and definitions in the statement are retained verbatim; no statement dispute or weakening.

Existing DAG searches found lem-sfb-qc-space-affine-etale-atlas and lem-trf-space-qc-finite-affine-atlas-refinement for the atlas, lem-sfb-algebraic-adjoin-transcendence-bound for the algebraic bound, lem-weil-pbc-lft-affine-pairs for affine finite type, lem-weil-pbc-etale-algebra-residue-field-separable for residue extensions, and lem-kun-transcendence-degree-tower for comparison. No new node was necessary. The two existing atlas formulations are not edited or duplicated. Blueprint searches for transcendence, uniform bound residue transcendence, finite type algebra residue field transcendence, arbitrary base change chart, and affine etale found no statement equal to the item. The current blueprint read was literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability.proof.md. The inherited ancestor is null, as tools/blueprint_refs.py ancestor reports; its precise inherited place and via chain are preserved.

The report declares generic off-unit tools in split_report.tool_uses: the affine atlas theorem, etale-cover fibre-product calculus, etale residue extensions and the field tower formula. They implement the bounded-dimension prerequisite under the unit's compactification/direct-image route; they replace no unit step.

Mathlib searches were run through the required msearch.py, and searches.jsonl is retained. The semantic queries returned trdeg_lt_aleph0, trdeg_le_cardinalMk, finite scheme fibres and affine-space instances. These do not give the full item. The pre-existing records were retained, and actual current searches were appended. The bound trdeg_le_cardinalMk was read at Mathlib/RingTheory/AlgebraicIndependent/TranscendenceBasis.lean:469 and reused through its existing DAG leaf, not made a new node. The zero-hit Loogle query is retained exactly as run. Two semantic phrasings were checked.

## Unfinished work

None in this stage-1 split. No Lean files were written and no compiler, Lake or build command was run. The reused DAG prerequisites retain their existing states.

## Not duplicates

No new nodes.

## Review by Q51

I read Stacks spaces-flat.tex at Tags 0CX1 and 0CWS. The former needs a uniform upper dimension bound to start descending induction, and the latter explains why etale charts express the relevant transcendence degrees. I checked the complete chapter and unit records and the latest blueprint proof: the split stays within the inherited bounded-dimension prerequisite of direct-image preservation.

For step 1 I read spaces-properties.tex Tag 03H6 (lemma-quasi-compact-affine-cover), and morphisms.tex Tag 01T2 (lemma-locally-finite-type-characterize). I opened def-sfb-space-morphism-properties: its quasi-compactness on the affine identity test gives quasi-compact X, and its local-finite-type chart test applies to W -> X and the identity of Y. I opened lem-sfb-qc-space-affine-etale-atlas: its hypothesis is precisely quasi-compact point space, and its conclusion is an affine representable surjective etale atlas. I opened lem-weil-pbc-lft-affine-pairs: unlike the existing affine-over-a-field lemma, it permits arbitrary affine base rings, so it gives finite algebra generators over R here. I used this more general existing node to avoid accidentally assuming the base is a field. There is no need for the atlas map itself to be quasi-compact.

For step 2 I read schemes.tex Tag 01I4 (lemma-fibre-product-affine-schemes) and its tensor-product formula, fields.tex Tag 030F (lemma-transcendence-degree) and its generating-set argument, and the recorded Mathlib generalization at line 469. I opened lem-weil-pbc-fibre-product-affine-spectra, def-weil-pbc-localization-at-prime and lem-sfb-algebraic-adjoin-transcendence-bound. They state respectively the actual tensor-coordinate formula, the residue field as localization modulo the prime, and the cardinal upper bound for an algebraic extension of a generated subalgebra. The proof writes out why this residue field is the fraction field of the prime quotient: exactly the nonzero quotient elements are inverted. It then writes out why that fraction field is generated as a field by the images of the fixed a_i over kappa(v). Every rational expression x/y satisfies yT-x with nonzero leading coefficient y in the generated subalgebra, so the algebraicity hypothesis of the cited Mathlib leaf holds. Repeated or vanishing images only decrease the cardinality of s. No source finiteness or Noetherian condition is imposed on the arbitrary C or B.

For step 3 I read morphisms.tex Tag 02GL (lemma-etale-over-field), especially part (2), and the affine-chart meaning of etaleness in def-weil-etale-morphism. I opened lem-trf-space-fibre-products-etale-covers: it explicitly preserves jointly surjective etale families under arbitrary base change, and it supplies scheme representability of the common chart. Thus T -> U is surjective and both projections are etale; a t above u exists. I opened lem-weil-pbc-etale-algebra-residue-field-separable: its hypothesis is an etale ring map, so the proof explicitly restricts each scheme projection to affine neighbourhoods before applying it. The source and target primes are related by contraction. The two residue extensions are finite separable and therefore algebraic, and the maps from kappa(v) commute by the fibre-product square. I did not assume that U was quasi-compact or that its map to X_B was surjective.

For step 4 I opened lem-kun-transcendence-degree-tower: it includes both the cardinal tower equality and vanishing exactly for algebraic upper extensions. Applying it to the two towers removes the algebraic degrees and compares the two chart residue fields. This is a short substitution, explicitly marked elementary, and needs no new comparison lemma. The bound from step 2 is finite, so the final cardinal bound is the stated integer bound.

I tested empty X and empty B (vacuous, D=0 allowed), a zero-generator atlas (the field generation calculation gives degree zero), arbitrary non-Noetherian B, non-surjective charts and infinite disjoint unions of charts (the argument is pointwise). For affine d-space the generic fibre point has degree d and its d polynomial generators supply D=d. I checked that no affine intersection or arbitrary scheme is assumed affine: only a chosen affine neighbourhood of v and its affine pullback are used. Each non-elementary input has an existing node whose statement says exactly what is used, and citations.json quotes those statements verbatim. All steps are under 2000 characters. This delivery creates no unsplit node, duplicate, clause restatement, or hidden proof in a new-node statement. B--E were checked against the actual JSON and source texts; there is no circular dependence on the item.
