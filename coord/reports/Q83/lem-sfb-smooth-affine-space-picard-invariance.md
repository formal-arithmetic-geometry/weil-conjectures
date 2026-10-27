## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-smooth-affine-space-picard-invariance.json`: statement; split into five steps; no Mathlib match. Statement and statement dependencies unchanged.
- `citations.json`: all 15 step/node occurrences, with verbatim statement quotations.
- `searches.jsonl`: actual Q83 search-command records. The item's earlier Q16 searches are retained in the node; none is presented as a new Q83 search.

New nodes: 0. New Mathlib leaves: 0.

## Attachments

None. Searched the live `lean/WeilConjectures/` for the exact blueprint tag and for Picard/homotopy/polynomial/affine-space terminology. No declaration states this item exactly. The existing smooth-regularity declaration is used through its already existing DAG node, not claimed to prove the Picard assertion.

## Wanted

None. All proof inputs were read in the local Stacks sources.

## Changes and source route

The imported item had no proof. Its source field suggested a Chow-group argument using 02TT and 0BE9. Those tags are mathematically relevant, but the existing DAG already contains the direct line-bundle argument: Divisors 0BD7 (`lemma-in-image-pullback`) and 0BDA (`lemma-open-subscheme-UFD`). Varieties 0BEH (`lemma-rational-equivalence-for-Pic`) explicitly applies these two results to the projection from a product with an open of affine space. Its proof gives descent of the entire line bundle, stronger than its stated equality of two restrictions. Our proof uses that published argument with the whole affine space, then the zero section. It cites the actual descent node, not the weaker statement of the existing normal-variety parameter-restriction node. This avoids a C4 mismatch.

The statement is true as written and needs no perfection hypothesis. No statement dispute or target/unit change. The current `literature/blueprint/latest/` direct-image proof (3), the inherited supporting Picard prerequisite, and the unit route were read. This is an implementation of that supporting prerequisite below the unit, with no replacement of a unit step. The source's missing hypothesis checks are written out in the split.

Off-unit tools declared in `split_report.tool_uses`: smooth-over-field regularity (`lem-weil-pbc-smooth-scheme-over-field-regular`) and only clause (1) of `rem-pc-regular-normal`. They provide generic geometric inputs to normal-base descent; no statement in this unit replaces them. All other substantive Picard inputs already belong to this unit, and polynomial flatness and affine tensor products are existing Mathlib leaves.

## Searches and reuse

Read the existing nodes for the normal-variety affine-parameter restriction assertion, affine-cell Picard product, normal-base generic-line descent, and affine-space invertible triviality. The first is weaker than the needed descent assertion and its statement is not used. Reused the underlying existing descent and affine-space-triviality nodes instead. Whole-blueprint searches `Picard`, `homotopy invariance`, `0BD7`, and `affine space` found no blueprint statement equivalent to this item. `blueprint_refs.py ancestor` reports a null ancestor inherited from the item, so its preexisting `from.node`, `from.place` and `via` are retained and `same_as` is an empty list.

The required command ran LeanSearch, Loogle, LeanFinder (two different formulations), a broad grep, and a focused grep in `RingTheory/PicardGroup.lean`. All were available. The results only supply Picard functoriality, relative Picard kernels, or affine-space constructions. Read `Mathlib/RingTheory/PicardGroup.lean:549-620`: `mapAlgebra`, `mapRingHom`, and their composition lemmas do not assert bijectivity for polynomial extension. Exact queries and actual returned metadata are recorded. No search is invented and no unsuccessful service is called a negative result.

## Not duplicates

No new nodes were created. In particular, no generalization of the item, clause of the item, or elementary polynomial/functoriality step was made into a new node.

## Review by Q83

I checked the unchanged item against the cited Chow sources (chow.tex 02TT and its divisor/invertible-sheaf section; divisors.tex 0BE9), then read the shorter published argument in varieties.tex 0BEH and the complete statements of divisors.tex 0BD7 and 0BDA. For the regularity prerequisites I read varieties.tex 056S and properties.tex 0569. For polynomial-projection hypotheses I read the affine-spectrum fibre-product node, morphisms.tex 01U5 and 01T6, and the defining polynomial description of affine space. There are no new-node sources to review.

Step 1 uses precisely the smooth-regularity node's local Noetherianity and regularity conclusion, then clause (1) of the regular-normal node. It does not use the latter's Noetherian decomposition clause, dimension restrictions, or connectedness. Integrality follows directly by taking the identity field extension in the item's hypothesis.

Step 2 uses the affine-space definition and affine-spectrum tensor-product statement to identify the projection with the polynomial coefficient inclusion. The inverse ring maps are explicit. The existing polynomial-projection flatness node says that very map is flat, including zero variables. The finite-type definition verifies the finite list of algebra generators, and the local-Noetherianity-under-locally-finite-type node applies to the base from step 1. No unsupported assumption that smoothness implies perfection is used.

Step 3 uses the affine-spectrum tensor-product statement again, now for the residue-field fibre. The polynomial-field-UFD node explicitly includes being a nonzero domain, which gives nonempty integral spectrum by the zero generic prime and domain localizations. It is the residue-field fibre, not a fibre over an algebraic closure, that the descent lemma requires. The computation works for every point and includes the generic point.

Step 4 first checks preservation of local rank-one frames directly from the tensor-pullback and invertible-module definitions. The affine-space-triviality node is over an arbitrary field, so it applies to the function field without perfection. I opened the full statement of the generic-line-pullback node: it gives existence of an invertible module downstairs with pullback isomorphic to the given module. Its five hypotheses are all verified in steps 1--3 and the opening of step 4. It assumes either quasi-compactness or local finite type; we supply local finite type, so no unstated global Noetherian or properness hypothesis is needed.

Step 5 cites the fibre-product universal property to construct the section and establish its composite with the projection, and the module-pullback node explicitly states identity and composition isomorphisms. The local tensor formulas spell out why the induced maps are group homomorphisms. Surjectivity plus the left inverse proves injectivity, and the displayed calculation proves the right inverse as well. This identifies the particular inverse requested by the item. This routine assembly is elementary; it conceals no line-bundle descent theorem.

I checked B--E individually: statements are self-contained; all substantive inputs are existing nodes; none is cited for a fact found only in its proof; all 15 quotations are verbatim; proof dependencies equal the union of step citations; no source route uses SGA; there is no moved-out clause or circular use of the item. Every step is below 2000 characters. Small cases checked: n=0 gives identities; X=Spec(F) gives the trivial Picard group of affine space; the same argument holds over imperfect fields; the hypotheses exclude empty X but none of the steps manufactures an F-rational point of X. The zero section exists over any base. No correction to the statement was necessary.

## Unfinished work

None in this one-level split. Existing supporting nodes retain their own independent stage state.
