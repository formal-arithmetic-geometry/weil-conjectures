# Stage-1 report: lem-sfb-flat-root-tower-nonzerodivisor

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-flat-root-tower-nonzerodivisor.json: existing statement split into six steps, with no change to its statement. Full tower assertion has no exact Mathlib match; component results already have DAG nodes.
- citations.json: verbatim statements for every step/dependency pair.
- searches.jsonl: actual msearch.py results; inherited item searches retained and current searches appended to the item.
- report.md: this report.

New nodes: 0. New Mathlib leaves: 0.

## Attachments

None. Searched the project library by the exact blueprint tag, nonzerodivisor terminology, simultaneous roots and root towers. The purely inseparable field root-tower declarations do not give this commutative-ring statement. No attachment is asserted from a Mathlib declaration or a sorried project theorem.

## WANTED

None. The complete combined assertion is an agent assembly, as the imported source explicitly says; all its ingredients are in the local Stacks sources and existing DAG statements.

## Findings and changes

The statement survives all checks and is unchanged. Its proof was empty. Added the quotient/algebra notion to stmt_deps, and supplied the diagram verification, flat scalar argument, induction on the number of roots, eventual-zero argument, second flat scalar argument, and the empty-variable case. No transition-map injectivity is needed.

The item is a descendant of the current blueprint direct-image clause (3), through the boundary nonzerodivisor part of lem-sfb-snc-root-limit-normal-charts. The current blueprint file was read, as were the chapter and unit records. The unit record is the inherited broader ctf-stability route; this algebraic prerequisite replaces none of its steps. tools/blueprint_refs.py ancestor returns None for this already imported extraction. Retained the supplied null ancestor and via chain, and the precise inherited place. Whole-blueprint searches for monic, nonzerodivisor, root, flat, simultaneous and the exact item wording found no equivalent blueprint assertion. The source and route metadata are not rewritten to pretend that the full generalized assertion is a quoted Stacks lemma.

## Not duplicates

No new nodes were created. In particular the generic flat-tensor, monic quotient, and commutative-ring filtered-colimit nodes were reused rather than duplicated. The stronger single-root tensor-coordinate node lem-sfb-monic-quotient-faithful-tensor-coordinates was inspected but is unnecessary for the proof.

## Review by Q135

I read Stacks algebra.tex Definition 00HB (definition-flat), the monic finite-free quotient used in the proof of 04GG (lemma-characterize-henselian), implication (10) to (1), and Lemmas 00D6 (lemma-directed-colimit) and 00D7 (lemma-zero-directed-limit). I also read categories.tex Section 04AX (section-directed-colimits), including its equivalence-relation description preceding 002W. These explain the component arguments, while the full finite-root and colimit assembly is recorded as agent-written. There are no new-node sources to audit. Mathlib searches used only msearch.py, including a second semantic phrasing; I read the actual hits, Flat/Basic.lean's tensor-injection and IsSMulRegular.of_flat declarations, and AdjoinRoot.lean's powerBasis' and free_quotient declarations. These are components, not a one-line specialization proving the whole item.

For step 1 I opened def-weil-pbc-category-colimit, which explicitly defines filteredness and the universal cocone, def-weil-pbc-mv-polynomial-ring, which supplies evaluation and determination by generators, and def-weil-pbc-algebra-hom-quotient, which supplies the quotient with its surjective map and kernel. Evaluation kills each displayed relation, and exponent multiplication checks composition. The elementary step includes that calculation rather than hiding diagram coherence in a citation. Positive integers and divisibility give an actual small nonempty directed poset.

For step 2 I opened lem-trf-flat-tensor-preserves-injection: its statement explicitly assumes an injective linear map and a flat module and concludes injectivity of the induced tensor map. Here those hypotheses are exactly multiplication by c on A and the given flat A-module R. I also read def-weil-pbc-module-tensor-product: its universal property, generating pure tensors, and relations give the two explicit inverse maps written in the step. Thus the tensor map really is multiplication by a(c), without any faithful-flatness or nonzero-ring hypothesis.

For step 3 I opened lem-weil-pbc-monic-quotient-free. Its statement gives the actual power basis, not just finite generation; these unique coordinates justify cancellation coefficient by coefficient. The induction claim, base, and induction step are written out. I corrected a potential zero-ring gap before writing the final proof: a zero coefficient ring is handled directly, before saying the polynomial has degree n. For a nonzero coefficient ring, n>0 gives the asserted degree and monicity. The identification of the iterated quotient with the simultaneous quotient is elementary from the polynomial/quotient nodes: the step writes both maps and checks their composites on every generator. It is not a new lemma hidden in a long step.

For step 4 I opened lem-pc-filtered-colimit-commrings-elementwise. Clause (1) gives a representative of every element, and clause (2) gives eventual equality for that same ring colimit. The input here is the actual small filtered ring diagram verified in step 1. Equality to zero is compared at a common later object; the two arrows from the same source agree because the index is a poset. This shows why no transition map needs to be injective. The later multiplication map is injective by step 3. No statement about a colimit of sets was silently substituted for one about rings.

For step 5 I reused the exact flat tensor statement and tensor definition opened in step 2, now over S with the supplied flat S-algebra Q. Both inverse formulas are displayed and identify the map in question. Step 6 uses the three definition nodes opened in step 1 and proves the constant-diagram colimit by its universal property, using the arrow 1 to n. Thus S=R means its canonical identification, not equality of arbitrary choices of colimit objects.

I checked delivery-errors B through E, including the repeated sections. B: no statement-only node was given an unauthorized proof; every notion used in a statement is inline or has its existing definition dependency; TeX is encoded once; sources name labels and tags; no unrun searches are invented. C: every non-elementary ingredient is an actual cited statement, opened and quoted verbatim in citations.json; no proof internals or definition-only substitute is used. The existing tools have no dependency on the item, so this split adds no cycle. All off-unit citations are generic algebra tools or definitions and are declared in split_report.tool_uses. D: the proof carries its argument and creates no nodes restating clauses; its induction is explicit. E: I checked all hypotheses and maps, including the two different base rings in flat tensoring and the quotient-generator identifications.

Small cases checked: r=0 gives the identity diagram and canonical R colimit; n=1 gives linear root equations and the expected quotient; t_d=0 allows nilpotent roots and does not affect monic division; c a unit makes the multiplication assertions automatic; R=0 makes every root stage and its colimit zero; Q=0 is an allowed flat zero module; a zero base A forces all unital target rings zero; no normality, reducedness, characteristic, coprimality, invertibility or Noetherian assumptions enter. All six steps are under 2000 characters (maximum 982), so none conceals a long comparison needing another node.

## Unfinished work

None in the stage-1 split. No Lean file was written and no compiler or Lake/build command was run. Dry run and push are the required final checks and delivery actions.
