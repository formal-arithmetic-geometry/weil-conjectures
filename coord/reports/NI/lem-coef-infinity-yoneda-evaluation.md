# Stage-1 repair report — NI

Item: `lem-coef-infinity-yoneda-evaluation`. Date: 2026-10-17.

## Files written

- `dag/nodes/sec-six-functors/lem-coef-infinity-yoneda-evaluation.json`: retained statement and nine-step proof, with steps 6–8 shortened to cite the three new supporting nodes.
- `dag/nodes/sec-six-functors/lem-coef-enriched-presheaf-rectification.json`: new unsplit statement node; Mathlib searches found no match.
- `dag/nodes/sec-six-functors/lem-coef-enriched-yoneda-evaluation.json`: new unsplit statement node; Mathlib searches found no match.
- `dag/nodes/sec-six-functors/lem-coef-enriched-nerve-transformation.json`: new unsplit statement node; Mathlib searches found no match.
- `citations.json`: regenerated verbatim quotations for every item proof citation.

No Mathlib leaves or Lean files are delivered. The item statement, `stmt_deps`, Lean record, and accepted pointwise route are unchanged.

## Attachments

None. I searched the source tree for the item id and for infinity Yoneda/presheaf declarations. The source search found no sorry-free declaration stating this item.

## WANTED:

WANTED: archived HTT, Lemma 5.1.5.2, Theorem 2.2.5.1, Proposition 4.2.4.4, Lemma 5.5.2.1, and Appendix A.3.3, for this item and the three new support nodes. I read the relevant online statements and did not modify the literature archive.

WANTED: archived Kerodon Subsection 8.3.1 (03M2), Proposition 8.3.1.3 (03M5), for the infinity-categorical Yoneda comparison. I read these online; no Stacks tag states the full result.

## Problems found and repaired

The returned review identified steps 6, 7, and 8 as non-elementary arguments longer than 2000 characters. I split those hidden arguments into three statement-only nodes. Step 6 now cites the enriched presheaf/model rectification node, step 7 cites the strict enriched Yoneda evaluation node, and step 8 cites the enriched-natural-transformation/coherent-nerve node. Each new statement is strictly smaller than the item: it concerns respectively a model presentation, evaluation in that strict model, or passage of an already-given enriched transformation through the nerve. The item continues to use the pointwise horn-filtration proof in steps 1–5 and the universe-qualified pointwise equivalence criterion in step 9.

## Review by NI

I read the current item node, its nine retained proof steps, the chapter and unit records, and every statement cited by each step. The item statement agrees with the HTT/Kerodon Yoneda-evaluation formulation: \(D\) is small, \(\mathcal P(D)\) is the space-valued presheaf infinity category, and evaluation at \(\operatorname{id}_d\) is a natural equivalence on \(D^{\mathrm{op}}\times\mathcal P(D)\), including higher homotopies. The source place and blueprint ancestry remain recorded in the node.

For step 1 I checked the statements of `lem-coef-infinity-slice-right-fibration` and `lem-coef-space-transport-classification`; they provide the right fibration and the coherent classification transport used there. Step 2 uses the slice statement and `def-cbc-enhanced-diagrams-cones`; the extra-degeneracy identities are written explicitly and cover the degree-zero case. Step 3 uses the nondegenerate-decomposition statement and the right-anodyne definition; the horn pairing and smallness ordering are written in the step. Step 4 uses the right-fibration exponentiation statement and the trivial-Kan-fibration definition; the pulled-back map is identified and the empty boundary case is addressed. Step 5 uses the trivial-Kan homotopy-equivalence statement and the classification statement; it explicitly invokes pullback compatibility at the vertex \(\{d\}\to D\) before the identity evaluation clause.

For the repaired steps, the new rectification statement says exactly that \(A\), \(q\), the projective model \(\mathsf M\), its bifibrant subcategory, and the equivalence \(\Theta\) exist with the required evaluation, mapping-complex, composition, identity, and universe compatibility; step 6 uses only that statement. The new enriched Yoneda statement gives the strict map \(\alpha\mapsto\alpha_a(1_a)\), its action-defined inverse, and full simplicial naturality; step 7 uses precisely those clauses. The new nerve-transformation statement gives the enriched interval functor, endpoint restrictions, natural whiskering, and preservation of components; step 8 uses those clauses to transport the strict transformation through \(\Theta\) and \(q\). Step 9 uses the componentwise-equivalence criterion and explicitly checks the \(\mathcal U'\)-small parameter category, empty \(D\), and empty values.

I searched the DAG and blueprint for each new support lemma before creating it. I also ran and read LeanSearch, LeanFinder, and Mathlib-source grep for each; the hits were ordinary Yoneda, enriched Type-valued transformations, simplicial nerves, or bifibrant-object infrastructure and did not state any of the three required results. The three searches and their actual outputs are recorded in `searches.jsonl` and copied with verdicts into the node records. Small cases checked for the item and the strict construction include empty \(D\), a one-object category, a single nonidentity arrow, empty presheaf values, and an \(S^1\)-valued presheaf. No statement was weakened or given an extra nonemptiness hypothesis.


## Resumed repair and second reading by NI

On resuming the preserved sandbox I compared all item fields with the current shared node. The statement, statement dependencies, Lean record, and Lean audit are unchanged. The shared version still has the three returned long steps; the retained sandbox replaces them by the three supporting statements, so this is a substantive repair rather than an unchanged re-push. I reran the prescribed dry run first. Its five failures were the item still being marked unsplit and the three new statements lacking explicit bracket citations. I marked the completed item split and added explicit statement-level references for their notions, checking their full statements. New support nodes remain statement-only and unsplit.

I independently reread HTT Theorem 2.2.5.1 (printed p.89) and Proposition 4.2.4.4 (printed p.258), and Lemma 5.1.5.2 (printed pp.324–325), plus Kerodon 03M2 and the right-fibration exponentiation source. The first two sources provide presentation and rectification; the strict evaluation and enriched interval constructions are the explicit constructions extracted from the returned proof, not verbatim assertions attributed to those theorem numbers. Their eventual proofs remain separate stage-1 items. No SGA source is used. The small simplicial category is U-small, whereas its whole category of U-small diagrams and the parameter category are U-prime-small. The nerve-transformation node now states its larger source universe explicitly, as required when C is A-op times B.

The second reading caught a C4 gap in the shortened step 8: the interval nerve node gives the transformation but does not itself identify its endpoints with the two presheaf bifunctors. I added that coherent bifunctor and Yoneda-diagram comparison explicitly to the rectification statement and cited it in step 8. Its comparison is natural in the representable variable and retains the identity evaluation; this is what matches the canonical component from step 5. Step 7 now also lists the rectification citation already named in its text. Thus neither endpoint identification nor coherence is inferred from objectwise equalities. All 16 step/node citation pairs are regenerated as exact full-statement quotations.

I read every retained search result rather than repeating it. The supplementary Loogle search for the rectification formulation returned no hits, and the supplementary grep located Enriched/Basic.lean:539 and Sites/Monoidal.lean:51. I read both: the former identifies ordinary Type-enriched transformations with ordinary transformations, while the latter concerns the internal Hom of diagrams on an ordinary category; neither gives the simplicial enriched representable evaluation used here. I copied the actual search log records into the new nodes and retained their verdicts. The alternative semantic phrasings already in the log are now recorded too.

The B–E audit leaves the main statement fixed, introduces every object in each new statement, keeps new proofs empty, uses citations for the relevant notions, and records genuine search outputs. The three support results are generic lemmas: none restates the item's entire presheaf-infinity-category Yoneda assertion. I checked all nine steps for the 2000-character limit (the longest is step 3 at 1794 characters); each returned long argument is now an unsplit prerequisite. The pointwise-node cycle is not reintroduced, and free cocompletion is not cited. Empty categories, empty values, and the one-object enriched category remain valid, and all maps are on full simplicial parameter spaces.

## Not duplicates

lem-coef-enriched-presheaf-rectification vs lem-coef-enriched-diagram-rectification: the existing general diagram comparison assumes a chosen enriched presentation and does not state the coherent representable diagram, its identity comparison, or the comparison of the restricted mapping bifunctor with presheaf Yoneda evaluation; the new statement packages those additional comparisons for the locally Kan presheaf model.
lem-coef-enriched-presheaf-rectification vs lem-coef-coherent-nerve-comparison: the existing node compares a simplicial category and its nerve, without the projective presheaf presentation or its coherent representable/evaluation comparison.
lem-coef-enriched-yoneda-evaluation vs lem-coef-simplicial-projective-model-calculus: the existing node gives the projective model and the mapping-end description, but does not state the enriched representable-evaluation isomorphism, its action-defined inverse, or its full two-variable naturality.
lem-coef-enriched-nerve-transformation vs lem-coef-coherent-nerve-comparison: the existing node defines and compares coherent nerves but does not state the enriched interval construction for a given natural transformation.
Whole-blueprint searches for enriched Yoneda, enriched natural transformation, and presheaf rectification returned no blueprint nodes. The item and new-node Lean searches found no project attachment. The independently reopened pointwise Yoneda node is not used as a substitute for coherence.
