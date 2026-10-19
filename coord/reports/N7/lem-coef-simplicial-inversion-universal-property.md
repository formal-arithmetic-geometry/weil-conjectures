# Stage-1 repair report: lem-coef-simplicial-inversion-universal-property

1. Files written

- `dag/nodes/sec-six-functors/lem-coef-simplicial-inversion-universal-property.json`: item, same statement; six proof steps, with Steps 2–4 repaired and accepted Steps 1, 5 and 6 retained. Not a Mathlib leaf.
- `dag/nodes/sec-six-functors/lem-coef-simplicial-derived-pushout-mapping.json`: new statement-only lemma. It now defines the framed function complex using ordinary Hom sets, and states its Kan, homotopy-category, span/pushout and family/coproduct comparison properties. No Mathlib match.
- `dag/nodes/sec-six-functors/lem-coef-simplicial-walking-groupoid-components.json`: new statement-only lemma, strengthened to a weak equivalence onto the union of invertible components, with compatible choices making it a trivial Kan fibration onto that union. No Mathlib match.
- `citations.json`: exact statement quotations for all ten step/node citation occurrences.
- `searches.jsonl`: retained all eight earlier executed searches and appended seven executed searches for the repaired statements. The new-node search fields preserve the original results and record the new queries literally; the two older grep query fields were normalized to their actual logged regex, with the subdirectory separate.
- `report.md`: this current repair report. The returned proof and review have been retained as `returned-packet.json` and `returned-report.md`; they document the earlier attempt and are not the repaired split.

There are **2 new nodes and 0 Mathlib leaves**. No Lean was written, no compiler was run, and no repository or launcher file was changed.

2. Attachments

None. Read-only searches of `WeilConjectures/` in both specified source trees for the exact item id, derived-pushout/mapping terminology and walking-groupoid terminology found no project declaration stating the complete item. The upstream reference is not evidence of a finished proof. The item remains unsplit in the current repository; its statement agrees verbatim with the sandbox. Comparison with that repository also found that the earlier second reader had incorrectly changed the item's `created` ancestry to itself/N7. This repair restores the repository's parent `lem-coef-simplicial-localization-comparison-calculus` and group Q71. The two actual new nodes retain item/N7 creation records.

3. Wanted sources

WANTED: Jacob Lurie, Higher Topos Theory, Appendix A.3.5, Notation A.3.5.1, Remark A.3.5.2, Lemmas A.3.5.3–A.3.5.4 and Proposition A.3.5.5, and Example A.3.2.18, for this item and the walking-groupoid lemma. Read online at https://people.math.harvard.edu/~lurie/papers/HTT.pdf on 2026-10-17; not archived in the project.

WANTED: Mark Hovey, Model Categories, Definition 5.2.7, Theorem 5.2.8, Corollaries 5.4.4 and 5.4.8 and Theorem 5.4.9, for `lem-coef-simplicial-derived-pushout-mapping`. Read online at https://www.sas.rochester.edu/mth/sites/doug-ravenel/otherpapers/hovey-model-cats.pdf on 2026-10-17; not archived in the project.

The split is `proof_origin.by = agent`. The stronger function-complex statement is an agent-stated supporting theorem, not a claim that HTT Proposition A.3.5.5 states that theorem. No Stacks tag states these enriched homotopical assertions; no SGA source is used.

4. Returned faults and repairs

- **B3, undefined enrichment:** the new derived-pushout lemma now uses ordinary sets of enriched functors from terms of a cosimplicial frame. It defines the augmentation, degree-zero object, latching cofibrations, degreewise weak equivalences, and simplicial operators. Its statement dependencies explicitly include the existing Reedy model theorem and Kan model theorem, in addition to the two Bergner interval inputs. No assumption that the Bergner model category is a simplicial model category occurs. The function-complex existence and comparison assertions are theorem clauses, not data supplied by an unnamed existence assumption.
- **C6, possible circular repair:** coherent-nerve, hammock and the existing cosimplicial-frame mapping comparison remain excluded: their transitive dependencies reach this item. The existing model-colimit/localization comparison also reaches the item through system localization and pinched rigidification. In contrast the Reedy model and Kan right-proper nodes used here have no dependency path to the item. These paths were read from node statement/proof dependencies, without running a local project check.
- **C4/E3, insufficient pi_0 criterion:** the walking-groupoid statement now gives a weak equivalence onto a union of connected components, equivalently weakly contractible homotopy fibers there and empty homotopy fibers outside. It additionally permits compatible frames making restriction a Kan fibration, hence a trivial Kan fibration onto that union. Step 3 uses those choices from the outset; it does not quietly assume that the product of arbitrary replacement maps is a weak equivalence. Step 4 computes the homotopy pullback by a strict pullback of this fibration, then proves its projection to the admissible subcomplex is a trivial Kan fibration by boundary lifting. Thus the connected-fiber inference rejected by the reviewer is removed.
- **E4, the wrong path-component category:** a vertex of a mapping set of RT is tested in pi_0(RT). The item's pi_0(T) formulation is recovered by the equivalence pi_0(T) -> pi_0(RT), rather than by identifying their object sets or vertices.
- **C1, pi_0 of mapping complexes:** the derived-pushout lemma explicitly states the natural bijection with Hom in h sCat and its restriction/composition compatibility, as well as the induced pi_0 functor's invariance up to natural isomorphism. Step 2 cites it, and Step 4 uses precisely that stated compatibility.
- **C1, coproducts to products:** the same supporting theorem explicitly states the comparison for every small family, with empty family included and compatibility with restriction. Step 3 cites this clause. Products of the resulting trivial Kan fibrations are then proved directly by choosing each boundary lift coordinatewise.

The imported item has no statement dispute: its statement is retained exactly, and neither the unit route nor the chapter route was changed. The sources give the original mapping property; the two new nodes isolate the smaller technical ingredients without moving the item wholesale into a replacement node.

## Not duplicates

lem-coef-simplicial-derived-pushout-mapping vs lem-coef-cosimplicial-frame-mapping: the existing statement identifies framed complexes with a universal coherent localization and includes Quillen naturality, but does not state the span-to-homotopy-pullback or arbitrary-coproduct-to-product comparisons used here. It also depends transitively on the item. The repaired node needs only the ordinary-model homotopy category and those two colimit shapes; it does not reintroduce the coherent-localization conclusion. The frame data are defined inline in the new statement, not created as a second definition node.

lem-coef-simplicial-derived-pushout-mapping vs lem-coef-model-colimit-localization-comparison: the latter says projective homotopy colimits become colimits in a universal infinity localization, and depends transitively on the item; it does not give the ordinary-Hom frame presentation and its particular function-complex restriction maps. The repaired node has no universal infinity-localization assertion.

lem-coef-simplicial-derived-pushout-mapping vs lem-coef-model-cofibrant-colimit-comparison: the latter proves weak-equivalence preservation for cofibrant colimit diagrams; it does not compute mapping function complexes.

lem-coef-simplicial-derived-pushout-mapping vs lem-coef-reedy-model-structure: the existing Reedy theorem supplies the latching and Reedy conventions and is cited. It does not state the framed function-complex theorem or either derived mapping comparison.

lem-coef-simplicial-walking-groupoid-components vs lem-coef-complete-segal-walking-isomorphism: the existing statement concerns endpoint restriction for vertically Reedy fibrant homotopy Segal spaces and a completeness criterion. The new statement concerns arrow restriction in framed Bergner function complexes for arbitrary simplicial-category targets, with image the invertible-arrow components; no comparison of those two models is assumed.

lem-coef-simplicial-walking-groupoid-components vs lem-coef-cofibrant-homotopy-groupoid-completion: the latter is a mappingwise comparison for degreewise groupoid completion of a fixed-object cofibrant simplicial category already having groupoidal pi_0. It does not compute function complexes from the walking groupoid into arbitrary targets.

lem-coef-simplicial-walking-groupoid-components vs lem-coef-simplicial-inversion-universal-property: the new lemma computes the single generating arrow restriction on entire function complexes, including higher homotopy fibers. The item concerns arbitrary C and W, and derives its injectivity/image, characterization under C and functoriality by the span calculation and explicit pullback argument. The strengthened lemma is the technical ingredient the returned review explicitly requested.

The complete blueprint was searched by `blueprint_refs.py` for cosimplicial frame, homotopy pushout, walking groupoid, derived mapping and A.3.5. No blueprint node states either new theorem. The lone derived-mapping blueprint hit is the coefficient dualizing-object theorem, not a theorem about function complexes of simplicial categories. Source-place and keyword searches in the whole DAG were also read; the relevant near matches are distinguished above. No new Stacks-tag pair is introduced.

## Review by N7

I read the worker brief, stages/1-dag.md, the three levels and tool-lemma requirements of SETUP.md, GOAL.md, coord/dag-sync.md, the worker role, and all delivery-errors B–E. I compared the retained sandbox packet to the current repository, read the chapter and unit records, and read the ancestor's current-blueprint proof: the inherited foundation serves its second-paragraph derived-adjunction mapping calculation. I read the returned faults as mathematical requirements, rather than treating the initially successful mechanical dry run as an endorsement of the returned proof.

For the item I read HTT A.3.5.1–A.3.5.5 online, including the cofibration replacement of the walking isomorphism and the proof of injectivity, and checked the role of Example A.3.2.18. For the framed-complex node I read Hovey's frame definition in 5.2 and the ordinary-model function-complex results in 5.4. Its source field distinguishes these frame results from the additional agent-stated span and family comparison theorem. For the walking-groupoid node I checked HTT's pointwise invertibility test and the need for the stronger full function-complex assertion requested in the return. That assertion remains an unsplit theorem to be proved, not an inline proof sketch or a purported quotation of a pi_0 theorem.

Step 1 retains the accepted argument and cites the interval-lifting node's exact generators/factorizations and the interval-cell-stability node's exact weak-equivalence closure and J-cell acyclicity. The model structure is already specified in the item; this step imposes no local Kan hypothesis on C.

Step 2 uses the derived-pushout lemma's displayed function-complex formula, its pushout comparison and its explicit pi_0/Hom bijection. I checked those exact clauses in the new statement, not a proof or a definition of a different localization. Source and target replacements are allowed; universes contain the span and all functor sets.

Step 3 uses the coproduct/product clause of that same node and the walking-groupoid node's stronger equivalence/fibration clause. The arrow is tested in pi_0(RT). The choice of compatible frame models making restriction a Kan fibration is explicitly in the cited statement. The Kan model node says a trivial Kan fibration is exactly a map lifting all boundary inclusions, which justifies the coordinatewise product argument even for an infinite set W. This is a direct lifting argument, not a new uncited product-of-weak-equivalences theorem.

Step 4 still cites both supporting statements and the Kan model node. Its latter statement says that replacing a leg by a weak equivalence followed by a fibration computes the homotopy pullback. Here the chosen leg is already a fibration. I wrote out why a component-union inclusion is a Kan fibration, why the pullback projection has boundary lifts and hence is trivial, and why pi_0 of a component union injects. The identification with homotopy classes and the induced pi_0 functor is an explicit clause of the framed-complex node. Equivalence of pi_0(T) and pi_0(RT) preserves and reflects invertibility. This establishes the exact image condition and proves that q itself inverts W by applying it to the identity of the localization.

Step 5 retains the accepted elementary under-C argument: the preceding identity application makes q and q' admissible, so the two maps exist, and injectivity makes both composites identities. Step 6 retains the accepted naturality argument and cites the derived-pushout lemma's explicit maps-of-spans, identities and composition clause. It does not cite coherent-nerve naturality.

Small cases were checked for both new statements as well as the item. For W empty the products are points and the derived pushout is C. For an identity arrow the restriction lies in the admissible union; for C empty necessarily W is empty. For C=[1] with its nonidentity arrow marked, the localization is the walking groupoid. For a discrete target with a noninvertible arrow, that component has empty homotopy fiber; for a discrete groupoid every arrow component is admitted, without losing its object-automorphism data. For the empty target both walking-domain function complexes are empty and the equivalence is empty-to-empty. The initial simplicial category has its constant initial frame, so every ordinary Hom(empty,RT) is a singleton and Map^h(empty,T) is a point, agreeing with the empty-coproduct formula. Coproducts here are disjoint unions, so mappingwise and pi_0 weak equivalences are preserved by that particular coproduct construction.

I also tested the reviewer's diagnostic example: both maps pt -> S^1 have a connected ordinary fiber over the basepoint, but their homotopy pullback has components indexed by Z. Neither map is a weak equivalence onto the full connected component S^1, so the repaired walking-groupoid hypothesis excludes exactly that false inference. Contractibility of the full homotopy fibers, not their mere connectedness, is now used.

Against B–E: both children are self-contained unsplit statements with empty proof/proof_deps, all object hypotheses and definitions are explicit or cited, TeX is encoded once, source places are precise and archival gaps are WANTED, every Mathlib search was executed and read, duplicate and cycle candidates were examined, and no clause of the item is simply relabelled as its proof. All non-elementary steps cite statements which explicitly contain their inputs; citations.json gives verbatim quotations. No non-elementary step exceeds 2000 characters (the longest is Step 4, 1308 characters), and no extra standard comparison is hidden inside a long step. The proof is acyclic on this packet and uses only its unit's existing foundation inputs. No tool-use exception or route departure is requested.

5. What remains

The two supporting statements are intentionally unsplit for later stage-1 work. The required server dry run is run on this repaired packet before handoff; no push is authorized for this worker. The fresh second reader must review and deliver the accepted sandbox.

## Server dry-run repair

The first dry run of the mathematical repair rejected the phrase “the item’s” in Step 4 under B2. I replaced it with the full induced-functor/invertibility condition. I also made the supporting mapping theorem define h sCat explicitly as localization at Dwyer–Kan equivalences, with cofibrant-fibrant homotopy representatives, and refreshed the exact quotations. No mathematical conclusion changed. The required dry run is rerun on these final files.

The repaired mathematical packet passed the server preflight (including check_dag and review_split) with no push. The final dry run also includes the clarified empty-category check and corrected character count in this report, so its handoff receipt is for the final sandbox contents.

## Second reading by N7

- Item statement: checked against HTT Appendix A.3.5, Notation A.3.5.1, Remarks A.3.5.2, Lemmas A.3.5.3–A.3.5.4, and Proposition A.3.5.5; all hypotheses (small simplicial categories, marked vertex arrows, derived pushout, homotopy classes, and the induced \(\pi_0\) functor) are present and the conclusion is unchanged.
- Step 1: checked against the statements of `lem-coef-simplicial-interval-lifting` and `lem-coef-simplicial-interval-cell-stability`; generator, factorization, retract, two-out-of-three, and relative-cell facts are exactly the cited inputs, with no hidden local-Kan assumption.
- Step 2: checked against the full statement of `lem-coef-simplicial-derived-pushout-mapping`; the framed ordinary-Hom mapping complexes, homotopy-pullback comparison, and \(\pi_0\)-to-\(h\mathrm{sCat}\) bijection justify the projection and its interpretation.
- Step 3: checked against the coproduct/product clause of `lem-coef-simplicial-derived-pushout-mapping`, the componentwise trivial-fibration clause of `lem-coef-simplicial-walking-groupoid-components`, and boundary lifting in `lem-coef-kan-quillen-right-proper`; coordinatewise lifts also cover infinite and empty families.
- Step 4: checked against the same three statements; component unions are Kan-fibrant inclusions, the displayed strict pullback computes the homotopy pullback after the stated replacement, and the resulting \(\pi_0\) image is exactly the invertibility condition in the item.
- Step 5: checked the elementary two-sided inverse argument directly from the item’s injectivity and image clauses; both composites have the same restriction and no additional theorem is used.
- Step 6: checked against the maps-of-spans, identity, and composition clause of `lem-coef-simplicial-derived-pushout-mapping`; the functoriality conclusion follows without importing coherent-nerve or hammock results.
- `lem-coef-simplicial-derived-pushout-mapping`: checked self-contained definitions, statement dependencies, Hovey frame source, blueprint search, duplicate candidates, and all recorded LeanSearch/Loogle/LeanFinder/grep searches; verdict unsplit, no Mathlib leaf.
- `lem-coef-simplicial-walking-groupoid-components`: checked the walking-arrow/groupoid definitions, invertible-component criterion, Kan-fibration strengthening, HTT source, blueprint search, duplicate candidates, and all recorded searches; verdict unsplit, no Mathlib leaf.

Changes made: no mathematical or statement changes were needed. I added this independent second-reading audit, preserved the worker’s report and citations/search logs, and kept the two supporting nodes as statement-only unsplit nodes. I also checked the empty marking, empty category/target, identity arrow, discrete noninvertible target, and walking-groupoid cases; each agrees with the statements. No Lean, compiler, Lake, or repository write was performed.
