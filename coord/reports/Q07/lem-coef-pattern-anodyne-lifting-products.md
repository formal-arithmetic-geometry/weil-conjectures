# Stage-1 repair: lem-coef-pattern-anodyne-lifting-products

## Files written

- `dag/nodes/sec-six-functors/lem-coef-pattern-anodyne-lifting-products.json`: split statement, nine steps, no Mathlib match; statement unchanged from shared main.
- `dag/nodes/sec-six-functors/lem-coef-pattern-generator-product-cells.json`: retained, corrected statement-only helper, no Mathlib match; generator products and sharp left-anodyne inclusions.
- `dag/nodes/sec-six-functors/lem-coef-finite-inverse-tetrahedron.json`: new statement-only helper, no Mathlib match; equivalence witnesses with the exact opposite-edge-collapse tetrahedron used by A1.
- `dag/nodes/sec-six-functors/lem-coef-cocartesian-cone-limit-section-test.json`: new statement-only helper, no Mathlib match; the general section-limit comparison of HA B.0.26.
- `dag/nodes/sec-six-functors/lem-coef-relative-limit-join-slice-recognition.json`: new statement-only helper, no Mathlib match; the converse from relative finality in the fixed-diagram join slice to relative-limit mapping universality.
- `citations.json`: literal statement excerpts for all step/node pairs. Existing search logs and reference results are retained.

Four new nodes relative to shared main, zero Mathlib leaves. The provisional `lem-coef-relative-limit-join-boundaries` was removed when a current-main duplicate was found; its searches remain as history only.

## Attachments

None. Searches in the project Lean source for the blueprint item tag and categorical-pattern/anodyne terminology found no finished project declaration giving every clause. Upstream sorry declarations are not attachments. No Lean was written or compiled.

## WANTED

WANTED: archived Lurie, Higher Algebra, Appendix B, Definition B.0.19, Example B.0.21, Remark B.0.26, Definition B.1.1, Propositions B.1.6 and B.1.9, Lemmas B.1.10–B.1.13, Proposition B.1.14 and Example B.2.2, for the item and all four new nodes.

WANTED: archived Lurie, Higher Topos Theory, Proposition 3.3.3.1, for `lem-coef-cocartesian-cone-limit-section-test`. HA B.0.26 states the section-limit equivalence and its exact-extension consequence explicitly. The shared literature lacks these archives; the item has `proof_origin.by = agent`. Reference text used for this repair is retained in the sandbox.

## Returned faults and repairs

STATEMENT-DISPUTED: the former auxiliary product-cell statement was false, although the item statement is correct. Its J0 used Cartesian final horns instead of the cocartesian point pattern. The supplied counterexample is P=P0, u the empty-to-point map, and h the final marked horn `{1}# -> (Delta^1)#`. Then u square h=h. The inclusion `{1}# -> (Delta^1)#` has RLP against the true point-pattern generators (outgoing edge and initial/inner horn problems forced into the terminal vertex; marking-only maps add no underlying simplex), but not against itself over the identity. Hence h is not point-pattern anodyne.

E2: J0 now consists exactly of A0,A1,B0,C0,C1, with INITIAL vertex B0 and INITIAL marked horn C0, and no cones. W0 is their weak saturation. The sharp ordinary LEFT-anodyne maps belong to W0 by B.1.13. No equality with ordinary left-anodyne or Cartesian marked-anodyne classes, and no positive-sharp-horn claim, remains.

E3: products use the correct point-pattern subfamily. Sharp nonfinal horns give LEFT fibrations, as B.1.14 requires. The right-fibration-over-Kan tool is used through explicit opposite/order reversal, not by claiming the original map is a right fibration. The proof no longer identifies an arbitrary-source marked internal Hom with a core using an inapplicable specialized assertion.

C1/D3: Steps 1–4 give every generator recognition argument. The missing finite Q witness and cocartesian section comparison are smaller generic helpers. The converse join-slice recognition is a separate generic helper; the forward implication and relative-final boundary criterion use existing statements, not a definition node or a bare B.1.6 citation. The cyclic `lem-coef-pattern-anodyne-generators` is unused.

C8: `split_report.tool_uses` declares the generic tools `lem-cbc-right-fibration-space-fiber`, `lem-cbc-inner-fibration-equivalence-outer-horn-lift`, and `lem-cbc-equivalence-outer-horn-filling` with their precise roles. They do not replace the coefficient-theoretic blueprint route.

The prior report's assertions equating W0 with Cartesian marked-anodyne maps and verifying positive sharp horns were wrong. This report supersedes those claims; the retained logs and source records preserve the search history.

## Not duplicates

- lem-coef-pattern-generator-product-cells vs lem-coef-pattern-anodyne-generators: the helper states generator products and sharp left-horn membership; the existing node recognizes fibered objects/trivial cofibrations and depends on this item, so citing it here is cyclic.
- lem-coef-pattern-generator-product-cells vs lem-coef-marked-anodyne-lifting-calculus: the latter uses Cartesian final horns and marked mapping recognition; the helper uses cocartesian initial horns and product-cell membership.
- lem-coef-finite-inverse-tetrahedron vs lem-coef-marked-anodyne-lifting-calculus: that detector collapses specified faces to degeneracies of edge 01; Q here collapses opposite edges 02 and 13 and detects central edge 12. Its extension is into any quasicategory, without a lifting assumption on a marked object.
- lem-coef-finite-inverse-tetrahedron vs lem-coef-pattern-anodyne-generators: the latter mentions Q as a generator but does not assert the equivalence-extension lemma, and depends on this item.
- lem-coef-cocartesian-cone-limit-section-test vs lem-cbc-cocartesian-sections-limit: the existing statement is for an ordinary indexing category and a strict diagram; the new statement permits any small quasicategory K and gives the restriction isofibration, conditional full faithfulness and exact-vertex-extension criterion.
- lem-coef-cocartesian-cone-limit-section-test vs lem-cbc-cocartesian-section-currying: currying describes parameterized sections, not the limit/restriction comparison or relative-universality implication.
- lem-coef-cocartesian-cone-limit-section-test vs lem-coef-cocartesian-straightening: straightening defines classification and its base change, not the section-limit theorem.
- lem-coef-cocartesian-cone-limit-section-test vs lem-coef-pattern-anodyne-generators: the helper is a general section theorem with no pattern or anodyne maps, giving B.0.26 rather than repeating the item.

The current-main `lem-coef-infinity-relative-limit-join-boundary` is reused only for its forward implication in Step 4, and `lem-coef-infinity-relative-initial-boundary` is reused for the relative-final test in Step 3. Whole-DAG source/concept searches and whole-blueprint searches found no duplicate of the four retained helpers. Their blueprint ancestry prepends this item to its existing via list and names the ancestor's proof paragraph 2, finite-coefficient mapping adjunction before inverse limits.

- lem-coef-relative-limit-join-slice-recognition vs lem-coef-infinity-relative-limit-join-boundary: the existing node assumes the cone is ALREADY a q-limit and derives boundary fillers/relative finality; the new helper assumes no limit and proves the converse, with the slice innerness independent of a prior limit hypothesis.
- lem-coef-relative-limit-join-slice-recognition vs lem-coef-infinity-relative-cone-initial-corner: the existing node requires an isofibration and uses the full functor-category exponential corner; the helper requires only innerness and uses the fixed-diagram join slice.
- lem-coef-relative-limit-join-slice-recognition vs lem-coef-join-slice-cocone-comparison: the existing node identifies absolute join/cocone categories and absolute initiality; the helper recognizes RELATIVE limit universality for an arbitrary inner fibration.

WANTED: archived HTT Definition 4.3.1.1, Remark 4.3.1.2 and Proposition 2.1.2.1 for the new join-slice recognition helper. I read the primary HTT page 261 and its arbitrary-inner-fibration hypotheses. The new helper adds only the converse that the current join-boundary statement does not state.

## Review by Q07

I reread the return against HA Appendix B: B.0.19, B.0.21, B.0.26, B.1.1, B.1.6 with its preliminary lemma, all fourteen cases of B.1.9, B.1.10–B.1.13, B.1.14 and B.2.2. The product helper now uses B.1.9 with P times P0=P and B.1.13 for sharp LEFT horns. For n=1 this is B0; for n=2 it is C0/C1 followed by missing-edge marking via B.1.11 or A0; for n>=3 all edges already occur in the horn. A final horn cannot be substituted.

For the finite Q helper, I read both occurrences in B.1.6: the equivalence extends centrally inside a fiber's Kan core. Conversely the collapsed edges 02 and 13 give two inverse relations, so every edge of any map Q to a quasicategory is an equivalence. The closest Mathlib hit, `CoherentIso.lean`, treats the entire nerve of the walking isomorphism and inverse structures from maps out of that nerve, not this finite-Q extension statement. The two semantic phrasings and source hits do not state the helper or specialize to it in one line.

For the new join-slice recognition helper, I checked HTT Definition 4.3.1.1, Remark 4.3.1.2 and Proposition 2.1.2.1 in the primary PDF, and the equivalent C2/relative-limit assertion in HA B.1.6. Its slice/finality test is for arbitrary cones over an inner fibration; it explicitly provides the converse not stated by the existing forward-only node. Empty K recovers relative finality of a vertex. The comparison is through natural join/cone comparisons, not equality of their simplices.

For the section helper, I read B.0.26. The full subcategories of cocartesian sections retain arbitrary transformations. Relative-limit sections give the required mapping-space equivalences on restriction, and the categorical fibration upgrades essential surjectivity to actual extensions. Small K, a larger universe for Cat-infinity and a cocartesian pullback are explicit. None is silently inferred from an inner fibration alone.

Step 1 reads the fibered and horn-cocartesian definitions: C1 gives innerness, C0 gives GLOBAL cocartesianness and B0 gives lifts. C is a quasicategory, so X is too. Full scaling is essential; a local-to-global theorem is not silently used.

Step 2 uses the finite-Q extension and the initial-lift comparison stated by `lem-coef-infinity-cocartesian-composition-initiality`. The comparison edge is an equivalence in the target fiber, A1 marks it, and A0 marks the long edge over (f,id,f), all base edges lying in S. This supplies the formerly missing marking converse.

Step 3 uses the fibered definition, horn definition and initial-lift comparison to check the cocartesian pullback and its marked sections. The new join-slice recognition lemma supplies the inner fibration of fixed-diagram join slices WITHOUT assuming the cone is already a relative limit. The existing relative-final boundary criterion converts positive C2 extensions into relative finality; the new recognition lemma supplies the missing converse implication to a q-limit. The existing join-boundary node is used only in Step 4 in its stated forward direction. The section helper supplies exactly the full-faithfulness/vertex-extension criterion, so B1 proves the classifying cone is a limit. Equalities of base maps and restrictions are exact. Fixed-diagram join slices are not identified with internal functor categories.

Step 4 checks all seven converse cases separately: definitions give C1,B0,C0; composition gives A0; finite Q and the relative equivalence outer-horn tool give A1; the section test gives exact B1 extensions; the existing join-boundary lemma gives C2. The relative outer-horn tool is applied to an inner fibration of quasicategories. Cone bases are small quasicategories, as the fibered definition requires.

Step 5 is the explicit elementary saturation/RLP and monomorphism argument. A0,A1 have identity underlying maps, so marking extensions are still degreewise injective. Step 6 uses the absolute outer-horn equivalence criterion and the cocartesian definition to identify point-pattern markings. Identities supply the existence condition and cone conditions are vacuous.

Step 7 uses precisely clauses (a),(b) of the corrected product helper. Fixed Cartesian products distribute over the stated degreewise colimits, including markings, so saturation works separately in each variable without a model structure. Step 8 uses clause (c), the marked product/Hom adjunction and the left/right horn definitions: its inputs are SHARP left horns, not merely the partly marked C0 generators. Reversal sends k to n-k and meets the right-fibration tool's hypothesis. Step 9 uses the already Kan target, the same tool and the literal boundary criterion in the Kan–Quillen node, including n=0. Thus it proves a trivial Kan fibration.

I tested empty K (B1 asks for a vertex and the relative-final test uses only positive dimensions), empty mapping domains, identity inclusions, marking-only underlying identities, the point pattern and dimensions 1 and 2. No nonempty or finiteness hypothesis was added. The item statement is unchanged. Every citation quote is a literal part of the cited current statement. Raw required-command search outputs are retained; ordinary/unmarked Mathlib hits were distinguished from these marked infinity-categorical statements. Historical malformed Loogle queries are not used as absence evidence.

## What remains

A fresh second reader must review and deliver the split after its dry run accepts this sandbox. This worker does not push.

## Second reading by Q07

I independently read delivery-errors B–E, the item and all four new statements, every statement cited by the nine steps, and the retained primary HA Appendix B text (B.0.19, B.0.21, B.0.26, B.1.1, B.1.6, B.1.8–B.1.14 and B.2.2). I also opened the primary HTT PDF and read Proposition 2.1.2.1, Proposition 3.3.3.1, Definition 4.3.1.1 and Remark 4.3.1.2. These are non-Stacks infinity-categorical sources, so there is no Stacks tag to substitute. The current-blueprint and whole-DAG searches, and a read-only search of slopmaster2, were repeated; no finished project declaration was found. Upstream sorry declarations were not treated as proofs.

- Item statement: checked the seven maps against HA B.1.1, recognition against B.0.19/B.1.6, products against B.1.8/B.1.9, and mapping complexes against B.1.13/B.1.14/B.2.2; PASS as the fully scaled, quasicategory-base specialization, including initial horns, the central-edge quotient Q, positive C2 dimensions, empty cones and boundary dimension zero; unchanged.
- Step 1: checked the actual inner/cocartesian horn definitions and fibrancy conditions (i),(ii) against HA B.1.6(1),(2),(4); PASS: full scaling allows every initial-horn base simplex, and B0 specifies the source.
- Step 2: checked both finite-Q clauses and the initial-lift comparison statement against HA B.1.6(3); PASS: the comparison is in the target fiber, and A0 is applied over the explicit triangle (f,1,f), not over an unspecified composite.
- Step 3: checked the definitions, comparison lemma, section test, join-slice recognition and relative-final boundary criterion against HA B.0.26/B.1.6(5 prime),(6) and HTT 4.3.1.1–2; REPAIRED the pullback-edge comparison into an explicit triangle and marking argument; PASS: the join-slice innerness does not presuppose a limit and C2 supplies precisely positive-dimensional final-vertex fillers.
- Step 4: checked each of C1,B0,C0,A0,A1,B1,C2 against the cited statements and HA B.1.6 reverse; REPAIRED the B1 paragraph to give exact extension using the isofibration and to prove the new section edges globally cocartesian via a fiber equivalence and composition; PASS, without using an RLP conclusion before proving it.
- Step 5: checked the weak-saturation argument directly; PASS elementary: pushout lifts correspond, successor lifts extend, limit lifts glue, retract lifts compose, and underlying injectivity is preserved; marking-only identities and empty chains are included.
- Step 6: checked the outer-horn equivalence criterion and fibrancy definition against HA B.0.21; PASS: over a point the absolute horn criterion identifies exactly equivalences, identities give lifts and no cone condition remains.
- Step 7: checked clauses (a),(b) of the product helper and coordinatewise marked products against HA B.1.8/B.1.9; REPAIRED an unnecessary bare B.1.8 invocation; PASS: the helper already states products in the correct pattern, and products distribute over underlying colimits and their generated markings, so weak saturation applies separately in each variable.
- Step 8: checked clause (c), the marked product/Hom adjunction, left/right horn definitions and the right-fibration-over-Kan statement against HA B.1.13/B.1.14; PASS: sharp nonfinal horns give left fibrations, order reversal sends k to n-k, and the tool is applied over the Kan point.
- Step 9: checked the right-fibration tool and the Kan–Quillen boundary criterion against HA B.1.14/B.2.2; PASS: Step 8 already proves the target Kan, and an anodyne i gives boundary lifts in every dimension including zero.
- New node lem-coef-pattern-generator-product-cells: checked every listed generator against HA B.1.1, both product clauses against all fourteen cases of B.1.9 and the point-pattern specialization of B.1.8, and clause (c) against B.1.13; PASS B1–B7, statement-only with definitions and source locations; the C2/product filtrations and n=2 marking step are not elementary, and it does not replace recognition or the mapping-complex proof. Point pattern, identity/empty factors, n=1 B0 and n=2 initial/inner horns pass. Existing anodyne-calculus nodes use final horns; the cyclic pattern-anodyne-generators node cannot be used.
- New node lem-coef-finite-inverse-tetrahedron: checked the exact collapsed edges 02 and 13, central edge 12 and both conclusions against HA B.1.6(3),(A1); PASS B1–B7. In an ordinary groupoid the adjacent arrows are inverse arrows; in a discrete category every map is constant on the two identified vertices; for empty D both assertions are vacuous. The core-extension assertion is not a two-line consequence of the stated horn definitions. CoherentIso.lean instead treats the whole walking-isomorphism nerve, not this finite quotient or its extension property.
- New node lem-coef-cocartesian-cone-limit-section-test: checked the cocartesian pullback, arbitrary transformations, classifying cone, restriction equivalence, conditional full faithfulness and exact extension against HA B.0.26 and HTT 3.3.3.1; PASS B1–B7. Empty K reduces to a fiber being terminal; with empty total space the comparison to the one-vertex section category is not an equivalence. The existing ordinary-index/strict-presentation section theorem is insufficient; this helper contains no pattern generators and is strictly smaller than the item.
- New node lem-coef-relative-limit-join-slice-recognition: checked arbitrary inner q, arbitrary small K, fixed-diagram join simplices and the converse implication against HTT 2.1.2.1 and 4.3.1.1–2, with the cited mapping-square definition open; PASS B1–B7. Empty K gives the relative-final vertex criterion; q the identity makes every cone relatively universal; q to a point recovers ordinary limit recognition. The existing join-boundary statement assumes a limit and supplies the forward implication, and the full exponential-corner statement requires an isofibration: neither states this converse under its hypotheses.

Changes made: expanded the pullback comparison in Step 3; replaced the B1 back-reference in Step 4 by its triangle, equivalence and composition argument; removed the uncited, unnecessary source-only assertion in Step 7; corrected the split-summary helper count; added twelve independent Mathlib searches (LeanFinder, Loogle and grep for each helper) with verbatim outputs under reference/second-*.txt and matching records in mathlib_searches/searches.jsonl. The four helper statements and item statement were retained. The proposed generic off-unit tools remain in split_report.tool_uses, as review_split.py explicitly permits for reviewer approval; no maintainer-owned top-level tool_uses was added.

The duplicate search included whole-DAG and whole-current-blueprint source/concept queries, and statements of the closest section, join-slice, relative-cone and marked-anodyne nodes were opened. The independent product hits are unmarked anodyne/inner-anodyne products; CoherentIso.lean was read through its inverse-structure declarations; the section/slice hits are ordinary-category or basic SSet results. None is an exact or one-line-specialization Mathlib leaf for these helpers. Four new nodes, zero Mathlib leaves remain. All current (step,node) citation pairs were checked mechanically against the repaired uses arrays, and every retained quote remains a verbatim substring of that node's statement; citations.json therefore required no content change.
