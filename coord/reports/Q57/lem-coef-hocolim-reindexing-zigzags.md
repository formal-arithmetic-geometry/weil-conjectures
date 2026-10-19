# Stage-1 report: lem-coef-hocolim-reindexing-zigzags

## Files written

- `dag/nodes/sec-six-functors/lem-coef-hocolim-reindexing-zigzags.json`: statement, split; no exact Mathlib match; statement and statement dependencies unchanged.
- `citations.json`: verbatim statement excerpts for every node citation in the seven proof steps.
- `report.md`: this report. The sandbox also contains the genuine `searches.jsonl` log and the item-specific writing script; neither is a new DAG node.

New nodes: 0. Mathlib leaves: 0. No unit record changed: this technical descendant is not its unit's key statement.

## Attachments

None. Searched the read-only slopmaster2 project under `WeilConjectures/` for the exact blueprint tag/id and the concepts `hocolim`, `homotopy.?colimit`, `reindexing`, and `zigzag`. The reindexing/zigzag hits concern finite stalk products, duality triangle identities, and connected indexing categories; none states the item's model-category homotopy-colimit theorem. No `lean_audit` is present on the item. No upstream sorry declaration was treated as a finished proof.

## WANTED

WANTED: Daniel Dugger, *Combinatorial model categories have presentations*, Appendix A, Remark A.3, Proposition A.4 and Remark A.5, printed pp.198–199, for lem-coef-hocolim-reindexing-zigzags. Read online at https://www.sas.rochester.edu/mth/sites/doug-ravenel/otherpapers/dugger-comb.pdf; not downloaded or archived. The report and proof therefore explicitly identify the expansion as agent-written.

WANTED: Mark Hovey, *Model categories*, Theorem 1.2.10(iv), printed p.13, for the existing saturation input. Read online at https://ericmalm.net/ac/projects/symmetric-spectra/hovey--model-cats.pdf; not downloaded. The corresponding existing DAG node, rather than an uncited external assertion, is used in the item.

## What was wrong or missing

The item's statement was already correct, including the important requirement of weak equivalences after applying the value diagrams to both zigzags. It had no proof. Its existing source reference names the right Dugger result; no Stacks tag states this general model-category theorem. I did not introduce a fictitious Stacks source.

I supplied the missing homotopy-colimit calculus using the existing projective-model/coherent-colimit comparison and the existing coherent cocone calculus. Dugger uses cosimplicial resolutions, while this item fixes projective replacement. The proof does not silently equate the two constructions: it establishes the required four calculus properties for the stipulated projective construction from its already-cited coherent-colimit universal property. The finite-zigzag and inverse calculations follow Dugger's route. The ordinary homotopy-category passage is spelled out using edge generators and two-simplex relations and the full localization universal property; it is not assumed to be an ordinary colimit of the localized vertex diagram.

The ancestry historically refers to the older biduality unit. I read the chapter/unit records and the current main-20261015 ancestor proof under `sec-six-functors/sk-thm-sf-package/`. This split supplies a technical foundation under paragraph 2's finite mapping-complex adjunction and preserves the item's maintainer-owned chapter/unit and ancestry. It changes no unit route. No SGA source is used.

Generic tool use requested: `lem-cbc-enhanced-functor-cone-calculus`, from `sk-prop-sf-cbc`, for the coherent cocone universal property and pointwise equivalence criterion. The coefficient unit has no other statement of that foundation. This is declared in `split_report.tool_uses`, not installed as maintainer-owned `tool_uses`.

## What could not be finished

No mathematical part remains open in this split. No new statement-only obligations were necessary. The required server dry run is reported in the delivery tool output; READY is returned only after its actual OK result. No Lean was written, no compiler/Lake/build tool was run, and no push was requested.

## Not duplicates

No new nodes, hence no new/existing pairs. Whole-DAG searches included homotopy-colimit, saturation, model-localization, Dugger and Appendix A terminology. Whole-blueprint searches with `tools/blueprint_refs.py search` for `homotopy colimit`, `reindex` and `zigzag` found no alternate blueprint statement of this item: the sequential triangulated homotopy-colimit statements are different. The existing arbitrary-shape projective/coherent comparison, cone calculus and model saturation statements are reused directly. A dependency traversal found no path from any of these three inputs back to the item.

## Mathlib searches

All new recorded queries were actually run through `/home/ubuntu/weil-launcher-nt/msearch.py Q57 lem-coef-hocolim-reindexing-zigzags`, with the exact queries and responses preserved in `searches.jsonl` and appended to the node. LeanFinder was tried in two phrasings; Loogle, LeanSearch and whole-Mathlib grep were also run. No service in these queries was unavailable. Semantic hits for `HasColimit.isoOfEquivalence`/`isoOfNatIso` concern ordinary colimits with actual indexing equivalences or natural isomorphisms. I read `Mathlib/CategoryTheory/Limits/HasLimits.lean`, including the ordinary colimit comparison section around lines 725–765. The second phrasing found `Functor.leftDerivedNatTrans`/`leftDerivedNatIso`; I read `Mathlib/CategoryTheory/Functor/Derived/LeftDerived.lean:88–147`. These require already supplied derived-functor data and do not assert the item's diagramwise weak-equivalence zigzag criterion. Cell-attachment reindexing hits concern bijections of cell indexing sets. The grep for `hocolim|homotopyColimit|homotopy_colimit` returned no hits. The inherited searches were retained, not represented as new searches of Q57.

## Review by Q57

I reread delivery-errors B through E against the completed node, not merely the imported dependencies. For the item I read Dugger A.3(i)–(iv), the whole A.4 statement and proof, and A.5 online. The two value-diagram weak-equivalence hypotheses are precisely those of A.4/A.5. I also read Hovey 1.2.10(iv), which gives the final detection fact without restrictions on the map's endpoints. There are no new nodes needing separate sources or edge-case audits.

Step 1 cites the **statements** of `lem-coef-model-colimit-localization-comparison` and `def-cbc-enhanced-diagrams-cones`. I opened both files in full at the statement level: the first explicitly supplies projective structures for every small ordinary category, localization with the full functor-category universal property, and the colimit cocone including its coherent universal property. The second explicitly defines equivalence edges by inverse equations witnessed by two-simplices. These statements support the specified projective construction and its passage to the ordinary localization. The edge-path construction explains why maps into an ordinary nerve impose exactly identities/composition, including natural transformations, so the ordinary-localization identification is not an extra uncited model-category theorem. The universes are enlarged only for the ambient category, not for any indexing diagram.

Step 2 cites that same projective/coherent comparison, `lem-cbc-enhanced-functor-cone-calculus`, and `lem-coef-model-localization-detects-weak-equivalences`. I verified the cone node states both componentwise detection of transformation equivalences and the arbitrary-shape cocone mapping-space criterion, not just a fully-faithful Yoneda claim. The actual map is the colimit of the functorial replacement map. Its compatibility with the localized cocones follows from the augmentation's naturality. The coherent inverse of a diagram equivalence gives inverse maps on colimits by the cocone criterion, and the saturation node's statement then makes the actual map a weak equivalence. I did not assume the original diagram is projectively or objectwise cofibrant.

Step 3 again uses the projective/coherent comparison for the structural cocones and the cone node for maps out of their colimits. Restriction along each index functor gives the requisite whole coherent cocone; its universal lift determines a homotopy class. The composite, identity, and value-diagram naturality equalities are checked on these cocones, using uniqueness in the mapping-space equivalence. This avoids the false inference that agreement on individual components alone implies agreement of coherent cocones.

Step 4 uses the definitions node and the cone node. I checked the mixed-arrow formula for the functor on `J × [1]`: its two formulas coincide by ordinary naturality. The cocone's naturality on that prism supplies the coherent cocone homotopy, and the cited mapping-space criterion gives exactly the natural-transformation triangle. For this step the definitions citation excerpt also records the nerve/functor-category definitions. The invertibility test uses Step 2, not an uncited homotopy-finality theorem. No contractibility of indexing nerves replaces the required component hypotheses.

Step 5 is an elementary finite induction from Step 4. Each adjacent link is separately evaluated by the correct diagram, `V` on `I` and `Vg` on `J`; both possible orientations transfer invertibility. I checked the zero-link base, the one-link case, and reversed links. The item imposes no coherence between the two zigzags, and the proof introduces none.

Step 6 is elementary algebra with explicitly typed objects and three arrows. The first `g` comparison has diagram `Vgf`; the last has diagram `V`. I recomputed both composites: `v u` is the `fg` comparison for `Vg`, and `w v` is the `gf` comparison for `V`. The displayed left and right inverses of `v` have type `C → B` and agree by associativity. Thus invertibility of both adjacent composites suffices even though the outer `g` maps differ. I deliberately did not claim that the bare `f` comparison is an inverse with coherent triangle identities supplied by the input zigzags.

Step 7 cites the saturation node's exact iff for every actual morphism of a model category and every ordinary localization. The model axioms in its referenced definition are the same complete/cocomplete, two weak factorization systems, two-out-of-three and retract-closure axioms in the item's Reedy terminology. The localization was identified in Step 1, so the hypothesis matches exactly. This is also what ensures images of natural isomorphisms are weak equivalences; strict identities need no further result.

For small cases I checked: an empty indexing category (the existence of functors both ways forces the other to be empty, and the comparison is the identity on the initial colimit up to its prescribed homotopy class); terminal indexing categories with identity functors; constant diagrams and zero-length zigzags; indexing equivalences with natural-isomorphism links; and a single noninvertible indexing transformation whose value is a weak equivalence. Every step still applies without requiring fibrancy, properness or a simplicial enrichment on `M`. The generic cocone node permits arbitrary small shapes, so no hidden finite/Reedy-shape restriction is used. I checked all quote entries against the exact current node statements and all cited nodes for cycles. No statement dispute was found, and no statement was weakened.

## Second reading by Q57

Item statement checked against Dugger, Appendix A, Remark A.3(i)–(iv) and Proposition A.4 (printed p.198), its proof and Remark A.5 (p.199), opened online in this reading. Both value-diagram hypotheses agree; combinatoriality supports the stipulated projective model and adds no requirement on fibrancy, properness, or enrichment. Hovey Theorem 1.2.10(iv), p.13, confirms saturation for arbitrary endpoints. There is no Stacks tag for this abstract model-category result. The current blueprint ancestor paragraph 2 was opened and the technical ancestry retained.

- Step 1 checked against `lem-coef-model-colimit-localization-comparison` and `def-cbc-enhanced-diagrams-cones`; verdict: the coherent projective-colimit comparison and ordinary localization construction are stated and cited correctly.
- Step 2 checked against the projective comparison, `lem-cbc-enhanced-functor-cone-calculus`, and `lem-coef-model-localization-detects-weak-equivalences`; verdict: objectwise weak-equivalence invariance and saturation follow from the cited statements.
- Step 3 checked against the projective comparison and cone-calculus mapping-space criterion; verdict: restricted cocones give the reindexing map, composition, identity, and naturality in the value diagram.
- Step 4 checked against the enhanced-diagram definitions and cone-calculus node; verdict: the prism functor and both orientations of the natural-transformation triangle are typed and justified.
- Step 5 checked by finite induction, including zero-link and reversed links; verdict: both stipulated zigzags make their endpoint comparisons invertible under exactly the stated hypotheses.
- Step 6 checked by explicit typing of the three comparison maps and both inverse composites; verdict: invertibility of the two composites implies invertibility of the middle comparison without identifying the two `g` maps.
- Step 7 checked against the model-localization saturation statement; verdict: every actual representative is a weak equivalence, with natural-isomorphism and identity cases covered.
- No new nodes were introduced; consequently there are no new-node statements, sources, Mathlib leaves, or duplicate candidates to repair.

Changes made in this second reading:

- Expanded Step 1's prism/natural-transformation correspondence into its vertical-edge and naturality-square argument, to remove the compressed appeal to the same description (E5).
- Expanded Step 5's second zigzag into its own indexed induction with reverse links, to replace the instruction to do the same (E5).
- Recorded independent LeanFinder, Loogle, and whole-Mathlib grep queries and their actual responses. LeanFinder returned only cell-attachment reindexing; the other two returned no hits.
- Added this itemized audit and concrete edge-case test. The item statement, dependencies and citation quotes remain unchanged.

Additional small-case check: take `I = [1]`, `J = *`, let `g` select 0, and let `f` be unique. The transformation from the constant-0 functor to the identity evaluates to the sole arrow of `V`. With `V = (0 → C)` for an acyclic complex over a field, this arrow is a quasi-isomorphism and the conclusion identifies two zero objects in the derived category. With a nonacyclic `C`, the component hypothesis fails, as it should. Empty indices force both categories empty because functors exist both ways; zero-link zigzags and terminal indices reduce to identity comparisons.
