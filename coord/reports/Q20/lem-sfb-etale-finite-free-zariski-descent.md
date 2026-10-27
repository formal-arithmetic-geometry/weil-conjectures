# Worker report: lem-sfb-etale-finite-free-zariski-descent

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-etale-finite-free-zariski-descent.json: statement split into five proof steps; Mathlib verdict no match; statement unchanged.
- citations.json: eleven step/node entries containing verbatim statement quotations.
- report.md and searches.jsonl: this review and the actual Q20 Mathlib searches.

New nodes: 0. New Mathlib leaves: 0. No unit file is changed: this auxiliary node is not the key statement of its unit.

## Attachments

None. I searched the project source under lean/WeilConjectures for the blueprint id, finite local freeness, etale/free combinations and the relevant Modules and Sites directories. FiniteDescent.lean contains ordinary module pullback/open-locality and descent results; IsFiniteLocallyFreeOfDegreeOfEtaleCover.lean concerns scheme morphisms of a fixed degree. Neither states this small-etale/Zariski module comparison with all its clauses. Sorry declarations in the project are not attachments. The item has no recorded completed Lean declaration.

## WANTED

None. All source material used is present in literature/stacks-project.

## Findings and corrections

The item was unsplit, with an empty proof. Its statement agrees with descent.tex Tag 05VG (lemma-equivalence-quasi-coherent-properties), finite locally free clause, together with 03DX(2) and 05B2 (lemma-finite-locally-free-descends). It does not assert that infinite-rank local freeness descends. I retained the whole statement and every existing Mathlib search, and appended the four actual Q20 queries. There was no earlier sandbox split or report, and no repair note for this item.

The imported ancestry has blueprint.from.node null and a long historical created-item chain. tools/blueprint_refs.py ancestor confirms the null ancestor. I retained that provenance and its already specified from.place. I read the current latest blueprint sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md and its sk-thm-sf-ctf-stability-direct-images.proof.md. The current direct-image proof does not contain the old alteration subargument; the module lemma remains a generic prerequisite below the historical conormal splitting node. No chapter or unit route is changed. Whole-blueprint searches for finite locally free, 05B2, 05VG and Zariski etale quasi-coherent found no blueprint statement of this comparison. The finite-locally-free-module definition that appears in the search is constant-rank and is not used to silently impose constant rank here.

## Unfinished work

None at stage 1. The item is a one-level split into existing statements; no Lean code or compilation is part of this delivery.

## Not duplicates

No new nodes were created. Whole-DAG searches for 05VG, 05B2 and the quasi-coherent/descent terminology found the existing general comparison, its normalized extension/restriction interface and lem-pc-fpqc-descent. These are reused. The scheme-morphism degree-descent result is about a different kind of object; the invertible-comparison result is only rank one. No auxiliary statement repeats this item or one of its clauses.

## Review by Q20

I read the item against the actual text of descent.tex at lemma-equivalence-quasi-coherent-properties (05VG), proposition-equivalence-quasi-coherent (03DX) and lemma-finite-locally-free-descends (05B2). In 05VG the global properties are immediate and local properties are tested on members of a covering before using ordinary fpqc descent. In 05B2 the module is quasi-coherent on any scheme; neither a constant rank nor a Noetherian base is assumed. Its proof descends flatness and finite presentation and uses the finite-projective criterion. I also read that criterion in algebra.tex lemma-finite-projective and its scheme version properties.tex lemma-finite-locally-free to check that no finite-type-only substitute or Noetherian hypothesis was being used. The split cites the already existing general descent node rather than creating a node restating 05B2.

Step 1 uses the statement of lem-trf-scheme-zariski-etale-quasi-coherent-equivalence: it expressly gives the inverse by restriction and the canonical comparison for every scheme morphism. It does not merely assert an abstract equivalence. lem-weil-pbc-module-pullback-quasi-coherent supplies quasi-coherence of each ordinary pullback, which is required before using the comparison. Thus the hypothesis on the tensor pullback of F really applies to the extension of the ordinary pullback of G.

Step 2 uses the statement of lem-trf-etale-extension-free-presentations-hom: its etale restriction formula identifies the locally framed object with extension of the further ordinary pullback, and its identity unit on open sections recovers that ordinary module. The finite direct sum is recovered coordinatewise on every Zariski open, with the same restriction maps; this elementary argument is written out, not taken from a definition node. The module-pullback-quasi-coherent statement applies a second time. def-pc-module-pullback explicitly includes the composition isomorphism, so the free module is indeed the pullback along the composite f_ab. No assertion of Zariski local freeness is assumed while recovering these frames.

Step 3 uses def-weil-pbc-etale-site for exactly its etale, jointly surjective covering convention, and lem-weil-pbc-etale-composition-cancellation for composition. Joint surjectivity of the composite family is proved by two point lifts. lem-weil-pbc-fpqc-finer-than-etale explicitly turns any such covering into an fpqc covering, including the affine finite-refinement condition; merely knowing flatness would not have sufficed. There is no global finite-subcover assertion.

Step 4 uses clause (2) of lem-pc-fpqc-descent, whose statement expressly reflects finite local freeness. I checked the ordinary quasi-coherent hypothesis from Step 1, the fpqc hypothesis from Step 3 and finite freeness of every ordinary pullback from Step 2. I use the unprescribed-rank property, not the additional version with a specified common r: the ranks n_ab are never assumed equal. This is the 05B2 property in the node's cited Descent Section 35.7. No descent datum needs to be chosen because all these modules are pullbacks of G itself.

Step 5 uses the structure-module, colimit and etale restriction clauses of lem-trf-etale-extension-free-presentations-hom. It thereby extends each finite free Zariski frame to an actual finite free etale frame. lem-weil-pbc-etale-composition-cancellation explicitly includes open immersions being etale. The argument proves the converse without applying the result being split.

I checked delivery-errors B through E with these files open. There are no new nodes requiring separate notion or duplication checks; the item's notions remain defined inline or by its existing statement dependencies. All non-elementary steps name their input statements, the proof dependency list is exactly their union, and citations.json copies the actual statements, never their proofs. Every step is shorter than 2000 characters. The off-unit statements are generic module/site/covering tools and are declared in split_report.tool_uses; they do not replace any six-functor unit step. The proof uses no SGA source.

The small cases checked are the empty scheme (including an empty covering), rank zero, disconnected schemes with different ranks on components, an infinite cover and a non-Noetherian affine base. The proof is pointwise local, never fixes a rank, and never uses finite presentation before it is supplied by finite free frames and the cited descent theorem. In particular the zero and varying-rank cases would expose an accidental constant-rank assumption. No statement dispute was found.

The Mathlib searches were run with msearch.py, with their exact tool/query strings in the item and searches.jsonl. LeanFinder returned site finite-presentation data and finite-type predicates; LeanSearch with a second phrasing returned ring-module localization, rank-at-stalk and scheme-morphism descent statements. I inspected the Quasicoherent.lean finite-presentation definitions and the indicated localization/local-ring/free-locus declarations: they neither compare the two module sites nor give this scheme-sheaf conclusion by a one-line specialization. Loogle and the targeted grep returned no matches. No result was recorded as an attachment or Mathlib leaf.
