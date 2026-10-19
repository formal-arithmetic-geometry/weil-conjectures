# Stage-1 worker report: lem-coef-space-kan-fibration-fiber-criterion

Group Q13, 2026-10-17. The delivery contains one existing node, no new nodes and no Mathlib leaves. The item statement is unchanged.

## Files written

- `dag/nodes/sec-six-functors/lem-coef-space-kan-fibration-fiber-criterion.json`: statement, now split into six steps. No exact Mathlib match found.
- `citations.json`: one verbatim statement excerpt for each of the ten step/node citations.
- `report.md`: this report. `searches.jsonl` is the actual search-command log.

## Attachments

None. I searched the read-only slopmaster2 `WeilConjectures/` for the item id, Kan/fibration/contractible combinations, and `KanComplex`, `WeakEquivalence`, `IsContractible`, `KanFibration` and `kanFibration`. No declaration states this theorem. No master sorry declaration was treated as a finished proof.

## WANTED

WANTED: archival copy of Kerodon Proposition 3.3.7.6, tag [00ZP](https://kerodon.net/tag/00ZP), for lem-coef-space-kan-fibration-fiber-criterion. I read the online statement and proof; no matching Stacks tag states this result.

WANTED: archival copy of Hovey, *Model Categories*, Lemma 2.4.16, the discussion of change of basepoint preceding Definition 2.4.3 and in Lemma 2.4.17, Proposition 2.4.18, Lemma 3.2.4 and Corollary 3.6.2, for the item's realization/Serre-sequence proof and its already-existing tools. I read the online [Hovey PDF](https://www.sas.rochester.edu/mth/sites/doug-ravenel/otherpapers/hovey-model-cats.pdf). Its archive is absent from literature/. I downloaded nothing. Accordingly the proof is marked agent-written: Kerodon verifies the statement, but the six-step argument is my expansion using existing Hovey-based DAG statements, not a transcription of Kerodon's simplicial proof.

## Corrections and provenance

The original source conflated two Kerodon locations: 0328 is Remark 3.4.0.6 about homotopy fibers, whereas this item concerns strict fibers of a Kan fibration and is the equivalence (3) with (4) in Proposition 3.3.7.6, tag 00ZP. I recorded the accurate location in proof_origin and here; the second reading corrected the stale source metadata. There is no statement dispute, additional hypothesis or weakening.

I read the chapter and `sk-prop-sf-biduality-general` unit records, the historical master ancestor's second proof paragraph, and the main-20261015 ancestor file. The current snapshot separates the integral adjunction statement from `sec-six-functors/sk-thm-sf-package/prop-coef-integral-exceptional-adjoint.proof.md`; I read that proof file and verified that its second paragraph retains the same derived-adjunction calculation. I preserved the historical `blueprint.from` chain and explained that provenance in `split_report.blueprint`. The three theorem tools used here have the same unit as the item; the remaining dependency is a definition. No off-unit tool declaration or unit realization edit is needed.

The original item had no proof. The split now supplies the actual component and homotopy-group arguments; it does not cite a new copy of its conclusion. Crucially, an exact sequence of pointed sets only controls a distinguished fiber on components unless one also uses the orbit/stabilizer information. Step 3 uses both clauses explicitly. Step 2 spells out why vertex basepoints suffice, rather than dropping the definition's requirement at every realization basepoint.

## Reuse and duplicate search

Before considering new nodes, I searched the entire DAG for Kan fibrations, contractible fibers, realization, homotopy exact sequences and source tags, and searched the imported blueprint with `blueprint_refs.py search` for `Kan fibration`, `homotopy equivalence` and `contractible`; `ancestor` returns prop-coef-integral-exceptional-adjoint. No imported blueprint node states this criterion in another form; `same_as` remains an empty list.

The already-existing `lem-cbc-kan-fibration-fiber-criterion` contains the present assertion and extra boundary-lifting and mapping-path clauses, but is unsplit. I did not create another criterion node or edit that existing node. Instead I reused the strictly foundational existing tools `lem-coef-realization-finite-limits`, `lem-coef-kan-realization-serre` and `lem-coef-serre-homotopy-exact-sequence` to give an independent detailed split of this assigned item. The item remains available to the parent that already cites it. The more general cbc node is a possible later merge candidate for maintenance; a worker has no authority to merge or edit it. No new-node duplicate pairs arise in this delivery.

## Mathlib searches

All recorded searches were run through the required msearch.py command and copied from its JSONL log, including their exact query strings. I tried the weak-equivalence/vertex-fiber formulation and then the trivial-fibration/contractible-fiber formulation. LeanFinder and LeanSearch returned generic homotopical category and horn-lifting facts; two grep formulations found no fiber criterion. A further grep returned the generic trivial-fibration predicate, which I opened at `Mathlib/AlgebraicTopology/ModelCategory/CategoryWithCofibrations.lean:108-124`. I also read the generating horns and fibration predicates in `Mathlib/AlgebraicTopology/SimplicialSet/CategoryWithFibrations.lean:38-55,85-105`. These assert a lifting condition or define trivial fibrations by already assuming a weak equivalence; they do not prove the fiber criterion and cannot specialize to it in one line.

On completing this earlier sandbox I reran six searches: LeanFinder with both formulations, LeanSearch, the successful Loogle name-substring query, and two grep patterns. The JSON records now reproduce those latest actual log entries. The historical invalid `SSet.fibration` query is not included in the absence evidence. The services were available; no unrun query is recorded.

## Unfinished work

None within this item's stage-1 scope. The three cited theorem tools remain existing DAG items with their own statuses; this delivery does not claim they are proved in Lean. The source archives are wanted as described above. The validation command is `python3 /home/ubuntu/weil-launcher-nt/deliver.py Q13 lem-coef-space-kan-fibration-fiber-criterion --no-push`; the worker reports READY only when it prints OK. No push is authorized for this worker; the accepted sandbox goes to a second reader.

## Review by Q13

I checked delivery-errors B through E with the actual node statements and sources open. The item agrees hypothesis by hypothesis with the Kan-fibration strict-fiber equivalence of Kerodon 00ZP: its Kan total space and base are an allowed restriction of that proposition, the horn convention includes both outer horns and positive dimension only, and weak contractibility includes nonemptiness. I read the defining statement of def-cbc-enhanced-diagrams-cones, its realization and cubical homotopy conventions, and Scholze Lecture II pp. 13–15 for the underlying simplicial/space conventions. There are no new statements, unsplit proof sketches, unintroduced objects or new Mathlib leaves to audit under B1–B8.

Step 1 uses the all-horn realization theorem from lem-coef-kan-realization-serre and the actual pullback homeomorphism in lem-coef-realization-finite-limits. I checked Hovey Corollary 3.6.2 and Lemma 3.2.4 online. The citation is specifically to k-space pullbacks, not an unsupported claim about ordinary products of arbitrary topological spaces. Horn filling of the simplicial fiber is written out by lifting the constant bottom simplex; it is not inferred from a definition node as an unstated theorem. The same step handles the empty base directly.

Step 2 is elementary and cites only the definitions it uses. Its formula inserts a path in a radial collar around a smaller cube; reversing the path, canceling the out-and-back excursion and rescaling the inner cube gives inverse maps on homotopy classes. Because all formulas commute with continuous postcomposition, bijectivity at vertex basepoints implies bijectivity everywhere. Only this bijection and naturality are needed, so the argument does not assume a separate multiplicative compatibility theorem about basepoint transport. Straight barycentric paths show that every realization component contains a vertex. These explicit constructions avoid a hidden basepoint-change black box.

Step 3 takes exactly the path-lifting and orbit/stabilizer clauses from lem-coef-serre-homotopy-exact-sequence, whose statement I read in full. Surjectivity on components gives a point that can be lifted along a path to the specified vertex. Its fiber is therefore nonempty before a basepoint is chosen. Bijectivity on total-space components gives one orbit, and surjectivity on fundamental groups makes the stabilizer of the chosen fiber component the whole loop group. Thus that orbit, and hence the entire fiber-component set, is a singleton. No connectedness hypothesis on E or Q was introduced.

Step 4 uses the five consecutive group terms in that same cited exact sequence. The preceding map is surjective and the following map injective, so the intermediate fiber group has both injective zero-image inclusion and must vanish. This also works for pi_1, without commutativity. The definition node then gives weak contractibility, after the explicitly justified change of basepoint from step 2.

Step 5 again uses the exact orbit-set statement, now applied to a singleton fiber-component set. It proves both existence and uniqueness of a total-space component over each base component. Step 6 uses ordinary group exactness in degrees at least two and explicitly uses pointed-set exactness for surjectivity on pi_1; vanishing pi_1 of the fiber supplies injectivity. The definition of weak equivalence requires all basepoints, which step 2 supplies. Every non-elementary inference is therefore covered by a cited theorem statement, not just its proof or its name; citations.json contains verbatim excerpts.

For E1–E6 I checked small cases: E=Q=empty gives a vacuous fiber condition and an equivalence; E empty and Q nonempty gives an empty fiber and fails both sides; a disjoint union of nonempty contractible components over a discrete base satisfies the criterion component by component; a two-point fiber over a point fails the pi_0 argument; a connected fiber with a nonzero higher group over a point fails the positive-degree argument. The proof permits any number of base components and never identifies homotopy fibers with strict fibers without the Kan-fibration realization theorem. There is no choice of data from a sorry existence assertion. I introduced no SGA reference and changed no target, coefficient category, existing dependency node or unit metadata.

## Source error

The imported source field named Kerodon tag 0328, but tag 0328 is Remark 3.4.0.6 on homotopy fibers. The stated strict-fiber equivalence is Proposition 3.3.7.6 at tag 00ZP; I verified its four equivalent conditions (trivial Kan fibration, homotopy equivalence, weak homotopy equivalence, and contractible vertex fibers) directly and corrected the node's source.document and source.place to 00ZP. The proof-origin note already records that the six-step realization/Serre proof is agent-written, while 00ZP confirms the statement.

## Earlier second reading (a previous round; superseded)

- Item statement: checked against Kerodon Proposition 3.3.7.6 (00ZP), including the Kan-fibration hypothesis, weak-equivalence clause, and every vertex strict fiber; verdict: agrees after correcting the source tag from 0328 to 00ZP.
- Step 1: checked the fiber horn-lifting argument against def-cbc-enhanced-diagrams-cones, realization-to-Serre in lem-coef-kan-realization-serre, and the realized pullback in lem-coef-realization-finite-limits; verdict: all hypotheses and the empty-base case are explicit.
- Step 2: checked the barycentric vertex paths and cubical collar basepoint-change construction against the realization and homotopy definitions in def-cbc-enhanced-diagrams-cones; verdict: the formulas give inverse basepoint bijections and commute with postcomposition, so vertex checks extend to all points.
- Step 3: checked the component orbit and stabilizer argument against the full statement of lem-coef-serre-homotopy-exact-sequence; verdict: surjectivity on components supplies a fiber point, and the orbit/stabilizer clauses prove the whole fiber is connected.
- Step 4: checked the positive-degree kernel/image chase against the five consecutive terms and exactness asserted by lem-coef-serre-homotopy-exact-sequence; verdict: it proves every positive homotopy group of the fiber vanishes, including the nonabelian degree-one case.
- Step 5: checked the converse component argument against the fiber-component orbit formula in lem-coef-serre-homotopy-exact-sequence; verdict: singleton fiber components give exactly one total-space component over each base component.
- Step 6: checked injectivity and surjectivity in all positive degrees, including the pointed-set degree-one tail, against lem-coef-serre-homotopy-exact-sequence and the weak-equivalence definition in def-cbc-enhanced-diagrams-cones; verdict: the converse is complete and checks every basepoint via step 2.
- New nodes: none; no B1-B7 audit or duplicate removal is needed. Existing dependencies were searched by identifier and key phrases, and the recorded Mathlib searches found only primitive horn/fibration declarations, not this criterion.
- Small cases: checked empty base and total space, empty total space over a nonempty base, discrete bases, a two-point fiber, and a connected fiber with nonzero higher homotopy; verdict: the statement and proof handle the edge cases correctly.

Completion of the earlier sandbox: I independently rechecked the proof and all ten citation excerpts, reran the six recorded Mathlib searches, and corrected the provenance note. The earlier report incorrectly said the current ancestor had no proof: its proof is in a separate `.proof.md` file. I read it and updated `blueprint.from.place` and `split_report.blueprint` to the actual second-paragraph derived-adjunction calculation. No statement, proof step, dependency or node count required mathematical repair. The accepted sandbox is left for the next reader; I made no push.


## Second reading by Q13

Independent reading on 2026-10-17, with the item, all four dependency statements, the current blueprint proof file, Kerodon 00ZP and 0328, and the cited Hovey passages open. The statement matches Kerodon 00ZP (3) iff (4) under the item's Kan-complex hypotheses: all positive-dimensional horns, strict fibers over every vertex, and weak contractibility including nonemptiness. The corrected source tag is accurate; no statement dispute remains. No Stacks tag is claimed for these topological results.

- Step 1: checked the horn lift with constant bottom simplex against the definition, the realization fibration against lem-coef-kan-realization-serre and Hovey Corollary 3.6.2, and the fiber homeomorphism against lem-coef-realization-finite-limits and Hovey Lemma 3.2.4; PASS, including the empty-base case and k-space fiber topology.
- Step 2: checked the collar formula against the cubical homotopy definition (the defining unit cube is affinely homeomorphic to the centered cube used here); PASS: the formulas match at radius one-half, reverse-path collars cancel relative to the boundary, and postcomposition preserves the formula. Straight simplex paths supply vertex representatives of every component. This is an explicit elementary argument.
- Step 3: checked against every path-lifting, orbit and stabilizer clause of lem-coef-serre-homotopy-exact-sequence; PASS: component surjectivity first supplies a fiber point, and component bijectivity plus fundamental-group surjectivity forces exactly one fiber component. The existing node explicitly states the orbit formula; it is not being inferred merely from pointed-set exactness in Hovey Lemma 2.4.16.
- Step 4: checked the five displayed consecutive terms against that same node; PASS: surjectivity kills the connecting homomorphism, injectivity kills the inclusion's image, and group exactness proves vanishing even in degree one. Step 2 covers every realization basepoint.
- Step 5: checked the converse against that node's orbit-set clause; PASS: a nonempty singleton fiber-component set gives exactly one total-space component over each base component, with no connectedness assumption on the base.
- Step 6: checked against that node's group and pointed-set exactness and the definition of weak equivalence; PASS: zero fiber groups give injectivity in all positive degrees, zero preceding fiber groups give surjectivity in degrees at least two, and the singleton component set gives surjectivity in degree one. Step 2 supplies arbitrary basepoints.
- New nodes: none; PASS. Searches of current DAG statements for 00ZP, Kan-fibration criteria, Serre fibrations and orbit sets confirm the four reused dependencies; the existing broader cbc criterion remains unsplit and is not used circularly. There is no new elementary, duplicate, or relabelled node to remove, and no new B1-B7 or Mathlib-leaf record to repair.
- Citation audit: PASS, all ten step/node pairs are present exactly once, and each quote is a verbatim substring of the current cited statement. No citation changes are needed.
- Edge cases: PASS for empty source and base, empty source over a point, discrete bases with singleton fibers, two points over a point, and a noncontractible Kan complex over a point. Nonempty fibers are obtained before choosing their basepoints; disconnected bases are allowed throughout.

Changes in this reading: appended this independent audit and added two actual search records using a new semantic phrasing ("weakly contractible point preimages") and a Mathlib-wide fiber/weak-equivalence/contractibility grep. LeanFinder returned abstract fibration facts that already assume weak equivalence, and grep returned zero hits. I read CategoryWithCofibrations.lean:108-124 to confirm the former are definitions, not this theorem. The six proof steps, statement, existing citation quotes and accurate source metadata needed no mathematical repair. The first worker's Review by Q13 and all earlier sections are preserved. The new records are copied verbatim from searches.jsonl, not reconstructed search results.
