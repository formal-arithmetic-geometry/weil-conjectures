## Files written

- dag/nodes/sec-six-functors/lem-weil-mate-iso-along-equivalences.json: statement, split into six elementary steps; not a Mathlib leaf.
- citations.json: empty list, since the argument cites no nodes.

No new nodes. The node's mathematical assertion is unchanged; the parenthetical pending-proof sketch was moved into actual proof steps.

## Attachments

None. Searched WeilConjectures for the blueprint tag, mateEquiv and mate/iso/equivalence terminology. CategoryTheory.Adjunction.isIso_mateEquiv_app_of_isIso, WeilConjectures/CategoryTheory/Adjunction/ProjectionMapMate.lean:131, assumes adjoints of both side functors, hence does not state the item: a fully faithful G' need not have a right adjoint. CategoryTheory.isIso_map_mateEquiv_app_of_isIso in WeilConjectures/Mathlib/CategoryTheory/Adjunction/Mates.lean proves invertibility only after application of a side right adjoint and also assumes that adjoint exists. Neither is an attachment.

## Wanted literature

WANTED: Kelly–Street, Review of the elements of 2-categories, LNM 420, section 2.2, for lem-weil-mate-iso-along-equivalences. It is not in literature/. The abstract argument is accordingly marked agent-written, not attributed to Deligne or to an unread reference.

## Findings and corrections

Deligne's cited passages motivate transport of structure and do not state this abstract categorical assertion. The source field already says this and was kept. The old statement had a pending-proof sketch, no actual proof, and incomplete grep-only searches. The new proof expands the sketch's central naturality calculation and replaces its invocation of Yoneda by an explicit two-sided inverse argument. No added hypotheses, coefficients, or triangulated structure are required. No source or statement dispute was found.

Mathlib queries were run through msearch.py and recorded from searches.jsonl. Both semantic phrasings returned mateEquiv and its component formulas; Loogle returned mateEquiv, iterated mates and conjugation compatibility. Reading Mathlib/CategoryTheory/Adjunction/Mates.lean confirmed that mateEquiv is a correspondence, not an invertibility theorem. Its documentation explicitly warns that an arbitrary mate of an isomorphism need not be invertible. Conjugation specializes to identity side functors; iterated mates require additional side adjoints. LeanSearch returned HTTP Internal Server Error and is recorded unavailable. The two grep queries were also run; no exact Mathlib match was found.

## Not duplicates

No new node is proposed. Whole-blueprint searches for mate, fully faithful and equivalence, and DAG searches for mate, adjunction and Yoneda were read. The existing lem-trf-adjoint-mate concerns two adjunctions between the same triangulated categories with identity side functors; it is not this general four-category result. It is not cited because its statement would not justify the Hom calculation under the present hypotheses.

## Review by NN

I read Deligne, Weil II (1.1.7), printed p. 151, and (1.1.14), printed p. 153, from the PDF: the first discusses the fibre action by transport, the latter the cohomological Frobenius comparison, including compact supports. I also read the ancestor def-weil-global-geometric-frobenius in the master blueprint and its DAG record, the unit sk-prop-sf-rf-shriek-preservation, and the chapter record. This auxiliary categorical argument supplies the exchange-map invertibility used in the ancestor's two first arrows; it does not replace the unit's preservation proof.

Step 1 uses only the definitions of fully faithful functors, adjunction and natural isomorphism supplied in the statement: each Hom arrow is a bijection, including precomposition by theta. Step 2 writes the unit-counit form of the adjunction bijections rather than citing an unspecified correspondence. Step 3 substitutes the naturality equations at t and G(t), with the source and target of each composite checked; this proves that the chosen Hom bijection is exactly postcomposition with alpha, not merely an unrelated abstract bijection. Step 4 uses essential surjectivity only for G, and explicitly conjugates Hom maps by an isomorphism Gc to x. Step 5 uses surjectivity at the target b and injectivity at the source a to prove both inverse equations. Step 6 derives inverse naturality by multiplying the original naturality equation by those inverses. All six steps are a few lines of definitions, compositions and the displayed identities; no non-elementary theorem, source tag, cited node, Yoneda lemma or hidden isomorphism-reflection theorem is used. Thus C1 and C4 have no omitted or mismatched node citations, and citations.json is empty by design.

I checked the direction theta:L'G to G'L and the component alpha:GRd to R'G'd in every calculation. In particular G' is used only for its Hom bijection, never for essential surjectivity or existence of an adjoint. The terminal-category case gives identity maps; with identity side functors the proof reduces to uniqueness of right adjoints. Empty categories cause no exceptional case: where a d exists, Rd and GRd exist, so essential surjectivity supplies the test objects used; where no d exists the component assertion is vacuous. A proper full subcategory for G' is permitted and the argument still uses only its Hom sets. No new statements require small-case testing or separate Stacks tags.

I checked B1–B10: no newly created unsplit node, hollow definition, duplicate or relabelled clause. For C1–C8 and D1–D5 the item itself carries the Hom and inverse calculations, with no cycle or off-unit proof dependency. For E1–E7 no extra adjoint, category-size, scheme or coefficient hypotheses enter. The inherited check_dag.py reports unrelated baseline findings; the authorized delivery preflight compares against that baseline. The dry run is the validation of the sandbox overlay, not the unchanged read-only node.

## Unfinished work

None in this stage-1 split. A fresh second reader must review and deliver; this worker does not push.


## Second reading by NN

- Statement: checked all four categories, both adjunctions, the direction of theta and the specified unit–theta–counit mate against the original item; the mathematical assertion is unchanged and well typed. Read Deligne Weil II (1.1.7), printed pp. 150–151, and (1.1.14), printed p. 153, and the master blueprint def-weil-global-geometric-frobenius: these motivate transport but do not state the categorical lemma; the agent-written provenance is accurate. There is no Stacks tag in this item's source to compare.
- Step 1: checked the five Hom bijections against the definitions of full faithfulness, the two adjunctions and invertibility of theta; PASS, elementary, no extra hypothesis on G'.
- Step 2: checked both transpose formulas and their inverse formulas against the units and counits of the given adjunctions; PASS, elementary. Each displayed arrow has the required source and target.
- Step 3: checked the naturality equations at t:c to Rd and G(t), then substituted into Step 2; PASS, elementary. The bijection is postcomposition by this alpha, not just a bijection of abstract sets.
- Step 4: checked essential surjectivity of G supplies u:Gc to x and both inverse precomposition maps; PASS, elementary. Associativity proves the square commutes, so no uncited Yoneda theorem is used.
- Step 5: checked surjectivity at b supplies a right inverse and injectivity at a proves the left inverse; PASS, elementary, including a or b a zero object.
- Step 6: checked counit naturality at f, theta naturality at R(f), and unit naturality at GR(f); REPAIRED the abbreviated whiskering argument with these three identities and the full composite calculation. Multiplication by beta_e and beta_d proves inverse naturality; PASS, elementary.
- New nodes: none. B1–B7 and the duplicate/special-case/restatement audit introduce no further items or Mathlib leaves; citations.json remains the correct empty list because every step is an explicit calculation from the statement's data.

Small cases: identity side functors reduce the calculation to the ordinary right-adjoint comparison; terminal categories give identities; for empty C or C', the existence of d forces Rd and GRd to exist, otherwise the component assertion is vacuous. In additive examples with d=0 the same Hom bijections apply, without requiring L or R to preserve zero objects as an extra assumption. G' may embed a proper full subcategory: its essential surjectivity is never used. Thus no statement dispute or hidden hypothesis was found.

Independent searches: ran msearch.py leanfinder with “Fully faithful functors and equivalences reflect invertibility of right adjoint comparison transformations” (eight hits, on reflective/fully faithful adjunctions and localization; none states the four-category comparison); grep “FullyFaithful.*mate|mate.*FullyFaithful|isIso.*mate|mate.*isIso” (zero hits); and loogle '"mateEquiv", "Iso"' (zero hits). Actual outputs are appended in searches.jsonl. Read Mathlib/CategoryTheory/Adjunction/Mates.lean:84–126: mateEquiv and its component formulas give the correspondence, not this invertibility claim. Re-read source ProjectionMapMate.lean:124–134 and source Mathlib/CategoryTheory/Adjunction/Mates.lean:300–330: both candidate lemmas assume side right adjoints, absent here. Read lem-trf-adjoint-mate: it assumes identical side categories and exact triangulated functors, so it cannot replace this item. No new nodes need Mathlib match records.

Changes: expanded only Step 6 and noted that expansion in split_report.summary; preserved the correct statement, Steps 1–5, first-worker sections, source attribution and empty citations. This resolves E5's demand for the argument behind “whiskering preserves naturality”. No Lean files, compilers, live project files or launcher code were changed.

Whole-blueprint duplicate searches were independently rerun with tools/blueprint_refs.py search for mate (23 hits) and fully faithful (10 hits); none supplies the general four-category statement. Validation: deliver.py NN lem-weil-mate-iso-along-equivalences --no-push printed OK, preflight passed (ef2b0ed1c4).
