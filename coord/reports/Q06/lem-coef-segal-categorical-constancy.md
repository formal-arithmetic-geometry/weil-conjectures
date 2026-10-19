# Worker report

Item: lem-coef-segal-categorical-constancy. Group: Q06. Date: 2026-10-17.
Only stage 1 was performed. All writes are in this item's sandbox; no Lean was written or compiled, no direct git command was run, and nothing was pushed.

## Files written

- dag/nodes/sec-six-functors/lem-coef-segal-categorical-constancy.json: item, split into seven steps; no Mathlib match.
- dag/nodes/sec-six-functors/lem-coef-bisimplicial-reedy-division-calculus.json: statement, unsplit; no Mathlib match.
- dag/nodes/sec-six-functors/lem-coef-segal-inner-horn-restriction.json: statement, unsplit; no Mathlib match.
- dag/nodes/sec-six-functors/lem-coef-complete-segal-walking-isomorphism.json: statement, unsplit; no Mathlib match.
- dag/nodes/sec-six-functors/lem-coef-joyal-walking-isomorphism-fibration-test.json: statement, unsplit; no Mathlib match.
- dag/nodes/sec-six-functors/lem-coef-model-fibrant-fibration-cofibration-test.json: statement, unsplit; no Mathlib match.
- citations.json: one entry for every node used by each numbered step, quoting that node's exact statement.
- report.md; research.py, write_split.py, search_jobs.json and search-*.txt: sandbox-only report and reproducible research/writing records. searches.jsonl is the search tool's own record.

There are five new nodes and zero Mathlib leaves. Every new node contains a statement only, with empty proof and proof_deps and null proof_origin. The item remains in its original chapter/unit; it is not the unit's key node and no unit file was changed.

## Attachments

None. Searches of WeilConjectures/ in /home/ubuntu/weil-src-slopmaster2 by the exact item id, complete Segal, Rezk, Joyal-Tierney, categorical constancy, bisimplicial, walking-isomorphism and lifting terminology found no declaration stating the item or the five new facts. The upstream master CategoryTheory source was also searched read-only; its declarations would not have counted as finished proofs. No attachment is claimed from Mathlib or from a partial theorem.

## Sources wanted

WANTED: Joyal and Tierney, Quasi-categories vs Segal spaces, arXiv math/0607820, Section 2 (Propositions 2.1, 2.5, 2.8, Theorem 2.6 and Proposition 2.10), Proposition 3.4, Proposition 3.10, Lemmas 4.2-4.3, Proposition 4.4, Theorem 4.5, Proposition 1.13 Corollary 7.11 and Lemma 7.14, for the item and its five new nodes. Read directly at https://arxiv.org/html/math/0607820; no local archive was found in literature/ and none was downloaded.

WANTED: Rezk, A model for the homotopy theory of homotopy theory, arXiv math/9811037, Theorem 6.2 and Proposition 6.4, for lem-coef-complete-segal-walking-isomorphism. Read directly at https://arxiv.org/html/math/9811037; archive absent.

No Stacks tag states these simplicial-homotopy results. Assigning an algebraic-geometric tag to them would be inaccurate. No SGA source is used. Because the actual sources are online rather than archived under literature/, the item's proof_origin is by agent, identifying the exact online argument reconstructed, as required by the standing brief.

## Corrections and source/route audit

The item's proposition is correct. Its JSON contained doubled TeX escapes; these were changed to single TeX escapes without changing any mathematical hypothesis or conclusion. In particular, the rows are X_{bullet,q}, the map is contravariant in the unique [q] to [0], and the last clause is for arbitrary bisimplicial sets. There is no statement dispute.

I read the original chapter record sec-six-functors and unit sk-prop-sf-biduality-general and followed the nearest blueprint ancestor prop-coef-integral-exceptional-adjoint, proof paragraph 2 (the enriched mapping-complex adjunction). This technical comparison lies below that unit and makes no change to its geometric route or its statement. I also inspected the ancestor's source/proof and the intermediate complete-Segal/quasicategory comparison. All five children inherit the item's chapter and unit and carry the exact ancestor/via chain printed by blueprint_refs.py ancestor. No new blueprint unit is needed.

A potential circular source dependency was removed before writing: lem-coef-rezk-local-model includes the mixed Joyal/Kan box-product theorem (Joyal-Tierney Proposition 4.6), but that proposition's source proof uses Theorem 4.5, the comparison being split here. The item uses only the Rezk model's existence, cofibrations and mapping-space tests, never that box-product clause. Instead its steps prove Lemma 4.3's relative lifting argument and Theorem 4.5's identity Quillen argument. The later first-row Quillen equivalence, Theorem 4.11, is not used.

All proof uses stay in the inherited unit. The generic Reedy and model-adjunction nodes already exist in that unit. No off-unit proof tool is introduced.

## Searches and candidate readings

For the item and each new node I ran leanfinder, loogle, grep and leansearch through /home/ubuntu/weil-launcher-nt/msearch.py, then ran a second differently phrased leanfinder query. The literal queries and returned output are in each node's mathlib_searches and search-*.txt; searches.jsonl was written by msearch.py. All thirty requests completed successfully; no unavailable service was called a negative match.

I read the returned candidates, including Mathlib/AlgebraicTopology/Reedy/Basic.lean lines 14-24 and its ReedyStructure definition, Mathlib/AlgebraicTopology/Quasicategory/StrictSegal.lean (quasicategory and quasicategory'), Mathlib/AlgebraicTopology/SimplicialSet/CoherentIso.lean (WalkingIso, its ordinary functor/iso correspondence, and coherentIso), and the generic model-category axioms and weak factorization-system instances in Mathlib/AlgebraicTopology/ModelCategory/Basic.lean. Reedy/Basic explicitly lists construction of the Reedy model structure as TODO. StrictSegal concerns strict Segal simplicial sets, whereas the new restriction theorem concerns homotopy Segal spaces. CoherentIso constructs the walking groupoid's nerve but supplies neither the complete-Segal-space comparison nor the Joyal fibration characterization. The generic model hits test against all fibrations; they do not give the converse with tests restricted to fibrations between fibrant objects. The closest candidates and these distinctions are recorded in the corresponding verdicts.

## Not duplicates

Whole-DAG statement searches were made for division, horizontal/vertical Reedy structures, inner horns with Segal, complete/walking-isomorphism restrictions, and cofibrations detected against fibrant fibrations. Exact proposed ids were searched across dag/nodes and both blueprint snapshots. blueprint_refs.py search was run for Segal, Reedy, walking isomorphism, inner horn and cofibration, and returned no blueprint matches for those phrases. The nearest-ancestor query returned prop-coef-integral-exceptional-adjoint. The following close existing nodes were opened and compared:

lem-coef-bisimplicial-reedy-division-calculus vs lem-coef-reedy-model-structure: the latter constructs generic Reedy structures; it does not identify bisimplicial cofibrations with all monomorphisms, give box-division lifting, or the all-monomorphism division criteria. Those identifications, not an elementary single-file specialization, are the new package's content.

lem-coef-segal-inner-horn-restriction vs lem-coef-segal-dk-diagonal-equivalence: the latter defines homotopy Segal spaces and proves a diagonal weak-equivalence criterion. It does not state trivial fibrancy of restriction along an inner horn.

lem-coef-complete-segal-walking-isomorphism vs lem-coef-segal-inverse-evaluation: the latter compares a derived mapping SPACE in Fun(Delta^op,Spc) with invertible arrows. The new node is a strict simplicial-set restriction map which is a trivial KAN FIBRATION, and tests completeness in the Reedy-fibrant model. Comparing coherent presheaf mapping spaces with the strict division model is not a one-line specialization; no such comparison is silently assumed. The existing inverse-evaluation theorem is a useful candidate for this child's later split, but its proof is not borrowed here.

lem-coef-complete-segal-walking-isomorphism vs lem-coef-rezk-local-model: the latter defines completeness through X_eq and supplies the model structure, not the walking-isomorphism restriction test.

lem-coef-joyal-walking-isomorphism-fibration-test vs lem-coef-joyal-quasicategory-characterizations: the existing statement tests lifting a specified equivalence EDGE; the new theorem tests lifting full maps from the walking-isomorphism NERVE. Extending a specified edge and prescribed image to all its coherent inverse simplices requires a theorem and is not asserted by that existing node.

lem-coef-joyal-walking-isomorphism-fibration-test vs lem-coef-joyal-interval-boundary-tests: the latter uses a finite freely inverted interval and its boundary-cylinder generators in all degrees. The new node uses the full groupoid nerve and only one endpoint inclusion, between quasicategories. These are different tests and neither change of interval is treated as definitional.

lem-coef-joyal-walking-isomorphism-fibration-test vs lem-coef-quasicategory-invertible-interval: the latter supplies endpoint evaluation and connects isomorphic objects by a J-map. It does not characterize a map as a Joyal fibration or solve lifting a prescribed J-map through it.

lem-coef-model-fibrant-fibration-cofibration-test vs lem-coef-cofibration-local-mapping-test: the latter is a simplicial local mapping-space test assuming left properness; the new theorem is a general ordinary model-category lifting test with both test objects fibrant, without a simplicial assumption.

No new node restates the item or one of its clauses. The children concern lifting criteria and auxiliary model structures, and the seven steps carry the relative lifting, constancy and comparison arguments. They do not simply apply a child asserting that rows are quasicategories, that the space is categorically constant, or that rowwise equivalences are Rezk equivalences.

## Review by Q06

I opened Joyal-Tierney's actual online Section 2, Proposition 3.4 and Proposition 3.10, Lemma 4.2, the proof of Lemma 4.3, the forward direction of Proposition 4.4, Theorem 4.5, Proposition 1.13 and Lemma 7.14. I also opened Rezk's Theorem 6.2 and Proposition 6.4, checking the difference between Joyal-Tierney's collapse-map completeness convention and the item's s_0:X_0 to X_eq convention. The child on completeness explicitly includes this convention comparison in its source, so it does not replace the project's definition with a different definition.

For the new division node I checked the order of both simplex variables, the two relative fiber-product targets, and the box lifting adjunction. Vertical means Kan columnwise and horizontal means Joyal rowwise. The all-monomorphism criterion for vertical division and the assertion that all objects are cofibrant are in the new statement, rather than being taken from the proof of the generic Reedy node. For the inner-horn node I checked vertical fibrancy and the full homotopy Segal hypothesis, and kept n at least 2 and 0<k<n. A Reedy-fibrant Segal space has Kan face/matching maps, so the strict Segal products in the source compute the homotopy products used by the project; this is why the theorem applies to the project's notion. For completeness I checked that J is the full nerve of the two-object contractible groupoid and that the conclusion is a trivial Kan fibration, not merely an equivalence of derived mapping spaces. For the Joyal test I retained BOTH quasicategory hypotheses and used the full groupoid nerve, not the finite interval in another existing node. For the generic lifting test I retained that i is a cofibration and that BOTH objects of every test fibration are fibrant; it does not assume A or B cofibrant.

Step 1 uses the division node's vertical trivial-cofibration criterion, the Kan node's monomorphism/weak-homotopy characterization, and the Joyal node's weak factorization system and two-out-of-three. All are stated explicitly in those nodes. The vertex inclusion is a weak homotopy equivalence by the written geometric contraction. The retraction identity is d s=1, with the direction of division reversed correctly; it is not s d=1. Completeness is not used here.

Step 2 uses precisely the inner-horn restriction statement and the division lifting bijection. A trivial Kan fibration lifts every monomorphism, so it lifts the empty inclusion into ANY simplicial set T. This supplies the general quasicategory X/T, including T empty, and hence every requested row. This argument is elementary after the two cited lifting statements. It does not substitute Mathlib's strict Segal theorem for the homotopy Segal hypothesis.

Step 3 uses the vertical model's stated simplicial enrichment and the Rezk node's stated mapping-space definition of weak equivalences. The test object Z is vertically fibrant because it is complete Segal. Applying the simplicial model axiom to j and Z to the terminal object shows directly that its mapping restriction is trivial Kan. Thus the inclusion of vertical trivial cofibrations in Rezk trivial cofibrations, and the vertical fibrancy of p, are justified by the two model axioms. No preservation theorem with missing cofibrancy hypotheses is being used.

Step 4 uses the inner-horn child's ABSOLUTE restriction statements for U and V, and the division child's RELATIVE Kan-fibration criterion for p. Its pullback projection and composite are written explicitly; pullbacks preserve the right lifting property, so the projection remains a trivial Kan fibration. Two-out-of-three then proves the relative restriction is trivial. Transposing against a monomorphism gives inner horn lifting for the relative division. I checked the target's quasicategory property separately: it is a pullback of the absolute inner fibration V/T to V/S over the quasicategory U/S. The text explains lifting a horn first in the base and then in that fibration, rather than assuming arbitrary pullbacks of quasicategories are quasicategories.

Step 5 uses the completeness child's endpoint restriction exactly as stated. The relative endpoint map is a Kan fibration by the vertical division criterion, and its weak-equivalence argument again uses the explicit pullback projection and composite. It lifts all monomorphisms; transposition gives the u_0 lift for the relative division. Step 4 has already supplied the inner-fibration and BOTH quasicategory hypotheses, so the Joyal walking-isomorphism test applies. Specializing to every boundary gives horizontal fibrancy of Rezk fibrations between fibrant objects. No child states this conclusion wholesale.

Step 6 uses the horizontal model's monomorphism cofibrations and the Rezk model's identical cofibrations. A horizontal trivial cofibration lifts the horizontal fibrations from step 5, hence every Rezk fibration between Rezk-fibrant objects. The new generic test states exactly the converse used to conclude it is Rezk trivial. This is the elementary adjunction-lifting part of Proposition 7.15, with the non-elementary restricted-fibration detection isolated in its own node.

Step 7 uses precisely the existing model-infinity-derived-adjunction clause that a left adjoint preserving cofibrations and trivial cofibrations preserves weak equivalences BETWEEN COFIBRANT OBJECTS. Both arbitrary objects of the horizontal model are cofibrant by the division/Reedy child. This removes any need for fibrancy of the original f and verifies the most easily lost hypothesis in the item.

I tested the new statements on the terminal and empty bisimplicial sets, and on constant bisimplicial sets arising from nerves where the stated Reedy-fibrancy hypotheses hold. Their horn restrictions satisfy the inner-horn result; a groupoid with two distinct isomorphic objects fails the completeness restriction test, as it should. I did not use arbitrary discrete nerves as fibrancy examples. For the horizontal model, q=0 has empty boundary and imposes the ordinary Joyal fibration condition on the first row. For division, T or S empty gives terminal division objects and correctly recovers the absolute maps. For the Joyal test an empty source over a nonempty discrete quasicategory is permitted: no lift is demanded without a source vertex, so no accidental surjectivity hypothesis was added. For the generic lifting theorem, identities satisfy both sides, and a non-weak cofibration is not accepted merely from a lifting property against trivial fibrations; tests against nontrivial fibrations between fibrant objects remain required.

I checked B1-B10: the five children are self-contained statement-only records, use their actual notion dependencies, have single TeX escapes, specific source places (with no invented Stacks tag), logged searches and filled blueprint ancestry. I checked C1-C8: every non-elementary input is a node statement, all cited statements were opened, the exact citations are in citations.json, there is no appeal to another node's proof, and no off-route tool or intentional cycle. I checked D1-D5: the actual deductions stay in the item, and no child moves an item clause or the whole theorem out of it. I checked E1-E7 with the hypothesis and small-case checks just described. The corrections made during this reading were the doubled TeX escaping, avoiding the circular mixed-box shortcut, and spelling out the quasicategory target of the relative division before using the Joyal test.

## Unfinished work

No part of the one-level split is left unfinished. Proving or splitting the five new statement-only children is later stage-1 work, as required by the brief. Source archival remains wanted. A fresh second reader must inspect and deliver this sandbox; this worker only dry-runs it.

## Final worker check

The first server dry run printed OK (not pushed), preflight passed, at 3499ef1c54. During the final source-place check I corrected the last step's Brown-lemma reference to Joyal-Tierney Corollary 7.11; Proposition 7.12 is instead the cobase-change theorem and was not used. I also stated the two Segal restriction children using only the already existing homotopy-Segal definition and the new independent Reedy/division notation, with completeness defined explicitly in the endpoint-test statement. Thus those primitive children do not depend on the entire Rezk model theorem. This matters for its later split: its mixed-box clause can use these lifting criteria without a back edge to the item or the Rezk model theorem itself. No mathematical assertion changed, and the exact citation quotes were regenerated. The final sandbox is subjected to a second required no-push server dry run after these corrections.


## Second reading by Q06

I reread the item statement against Joyal–Tierney, arXiv:math/0607820, Proposition 4.4 and Theorem 4.5, with rows and the contravariant vertical map checked in every degree; verdict: hypotheses and conclusions agree, including the unfibrant final assertion.

- Step 1: checked against the division, Kan, and Joyal model statements; the vertex inclusion is a monomorphic Kan weak equivalence and the direction of $d=X/v$ and $s=X/t$ is correct; verdict: sound.
- Step 2: checked the horn-to-division adjunction and the empty inclusion $\varnothing\hookrightarrow T$; verdict: elementary after the cited statements and covers empty $T$.
- Step 3: checked the Rezk mapping-space definition, simplicial model axiom, and vertical weak factorization system; verdict: both fibrancy hypotheses and the cofibration inclusion are present.
- Step 4: checked the relative pullback target, pullback of the trivial Kan fibration, two-out-of-three, and quasicategory property of the target; verdict: sound with no implicit pullback fibrancy assumption.
- Step 5: checked the completeness endpoint test, relative restriction, and both quasicategory hypotheses required by the Joyal walking-isomorphism test; verdict: sound in degree zero and positive degrees.
- Step 6: checked the identity Quillen criterion and the model fibrant-fibration test; verdict: the test is applied only to Rezk fibrations between fibrant objects.
- Step 7: checked the derived-adjunction preservation clause and cofibrancy of the horizontal model; verdict: no fibrancy assumption is added to the arbitrary map.

- `lem-coef-bisimplicial-reedy-division-calculus`: checked all division formulas, both Reedy structures, and cofibrancy against Section 2 of the cited source; verdict: self-contained statement-only node.
- `lem-coef-segal-inner-horn-restriction`: checked $n\ge2$, $0<k<n$, homotopy Segal and vertical Reedy-fibrancy hypotheses against Proposition 3.4; verdict: self-contained and correctly states a trivial Kan fibration.
- `lem-coef-complete-segal-walking-isomorphism`: checked the full walking-isomorphism nerve, endpoint, and the project's $X_{\mathrm{eq}}$ completeness convention against Lemma 4.2 and Rezk's convention; verdict: self-contained.
- `lem-coef-joyal-walking-isomorphism-fibration-test`: checked both quasicategory hypotheses, full groupoid nerve, and no vertex-surjectivity condition against Proposition 1.13; verdict: self-contained.
- `lem-coef-model-fibrant-fibration-cofibration-test`: checked the cofibration hypothesis and fibrancy of both test-object endpoints against Lemma 7.14; verdict: self-contained.

I searched the whole DAG, both blueprint snapshots, and Mathlib candidates for each child; no duplicate or exact Mathlib declaration was found. I verified every citation quote byte-for-byte against its cited node statement and checked that no step cites a node proof. I corrected the report's overbroad discrete-nerve fibrancy example to restrict the example to cases satisfying the stated Reedy-fibrancy hypotheses; no DAG statement or proof step required mathematical change. The five children remain statement-only, with no hollow definitions, no SGA 4 citation, and no source statement dispute.
