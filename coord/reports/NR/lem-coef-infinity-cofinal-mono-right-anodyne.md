# Stage-1 report: lem-coef-infinity-cofinal-mono-right-anodyne

## Files written

- dag/nodes/sec-six-functors/lem-coef-infinity-cofinal-mono-right-anodyne.json: existing statement, now split into six proof steps, no Mathlib match.
- citations.json: one exact statement quotation for each step/node citation.
- searches.jsonl: five actual searches made with the required msearch command. The item preserves all inherited searches and appends these records.
- report.md: this report. prepare.py is the sandbox-only preparation script, not a delivered node.

There are zero new nodes and zero Mathlib leaves. No unit/chapter record is changed. The sandbox had no existing item or report when this worker started, so there was no previous split or dry run to recover.

## Attachments

None. Searched the read-only slopmaster2 WeilConjectures tree for the exact item/tag and cofinal-monomorphism, anodyne and right-fibration vocabulary. No project declaration states the item. The master checkout was also searched as reference only. This item has no Lean audit declaration to inspect; master sorry declarations were not treated as proofs. No Lean file was written and no compiler, Lake or build command ran.

## WANTED

WANTED: archival Kerodon, Proposition 7.2.1.3 (02N3), Theorem 7.2.3.1 (02NY), Remark 7.2.3.2 (02NZ), Proposition 7.4.3.11 (04K3), and Propositions 4.2.5.1 (00TP), 3.2.7.2 (00X1), 4.2.4.5 (014X), for this item. Read their actual online pages. These are Kerodon tags, not Stacks tags; no Stacks tag states this quasicategory theorem.

WANTED: archival Lurie, Higher Topos Theory, Lemma 2.2.3.4, Corollary 3.3.3.4 and Remark 3.3.3.5, for the already existing section-space foundations cited by this split. Their statements were read in the DAG; no claim is made here to have read an unavailable local HTT archive.

## Findings and corrections

The item statement is unchanged, including fullness, smallness, all higher comma data, and the horn orientation 0 < i <= n. There is no statement dispute. Fullness is stronger than needed in the proof but was retained as requested. No target, coefficient definition, or upstream statement changes.

The initially empty proof is now an argument rather than an application of a renamed cofinal-monomorphism theorem. It passes through finality, limits of right-fibration transport, a weak equivalence of the actual section-restriction map, its Kan fibration property, exact lifting, and a small-object retract. The final step spells out coproduct refinement because the right-anodyne definition lists pushouts and transfinite composites rather than coproducts. Section restriction is not asserted to be a trivial fibration merely because it is a weak equivalence: its independent Kan-fibration hypothesis is cited.

The existing unit sk-prop-sf-biduality-general and chapter sec-six-functors were read, as was paragraph 2 of main-20261015 prop-coef-integral-exceptional-adjoint.proof.md. This is a generic infrastructure lemma in the item's already recorded ancestry to the coherent mapping-complex adjunction and operadic join-slice extension. The unit has no proof steps to rebind and this item is not its key node. No SGA source is used. No off-unit statement tool is needed; all cited statement nodes have the item's unit, and the other citations are definitions.

## Mathlib and duplicate searches

Read the actual output of all five new searches. LeanFinder's two different formulations returned all-horn Quillen classes, monomorphism/cofibration results and inner-horn fillers. Loogle and the focused Quasicategory grep returned no hits. LeanSearch found generic small-object and model-category lifting statements, and all-horn Quillen fibrations. Read Mathlib/AlgebraicTopology/Quasicategory/Basic.lean:34–103 and SimplicialSet/CategoryWithFibrations.lean:35–114: the all-horn J class and an inner-horn filler are not this right-horn theorem. Generic small-object results are already supplied by the existing cited node, not a reason to mark the entire item Mathlib.

Searched the whole DAG by cofinal, monomorphism, right-anodyne and section-restriction vocabulary and the relevant tags. Ran blueprint_refs.py ancestor and whole-blueprint searches for the item concept, right anodyne, cofinal monomorphism and 02N3; no matching blueprint statement exists. Reused the already existing section/limit and homotopy-descent-gluing nodes. Terminal-anodyne is only a one-vertex specialization, and cone-mono-right-anodyne concerns coned inclusions, so neither restates the item. The existing equivalence-section-restriction lemma assumes an equivalence, which the present final inclusion need not be. No helper was created for opposite-cone duality, uniqueness of terminal objects, pullback horn lifting, finite-face smallness or the arrow retract, because those are explicit routine arguments.

## Not duplicates

No new nodes, hence no new/existing same-tag pair.

## Review by NR

I read the item against Kerodon 02NZ condition (2′), 02NY, and 02N3. In particular, 02NZ uses the oriented arrow-pullback comma, exactly the model here; I did not substitute a set of objects, a core or an ordinary comma category. I also read 04K3's universal-colimit condition, 00TP's exponentiation assertion, 00X1's weak-equivalence/Kan-fibration criterion and 014X's horn lifting convention. With the required archives absent, proof_origin is agent, tied to the actual ancestor blueprint, and the online sources are identified above.

For step 1 I opened lem-coef-infinity-cofinality-space-test: its condition (3) displays exactly our comma, and its condition (1) preserves the given colimiting cocone in every containing target. The smallness assumptions agree. This is stronger than preservation only for space-valued diagrams and allows the opposite space category used in step 3.

For step 2 I opened lem-coef-right-fibration-section-limit. It asserts that sections are Kan, evaluation is a limit cone, and the comparison is natural under restriction of the base. I checked pullback lifting directly and fixed a common universe before taking sections and transport. This establishes the actual evaluation comparison, rather than borrowing the proof of a cited node. The fibers and section spaces may be empty.

For step 3 I reread the terminal-cone and initial-cocone definitions in def-cbc-enhanced-diagrams-cones. Opposites interchange these definitions and reverse the direction of the vertex comparison. Thus finality of j restricts the colimit of m_q^op and says that the restricted cone on m_q is limiting. Its universal comparison to the section limit is exactly restriction by step 2's stated naturality. Two terminal cones have inverse comparison maps because each composite and identity lie in the same contractible mapping space. This gives the weak equivalence of r, including all coherent data; it does not require an uncited theorem identifying limits with merely sets of compatible vertices.

For step 4 I opened lem-coef-unstraightening-homotopy-descent-gluing: its monomorphism clause explicitly makes over-map restriction a Kan fibration for arbitrary simplicial bases. Then lem-coef-kan-quillen-right-proper explicitly supplies a model structure with these weak equivalences and Kan fibrations, and characterizes trivial fibrations by boundary lifting including dimension zero. These statements supply both hypotheses, so r has exact lifts. Pulling an arbitrary p:X -> S back to B puts a lifting square in precisely this situation; no quasicategory assumption on S was added.

For step 5 I opened lem-coef-small-object-cell-factorization and def-weil-pbc-category-colimit. The former needs small Hom sets, small colimits and preservation of the specified omega-chain colimits by horn domains. The step verifies each: finite face data and finite overlaps stabilize, while degreewise set pushouts preserve injections. It produces a small factorization whose second map is a right fibration with the exact nonzero-index horns; no global model structure for right fibrations is assumed.

For step 6 I opened def-coef-infinity-right-anodyne. I checked both arrow squares using s j = i and p s = id, and the small well-ordered refinement of each coproduct attachment against that definition's actual closure operations. The step is elementary once the preceding factorization/lift exists; it contains no separate classification theorem. Every cited node has a verbatim quotation in citations.json. I checked the dependency closure for a path back to this item; none of the cited statements depends on it.

I tested B empty (then A empty), j the identity, B a point, the final-vertex inclusion {1} -> Delta^1, and an attempted empty A with nonempty B. The final-vertex case fixes the right-horn orientation; the last case violates comma contractibility rather than forcing a nonexistent section. The initial-vertex inclusion {0} -> Delta^1 fails the comma test at 1, as it should. For an arbitrary empty right fibration, both section spaces in the nonempty indexing case are empty and the proof does not demand a vertex unless a given lifting square supplies one. Small-object horn n=1 and coproducts with no cells are included.

Against delivery-errors B–E: no statement-only helper with a hidden proof, no new notion, no unrun recorded search, no off-unit route replacement, no renamed clause, and no appeal to the proof of another node. Step lengths are 475, 811, 1054, 1015, 1191 and 1029 characters: none exceeds 2000, and I checked the routine inline arguments for hidden lemmas. The only corrected issue during preparation was making section-to-limit naturality and the separate Kan-fibration input explicit; the statement needed no correction.

## Unfinished work

No mathematical part of this one-level split remains. New foundation nodes: none. A fresh second reader must review and deliver; this worker runs only the required --no-push dry run.

## Second reading by NR

I independently reread the existing item statement, all six proof steps, `citations.json`, and the five recorded Mathlib searches. There are no new nodes, so the new-node checklist has no entries. The item is checked against Kerodon Remark 7.2.3.2 (02NZ), Theorem 7.2.3.1 (02NY), Proposition 7.2.1.3 (02N3), Proposition 7.4.3.11 (04K3), and the cited 00TP, 00X1, and 014X pages; the displayed arrow-pullback comma, right-cofinal orientation, smallness, and right-horn range agree.

- Step 1: checked against `lem-coef-infinity-cofinality-space-test`; its comma and finality clauses supply exactly the conclusion used, with no colimit hypothesis on A or B.
- Step 2: checked against `lem-coef-right-fibration-section-limit`; pullback right-fibration lifting, section Kan-ness, evaluation limits, and restriction naturality all match the step.
- Step 3: checked against `def-cbc-enhanced-diagrams-cones`; passage to the opposite, terminal-cone uniqueness, and the induced equivalence of section spaces are explicit and coherent.
- Step 4: checked against `lem-coef-unstraightening-homotopy-descent-gluing` and `lem-coef-kan-quillen-right-proper`; the restriction map is a Kan fibration, the weak-equivalence-to-trivial-fibration input includes dimension zero, and the arbitrary-base lifting square is formed by the stated pullback.
- Step 5: checked against `lem-coef-small-object-cell-factorization` and `def-weil-pbc-category-colimit`; the countable right-horn set, small colimits, injective cell stages, and finite-domain preservation of omega-chains meet the cited hypotheses.
- Step 6: checked against `def-coef-infinity-right-anodyne`; the two arrow-category maps give the stated retract, and coproduct attachments are refined into the allowed transfinite sequence of single horn pushouts.

I tested the empty and identity inclusions, a point, the final-vertex inclusion in $\Delta^1$, the failing initial-vertex inclusion, empty right-fibration sections, the $n=1$ horn, and an empty coproduct. No statement dispute or mathematical repair is needed. No duplicate or elementary new node exists, and no cited node depends on this item. I changed only this report by adding this independent audit; the item JSON, citations, and search records remain unchanged because their statements and records passed review. No Lean, compiler, Lake, build, live-project, or live-launcher operation was performed.
