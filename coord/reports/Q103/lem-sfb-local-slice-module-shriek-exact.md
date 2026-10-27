# Stage-1 repair: lem-sfb-local-slice-module-shriek-exact

## Worker report

Files delivered:

- dag/nodes/sec-six-functors-basics/lem-sfb-local-slice-module-shriek-exact.json: split item, statement unchanged, six proof steps.
- dag/nodes/sec-six-functors-basics/lem-sfb-module-shriek-forgetful-counit-criterion.json: retained statement-only child, unsplit, no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-abelian-lower-shriek-exact.json: new statement-only child for Stacks 04BH, unsplit, no Mathlib match.
- citations.json: twelve verbatim quotations, reindexed to the repaired proof. searches.jsonl retains the prior six searches and appends the six actual searches for the abelian exactness child. Sandbox preparation scripts are not delivered.

Attachments: none. The item and both child tags have no matching project declaration. I reread HasLeftKanExtension.lean:297-381, 403-418 and 467-483: its over-map lower shriek and over-pullback exactness results concern special scheme-site functors, not arbitrary site functors preserving pullbacks and equalizers. Searches in WeilConjectures/ by the item tag, both child tags, lower-shriek terminology, exactness-lower-shriek, 04BH and slice equivalence gave no theorem stating the item or the new child. No Lean was written and no compiler, Lake or build command was run.

WANTED: none.

Return repaired: the approved returned head was ed48ae3bb1c. In the current DAG, lem-sfb-ringed-site-slice-equivalence-exact-shriek has been split by Q39 and its proof now depends on this item. The retained delivery cited it in Step 1, producing the reported two-node cycle. The first required dry run reproduced exactly that failure and exited before any push. I reread the changed node's statement, both proof steps, proof_deps and review, then removed every citation to it from this item's proof and citations.json. Its file is not edited. The current item's maintainer-owned fields are reread from the current repository; only split-owned fields are applied. deliver.py prepares the commit on the current server base. This is a mathematical repair, not an unchanged rebase.

Nothing remains unfinished in this one-level split; both children intentionally remain unsplit. No statement dispute or correction is needed.

## New nodes

The retained counit criterion is unchanged from the prior delivery and keeps its prior searches and blueprint information. The new abelian exactness node states 04BH for a chosen abelian left adjoint: continuity, cocontinuity, existence and preservation of fibre products and equalizers, and exactness. It assumes neither slice equivalences nor any ring and concludes no module comparison. Its source is sites-modules.tex, Tag 04BH, label lemma-exactness-lower-shriek (lines 1658-1695). Its additivity clause is the standard additivity of an adjoint between abelian categories. Both children have self-contained statements, empty proof/proof_deps and null proof_origin. Neither is a clause of the module item merely relabelled: the proof constructs the module adjoint, checks the local counits and transports exactness, rather than outsourcing those steps to a new copy of the item.

## Searches and blueprint

Prior logged counit searches and their results are retained, as is the item's prior Mathlib search evidence. For the new abelian theorem I ran LeanFinder with two phrasings, LeanSearch, Loogle and two greps using msearch.py; all services answered. The exact tool/query strings and actual results are copied from searches.jsonl into the new node. I read Mathlib CategoryTheory/Sites/Pullback.lean:45-121 and CoverLifting.lean:317-375. The former's finite-limit theorem additionally assumes RepresentablyFlat and finite-limit preservation by the presheaf Kan extension. These hypotheses cannot be inferred merely by pretending a terminal object exists: the present theorem explicitly permits its absence. The latter adjunction has precomposition on the left, whereas our A is left adjoint to precomposition. The other hits are general exactness or sheafification/local-injectivity facts, not this theorem. There are zero new Mathlib leaves.

I searched the whole DAG by 04BH, lemma-exactness-lower-shriek, abelian lower shriek, continuous/cocontinuous exact adjoints, and the prospective id. The only matching slice-shriek theorem nodes are the item and the existing dependent ringed-site node. lem-sfb-site-left-adjoint-connected-limits states preservation of pullbacks and equalizers on SET sheaves, not the abelian exactness theorem. I reuse existing generic generator and partial-adjoint nodes instead of creating module-adjoint duplicates. Blueprint searches for 04BH and abelian lower shriek returned zero; lower shriek and exact left adjoint returned geometric/derived or open-extension statements, none stating 04BH. The ancestor command still reports None; the inherited from.node and via chain are retained, with the item's id prepended for the new child. I reread the chapter/unit records and latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md. No chapter or unit route is changed.

## Not duplicates

lem-sfb-abelian-lower-shriek-exact vs lem-sfb-local-slice-module-shriek-exact: the child concerns abelian sheaves for any limit-preserving continuous cocontinuous functor; it has no ring, slice-equivalence assumption or forgetful comparison. The item needs a separately constructed module adjoint and local comparison to apply it.

lem-sfb-abelian-lower-shriek-exact vs lem-sfb-ringed-site-slice-equivalence-exact-shriek: the existing theorem is about module adjoints under slice equivalences and now depends on the item; the child is the more general abelian exactness input, independent of slice equivalences. It does not duplicate that module theorem.

lem-sfb-module-shriek-forgetful-counit-criterion vs lem-sfb-local-slice-module-shriek-exact: the child assumes chosen adjunctions and proves the comparison from ring counits; it does not construct the module adjoint or prove exactness. Steps 3-4 verify its conditions from slice equivalences.

lem-sfb-module-shriek-forgetful-counit-criterion vs lem-sfb-ringed-site-slice-equivalence-exact-shriek: the existing node states no comparison with abelian sheaves; the child does not conclude its exact-adjoint assertion. The old Step 1 reuse is removed because that node now depends on the item.

## Review by Q103

I reread the full return, the returned sandbox proof/report/citations and all search logs, and compared the current item with the retained split. The important changed citer is the ringed-site theorem: its statement is unchanged, but its formerly empty proof_deps now contains this item. The earlier report's assertion that its closure did not reach the item was true only of the earlier snapshot and is explicitly superseded here. The required initial dry run confirmed the live cycle. The replacement proof has no edge to that theorem. I checked the statement/proof dependency closures of every replacement generic tool against both members of the cycle; none reaches either. This resolves the return's single numbered concern (C6) without changing either statement.

I read 0797, lemma-lower-shriek-modules (8001-8039), all of 0798, remark-when-shriek-equal (8042-8090), and 04BH, lemma-exactness-lower-shriek (1658-1695). I also read 03DA/03DB, lemma-abelian and lemma-limits-colimits (1337-1402), and Homology 0793, lemma-partially-defined-adjoint (7388-7452). The first child is the precise localized-ring counit sufficient condition in 0798; the second is precisely the general abelian exactness input 04BH. The item retains all its original hypotheses and conclusions.

Step 1 uses the statements of def-weil-sheaf-of-modules-category, lem-trf-ringed-site-restriction-generator-data and lem-trf-partially-defined-module-adjoint, each opened in the current DAG. The first gives abelian module categories in the stated small universe. The generator theorem explicitly gives additivity of T, a small epimorphic generating class and the corepresenting bijections for every small sum. The partial-adjoint theorem explicitly requires these data and supplies L left adjoint to T. The Hom bijections are used only from the statements, with their correct adjunction direction. An object isomorphic to a sum is handled by composing its Hom bijection with that isomorphism; no unrecorded generator theorem or exactness of L is assumed.

Step 2 cites the existing left-adjoint-colimit and finite-colimit-additivity statements, plus the module-category definition: L preserves finite colimits, hence is additive. Both former nodes are Mathlib leaves. The construction does not assume that every left adjoint on arbitrary categories is additive.

Step 3 retains the former Step 2 and its actual citations, all reread: the continuity node states that set and abelian sheaves precompose to sheaves; the adjunction leaf supplies A and each A_U. The localized-ring definition gives covering families and restricted sections. Covers, covering pullbacks and their preservation restrict to slices. A cocontinuous lifted cover retains its composite to U. All slice and comma indices remain small. The restricted-ring identity is sectionwise, so no new scalar comparison is assumed.

Step 4 retains the explicit elementary counit argument: a quasi-inverse to an equivalence of sites identifies cover sheaf-condition diagrams, giving inverse functors on abelian sheaves. Fullness lifts the unit to d; the triangle identity and faithfulness give c_U d = 1, and the adjunction bijection gives d c_U = 1. Thus the precise counit used by the child is invertible; this is not just an unrelated abstract isomorphism. No original site needs a terminal object.

Step 5 applies only the retained counit child's statement, with the same module adjunction fixed in Step 2 and the abelian adjoints of Step 3. Its gamma is the adjunct of the forgotten module unit. The inverse gives the requested natural isomorphism, with the correct direction. The repaired text defers exactness to Step 6 rather than claiming it already proved.

Step 6 applies the new 04BH statement under the given pullback/equalizer assumptions. I reread lem-weil-pbc-module-sheaves-colimits-forgetful: it explicitly states faithfulness and preservation of kernels and cokernels on a small site with sheafification, which applies to both sites. The gamma isomorphism sends the underlying image sequence to A of the underlying input sequence. Kernel/cokernel preservation identifies its endpoint defects and middle homology with zero abelian sheaves. A module object with zero underlying identity is zero by faithfulness, so exactness is reflected. This writes out the elementary reflection argument instead of citing the forgetful node for an unstated reflection theorem.

The generic off-unit tools are declared with specific reasons in split_report.tool_uses: the generator computation and abelian partial-adjoint extension from the trace-formula chapter are general site/category facts used in the very same Stacks 0797 proof, not trace-formula assumptions. The continuity fact is a generic site tool. Exact faithful forgetting is a generic module-site tool and is also already Lean-closed. No SGA route is used. No new tool's dependency closure reintroduces the item.

I checked B-E on both child statements and every repaired step: no hidden proof in an unsplit node, all objects and notions introduced or defined by dependencies, precise tag/label sources, actual logged searches, no duplicate theorem, no proof-only citation, no extra hypothesis, no relabelled module theorem. Verbatim quotations were checked against each current cited statement and assigned to the repaired step numbers. All steps are below 2000 characters (722, 249, 644, 789, 414, 853); none hides a long sublemma.

Small cases: u = identity gives identity comparison and exact identity; R = 0 gives zero module categories; an empty source site makes the local condition vacuous and both left adjoints send its zero sheaf to zero. For the new abelian theorem, a discrete two-object source mapping to a point gives A(M,N) = M direct sum N; it is exact though it does not preserve the terminal SET sheaf. This specifically tests the absence of a terminal-preservation assumption that the Mathlib finite-limit theorem would require. Empty sites and zero short exact sequences remain allowed. The final required server dry run and push are recorded by deliver.py.

## Retained report from returned head ed48ae3bb1c (historical)

The following prior report is preserved for its proof, citations and searches. Its four-step numbering and claims about the ringed-site node's old dependency closure are superseded by the repair and review above.

# Stage-1 delivery: lem-sfb-local-slice-module-shriek-exact

## Worker report

Files written, all in the assigned sandbox:

- dag/nodes/sec-six-functors-basics/lem-sfb-local-slice-module-shriek-exact.json: item, split, statement unchanged.
- dag/nodes/sec-six-functors-basics/lem-sfb-module-shriek-forgetful-counit-criterion.json: new statement-only lemma, unsplit, no Mathlib match.
- citations.json: a verbatim statement quotation for every citation in every item proof step.
- searches.jsonl: the unmodified search-command log; report.md: this report. write_split.py is the sandbox-only JSON preparation script and is not part of the delivery.

Attachments: none. I searched the whole project WeilConjectures source by the item tag, prospective new tag, slice-equivalence terminology and lower-shriek terminology. The localizations in CategoryTheory/GrothendieckAbelian/HasLeftKanExtension.lean concern a monomorphism in a morphism-property over category; they do not state this arbitrary ringed-site theorem or its coefficient-ring counit comparison. No declaration found states all clauses of the item. No Lean was written or compiled.

WANTED: none. The Stacks sources required here are present.

The inherited item has no proof steps. Its statement correctly includes the underlying-abelian comparison, which is missing from the statement of the existing lem-sfb-ringed-site-slice-equivalence-exact-shriek. I reuse that existing node for the exact module adjoint, instead of generating another copy. I do not infer the comparison from that node's proof or source field. The new lemma records precisely the more general counit criterion needed for the comparison. There is no statement dispute or correction.

Nothing remains unfinished in this one-level split. The new lemma is intentionally unsplit, as required for a stage-1 child.

## New nodes

lem-sfb-module-shriek-forgetful-counit-criterion is the criterion in Stacks Tag 0798, remark-when-shriek-equal, including the canonical transformation and equation-compare-on-localizations. It assumes the chosen module and abelian adjunctions, and invertibility of the localized ring counits. It does not assume slice equivalences or equalizer preservation, and it does not conclude exactness or construct the module adjoint. Its statement introduces its sites, rings, functors, adjunctions, forgetful functors, localized rings, counits and canonical comparison.

For a future split of this child, the source's argument tests the comparison on the module generators j_U! R_U and then uses presentations by sums of these generators. Composition of abelian left adjoints along the localized square identifies that generator comparison with j_u(U)! applied to the local ring counit. These arguments belong to the child's eventual split, not to its statement. They have not been inserted as uncited proof steps into the present item.

## Searches and blueprint

Before creating the child I searched the whole DAG by 0798, remark-when-shriek-equal, equation-compare-on-localizations, lower shriek plus forgetting, and slice-site equivalence terminology. I read both existing slice-shriek statements. I also searched the imported blueprint with tools/blueprint_refs.py search for "lower shriek", "0798", "equivalence of sites" and "forget"; no blueprint statement gives this general localized-ring criterion. The lower-shriek blueprint hits concern geometric/open or derived operations and do not replace the criterion.

The unchanged item's inherited Mathlib searches were read and retained: the module adjunction, sheaf adjunction and finite-limit-preservation hits do not give the full slice-equivalence theorem. I inspected PullbackContinuous.lean:45-125 and Limits.lean:92-120 directly. No duplicate search of this unchanged question was necessary.

For the new child, the six actual msearch.py queries are recorded verbatim in its mathlib_searches and searches.jsonl: two LeanFinder phrasings, LeanSearch, Loogle, and two source greps. All services answered. The hits give module pullback and sheafification adjunctions, reflection of isomorphisms, stalk identifications or the continuous/cocontinuous sheaf adjunction, not the localized-ring criterion. In CoverLifting.lean:317-375, sheafAdjunctionCocontinuous has precomposition as its LEFT adjoint; this is not the adjunction A left adjoint to precomposition needed here. PullbackContinuous.lean supplies module adjunctions without this forgetful comparison. None is an exact match or one-line specialization. There are zero new Mathlib leaves.

I read the chapter/unit records and the latest blueprint sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md. This is a supporting site lemma far below the inherited alteration/direct-image branch, not a change to that route. tools/blueprint_refs.py ancestor reports blueprint.from.node = None for the inherited chain. I preserved that ancestor and all intermediate via entries; the child adds the item to the front of via and specifies the 0798 comparison place. No chapter or unit file is changed.

## Not duplicates

lem-sfb-module-shriek-forgetful-counit-criterion vs lem-sfb-local-slice-module-shriek-exact: the child is a general conditional comparison theorem for specified adjunctions, with localized ring counits as its condition; the item assumes actual site equivalences and limit preservation and concludes existence and exactness as well as comparison. Steps 2 and 3 establish the child's local conditions, including the counit normalization, rather than moving the item's slice-equivalence assertion into a child.

lem-sfb-module-shriek-forgetful-counit-criterion vs lem-sfb-ringed-site-slice-equivalence-exact-shriek: the existing node concludes existence of an additive exact module adjoint under slice equivalences. It states no comparison with abelian sheaves. The new node assumes adjunctions and proves the forgetful comparison from local ring counits, without slice equivalence or limit-preservation hypotheses; the existing node is reused in Step 1.

## Review by Q103

I read sites-modules.tex, lemma-exactness-lower-shriek (04BH, lines 1658 onward), lemma-lower-shriek-modules (0797, lines 8001 onward), and the whole remark-when-shriek-equal (0798, lines 8042-8090). The item is the valid combination of 0797, 0798 and 04BH. The new child states the final conditional implication of 0798. Its map c_U is the source's comparison-on-localizations map, identified with the abelian adjunction counit because the structural ring map is the identity. The transformation gamma is specified by the forgotten module unit, which is exactly the source's canonical transformation; the item needs its inverse, so the direction is checked.

Step 1 cites the whole statement of the existing lem-sfb-ringed-site-slice-equivalence-exact-shriek. I matched all its hypotheses: small sites in the fixed module universe, the same continuous and cocontinuous u, R'=R composed with u, fibre products and equalizers existing in C and preserved by u, and ring-identifying site equivalences on every slice. Its conclusion supplies both additivity and exactness, with no terminal-object requirement. It does not supply the forgetful comparison and is not cited for one. Its dependency closure does not reach this item.

Step 2 cites lem-weil-pbc-site-continuous-pushforward-sheaf for restriction sending sheaves of sets and abelian groups to sheaves, and lem-weil-pbc-continuous-functor-sheaf-pullback-adjunction for the actual abelian left adjoints. I opened their statements and checked that the second applies once precomposition preserves set sheaves. I checked the same hypotheses for each localized site: its covers and covering pullbacks are those underneath, and a cocontinuous lift over V retains its composite to U. The cited def-pur-localized-ringed-site explicitly defines these covers and the formula for the restricted ring. The equality R' restricted to U = T_U applied to R restricted to u(U) is a sectionwise equality, not a new ring identification theorem. Smallness survives forming the slices and comma categories. The continuity lemma is declared as a generic off-unit tool; the adjunction lemma already has status mathlib. No replacement of a unit's proof route is involved.

Step 3 is an elementary argument from the assumed equivalence of sites and the adjunction bijections: precomposition with a covering-preserving quasi-inverse gives inverse functors on abelian sheaves. Transport of the sheaf-condition diagrams verifies that these are functors on sheaves, not merely on presheaves. Fullness lifts the unit to d, faithfulness and the first triangle give c_U d = 1, and injectivity of the adjunction bijection gives d c_U = 1. This explicitly proves the condition needed in Step 4, for the specified counit. It does not cite a definition in place of an equivalence theorem or assert an unspecified isomorphism.

Step 4 cites only the new criterion, whose statement says exactly that these c_U make the specified gamma invertible. The comparison is natural because it is that natural transformation's inverse. The additive exact L from Step 1 is the same L fed into the criterion. The citations file quotes only actual statement substrings, including the defining slice statement and the adjunction clause. Every proof dependency is in the union of the step citations.

I tested the new statement on the identity functor (both ring counits and gamma are identities up to the chosen adjunction identifications), the zero ring (both module categories are zero), and the empty source site (the local condition is vacuous and both left adjoints send its unique zero object to zero). Slice localizations have their own terminal object U/U; no terminal object of C or D was introduced. General continuous cocontinuous functors without the local counit condition are not claimed to satisfy the comparison, in agreement with the warning in 0798. All new notions have definition dependencies or an inline definition, TeX uses single decoded backslashes, the child has empty proof/proof_deps and no proof sketch in its statement, and the source names the precise tag and label. I checked B-E with the files open. No non-elementary step exceeds 2000 characters (lengths 427, 644, 789, 427); no hidden comparison lemma is buried in a long step. I corrected the initial planning assumption that the two existing slice-shriek nodes had identical statements: only the present item has the forgetful clause, which explains why the existing node cannot replace the full item.
