# Worker report: lem-sfb-modobj-restriction-preserves-limits

## Files written

- `dag/nodes/sec-proetale-coefficients/lem-sfb-modobj-restriction-preserves-limits.json`: statement node, status `split`; unchanged statement, explicit restriction statement dependency and two proof steps. Not itself a Mathlib leaf.
- `citations.json`: retained the two exact statement quotations and checked them again against the current shared DAG.
- `report.md`: refreshed this worker review of the earlier sandbox attempt. `searches.jsonl` retains earlier command records and the fresh searches from this review.

New nodes: 0. New Mathlib leaves: 0. Reused the existing Mathlib leaf `lem-weil-pbc-right-adjoint-preserves-limits`.

## Attachments

None. Searched `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/` for the blueprint tag, its recorded instance name, `extendRestrictAdjunction`, comap/limit patterns, and restriction of scalars. No project declaration states this general internal-module assertion. The ordinary-module/sheaf restriction declarations in `Algebra/Category/ModuleCat/Sheaf/RestrictScalars.lean` have a different coefficient category. The reference master instance at `WeilConjectures/CategoryTheory/ModuleObjects/ExtendScalars.lean:475–476` applies the extension-restriction adjunction, but that checkout is not accepted completion evidence. No ATTACH is claimed.

## WANTED

None. All sources needed for this split are available locally.

## Corrections and source route

Read the current `main-20261015` chapter `_section.md`, scalar-change unit `_section.md` item 2, the item's statement and companion `.proof.md`, and the extension, restriction and adjunction node statements. The companion proof gives only the assertion that restriction is a right adjoint; the split supplies the missing implication through the already existing right-adjoint-preserves-limits node. This follows exactly the final implication of unit item 2.

The original shared item has no `chapter` or `unit` fields. Neither `dag/chapters/sec-proetale-coefficients.json` nor `dag/units/sk-def-sfb-change-of-scalars.json` exists, so I read the current blueprint chapter and unit directly. This maintainer metadata is left unchanged. The item is not the unit's statement-bearing key node, so no unit realization file is written.

The earlier sandbox attempt already repaired the incomplete imported proof and added the direct restriction definition dependency. I retained those mathematical changes. In this pass I located and read the current companion proof, made step 1's source point to it explicitly, repeated the Mathlib searches, recorded the additional scoped grep, and replaced stale delivery/second-reader narrative with this worker handoff. The statement has no identified typing defect or counterexample; no statement correction is needed.

## Mathlib and duplicate searches

All Mathlib queries used `/home/ubuntu/weil-launcher-nt/msearch.py Q51 lem-sfb-modobj-restriction-preserves-limits`; the exact query strings are in the item's `mathlib_searches` and the command's log. Fresh LeanSearch and LeanFinder restriction queries returned ordinary `ModuleCat` results and the internal `Mod_.comap` construction. Read `Mathlib/Algebra/Category/ModuleCat/ChangeOfRings.lean:932–940`: its theorem concerns modules over rings, not modules internal to this arbitrary braided monoidal category. Read `Mathlib/CategoryTheory/Monoidal/Mod.lean:340–425`: `comap` is the restriction construction, without the preservation assertion. The scoped grep returned this construction and unrelated Mon/tensor/reflector/internal-Hom preservation facts.

A second semantic phrasing, `A functor which is a right adjoint preserves limits of every diagram`, and Loogle query `CategoryTheory.Adjunction.rightAdjoint_preservesLimits` returned the general right-adjoint theorem. The scoped Adjunction grep located its declaration at `Mathlib/CategoryTheory/Adjunction/Limits.lean:207`; I read its type, universes and proof at 190–214. It is already represented by `lem-weil-pbc-right-adjoint-preserves-limits`. It is a proof tool here, not a direct Mathlib leaf for the item, because the required internal extension-restriction adjunction is a project dependency.

Earlier logged searches are preserved as earlier searches. The unsuccessful directory grep, capped unrestricted grep and oddly parsed single-file grep are explicitly described in their records/report; no such result is used to establish absence. Fresh services succeeded, so no unavailable service is reported as a no-match result.

Searched the whole DAG for Tag 0038 and the restriction/right-adjoint/limit wording and searched the blueprint index with `Restriction of scalars`, `preserves limits`, and right-adjoint variants. The general theorem is reused. The umbrella `sk-def-sfb-change-of-scalars` includes this assertion as one of several clauses and cites this item in its proof, so it is not used circularly. Other preservation assertions have specialized sheaf coefficients or different functors; the restriction-colimit assertion has the opposite preservation conclusion and a coextension adjunction. No new node is needed. The item's `blueprint.same_as` is `[]`, and its imported `blueprint.from` remains null.

## Review by Q51

I compared the unchanged statement with the current item markdown and unit item 2. The extension situation assumes a braided monoidal category with coequalizers, colimit preservation by tensoring on both sides, a monoid morphism from a commutative source monoid, and internal module categories. The restriction definition uses the same monoid morphism and changes the action by composition. No closedness, coextension, abelianness or existence of all limits is assumed.

For step 1, I opened the complete statement of `def-sfb-modobj-extend-restrict-adjunction`. Despite its imported kind `definition`, its statement explicitly gives the natural Hom bijection and concludes the extension-restriction adjunction in the required direction. Its opening phrase refers to exactly the extension hypotheses already in force here. Step 1 uses that adjunction clause, not a claim buried in the node's proof. Its citation quotation is copied from that statement. This dependency is now a reviewed split in the shared DAG.

For step 2, I opened `lem-weil-pbc-right-adjoint-preserves-limits` and checked its first three sentences against Stacks Tag 0038, `categories.tex`, `lemma-adjoint-exact` (2), and the Mathlib declaration at line 207. They say exactly that the right-adjoint image of an existing limiting cone is limiting. Set its left category to R-module objects, its right category to S-module objects, its left functor to extension, and its right functor to restriction. The arbitrary diagram in step 2 takes values in S-module objects and its image takes values in R-module objects, as required. The quoted sentence is verbatim from the node's statement. No hypothesis of completeness, smallness of the ambient categories, or closedness is needed; the diagram shape is small, with arbitrary universe sizes. The two non-elementary statements in the argument are therefore precisely its two citations. Their union equals `proof_deps`.

For the small cases, an empty diagram gives preservation of an existing terminal object; a discrete pair gives preservation of an existing product cone; a parallel pair gives preservation of an existing equalizer cone. An identity monoid map gives identity restriction, consistent with all three. The proof never assumes a zero object or makes an elementwise argument in an arbitrary category. There are no new statements requiring separate counterexample tests.

For delivery-errors B, no new unsplit node, hollow object, vague statement or alleged new leaf is introduced; the cited general leaf has the checked declaration/file/line, and all actual searches retain their records. For C, both non-elementary facts are cited and each cited statement supplies exactly the fact used; neither source proofs nor the umbrella unit are borrowed as hidden lemmas. The finite dependency closure was checked for missing nodes, merged nodes and cycles. The general Mathlib leaf is declared as a tool in `split_report.tool_uses`; no maintainer-owned top-level `tool_uses` is installed. For D, the two steps apply a separately established adjunction and a general theorem, rather than moving the item's assertion into a new clause-node. For E, the morphism, coefficient categories, functor directions and inherited hypotheses match at both applications; preservation is kept distinct from limit existence. No SGA route is used.

## Remaining work

The mathematical split is complete. This worker runs only `deliver.py Q51 lem-sfb-modobj-restriction-preserves-limits --no-push`; the installed script accepts no trailing positional dot. A fresh second reader must inspect and deliver the accepted sandbox. No push is performed by this worker.

## Earlier dry-run tool blockage

The required command `python3 /home/ubuntu/weil-launcher-nt/deliver.py Q51 lem-sfb-modobj-restriction-preserves-limits --no-push` did not reach packaging or preflight. It remained in the shared worktree-slot acquisition loop for more than 15 minutes, with no child process or output. A read-only lock inspection showed all of its first 48 permitted slot locks occupied. I interrupted only this invocation after the prolonged wait; the resulting traceback confirms `/home/ubuntu/weil-launcher-all/sharedrepo.py:85`, `if _SLOT is None: _t.sleep(3)`, and exit status 130. No slot limit, lock or delivery-tool file was changed, and no push was attempted.

Thus this pass has no `OK` result and cannot be handed over as READY. The node, report, citations and actual search log are complete in this sandbox; the required dry run must be retried once shared tool capacity is available. Independent read-only validation passed for the unchanged statement, exact proof dependency union, both verbatim citations, and all 154 nodes in the item's statement/proof dependency closure (no missing/merged dependency or cycle).

## Retry review by Q51

On this retry I reopened the current chapter and scalar-change unit, the item and its companion proof, both cited node statements, and Stacks Tag 0038 (`categories-lemma-adjoint-exact`), part (2). The adjunction statement still has exactly the extension hypotheses, and the general preservation statement applies to the S-module diagram and R-module image in step 2. The shared item remains imported and has not been superseded by a reviewed split. The shared adjunction dependency is now reviewed; no dependency statement changed the argument.

I repeated the exact item-tag/name and conceptual searches in the completed project source; only ordinary-ring/sheaf restrictions and the general internal restriction construction appeared, with no project declaration proving this item. I read the reference master instance at ExtendScalars.lean:475–476 only as evidence for the route, not as an attachment. Fresh searches through msearch.py used LeanFinder, Loogle, LeanSearch and scoped Mathlib grep with the exact queries already recorded in the item. Their log is retained verbatim. The current LeanFinder result also includes `CategoryTheory.Mon.limit_X`, `CategoryTheory.Mod_.comap_obj_mod`, and `CategoryTheory.Mon.hasLimitsOfShape`; these concern monoid limits or the restriction construction, not this assertion. The ordinary-module preservation theorem and internal `comap` definition were read again at their source lines.

The whole-blueprint search for “Restriction of scalars preserves limits” found only this item. No new node or duplicate is introduced. Independent read-only validation on the current shared DAG passed: unchanged statement, exact proof-dependency union, both verbatim citations, every recorded query present in the actual search log, and all 154 reachable statement/proof dependencies with no missing or merged node and no cycle. The preceding Review by Q51 remains my mathematical check, including the small cases and B–E audit.

## Retry dry-run result

The required --no-push invocation again could not acquire a shared worktree slot. It waited 7.0 minutes without output or child processes; read-only /proc inspection confirmed all 48 slots in its configured default range were held and the invocation was sleeping in the acquisition loop. Combined with the earlier attempt's wait of over 15 minutes, this is a persistent shared delivery-tool capacity failure, not a preflight rejection. I interrupted only my own invocation (PID 3027104) using SIGINT; no slot configuration, lock, launcher, shared repository or other process was modified. No push occurred. The unchanged mathematical split and refreshed review remain in the sandbox for a later dry run and fresh second reader. READY is not claimed because no preflight OK was obtained.

## Final dry-run result

After the shared worktree slot became available, the required command
`python3 /home/ubuntu/weil-launcher-nt/deliver.py Q51 lem-sfb-modobj-restriction-preserves-limits --no-push`
completed successfully. It printed `OK (not pushed) ... preflight passed` (delivery commit
`68554685ba`). No push was performed.

## Second reading by Q51

- Item statement: checked against the blueprint node and `sk-def-sfb-change-of-scalars` item 2; the braided, coequalizer, tensor-colimit, commutative-source, and module-object hypotheses and the conclusion that `Res_\\varphi` preserves limits agree exactly.
- Step 1: checked against the companion proof and the complete statement of `def-sfb-modobj-extend-restrict-adjunction`; its adjunction clause supplies precisely `Ext_\\varphi \\dashv Res_\\varphi`, with no proof-only fact used.
- Step 2: checked against `lem-weil-pbc-right-adjoint-preserves-limits` and Stacks Tag 0038, `lemma-adjoint-exact` (2); an arbitrary small diagram and an existing limit cone are mapped to a limit cone in the correct module categories, without assuming existence of all limits.
- New nodes: none; consequently B1–B7 and duplicate/Mathlib-leaf checks introduce no new-node issues. The existing Mathlib leaf `lem-weil-pbc-right-adjoint-preserves-limits` was rechecked at `Mathlib/CategoryTheory/Adjunction/Limits.lean:207`, and the internal restriction theorem was not found in Mathlib or the project source.
- Edge cases checked: empty diagrams, discrete two-object diagrams, parallel-pair diagrams, the zero object when present, and an identity monoid morphism; each is consistent with the preservation statement.
- Changes made in this second reading: added this required audit section only; no mathematical or citation changes were needed. The two citation quotations remain verbatim statements of their cited nodes, and `proof_deps` is exactly the union of the two step dependency lists.
