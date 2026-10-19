# Stage-1 repair: thm-weil-pbc-qbar-idempotent-complete

## Files written

- `dag/nodes/sec-smooth-purity/thm-weil-pbc-qbar-idempotent-complete.json`: five-step split; exact imported statement preserved. Added the explicit additivity calculation for the quasi-inverse and refreshed `split_report` against current cited statements.
- `citations.json`: twelve verbatim current statement excerpts covering every step/node use; retained after rereading each.
- `dependency-snapshot.json`: current full statements, statuses and SHA-256 hashes for the nine proof dependencies, for the next reader; sandbox evidence only.
- `report.md`: this repair review replaces the previous rounds' accumulated reports and stale dry-run claims.

Zero new nodes and zero new Mathlib leaves. No whole-item Mathlib match.

## Attachments

None. Read-only slopmaster2 searches for the exact item tag and qbar/idempotent/Karoubi vocabulary find no declaration of this particular coefficient pair-category theorem with both clauses. The generic bounded-t-structure and Karoubi-envelope results do not instantiate the required completeness of this pair category without further input. The current item's slopmaster2 audit is `none`. Upstream master, especially any sorry declaration, is reference material only.

## WANTED

None. I read the complete original blueprint node at `/home/ubuntu/work-bp/sheaf/literature/blueprint/master/blueprint/sec-smooth-purity/sk-prop-sf-cbc/thm-weil-pbc-qbar-idempotent-complete.md`. Preserved `sources/homology.tex`, `sources/derived.tex` and `sources/balmer-schlichting.txt` in this sandbox supply the actual source passages. No document was downloaded.

## Return repaired

The mathematical delivery had been approved; landing failed because another item held `coord/.merge.lock` for 120 seconds. The requested repair is to rebuild on the current DAG and reread changed citations. I reread all nine current directly cited statements, including filtered retract descent and the Karoubi full-faithfulness lemma, rather than rely on an old approval. The former still supplies precisely the finite-stage splitting conclusion needed in step 1; the latter is now a Mathlib leaf and still states precisely the canonical full faithfulness needed in step 2. All twelve quotes remain literal substrings of the current statements. The new snapshot records exactly what was inspected; I do not infer a historical byte comparison from an unavailable older snapshot.

This repair also adds the explicit additivity verification of G to step 4 and replaces the obsolete report/history. The supported `deliver.py ... --no-push` command constructs a fresh commit on current `origin/newtargets-dag`, preserving maintainer-owned fields; this is the authorized rebase mechanism. No direct git command was run. This worker leaves the repaired sandbox for a fresh second reader and does not push.

The inherited request to compile is superseded by the explicit human stage-1-only instruction: no Lean, compiler, Lake or build tool was run. No agent was started, and no shared/live-project, Lean-source or launcher file was written.

## Import faults, statement and route

The original one-paragraph proof omitted explicit step citations for full faithfulness and canonical exactness. The retained five-step split names those inputs and the actual Verdier triangulation, expands the envelope isomorphism, and constructs the equivalence data directly. Every non-elementary fact is a cited statement. The item still states both idempotent completeness and the exact equivalence of the canonical inclusion.

No STATEMENT-DISPUTED was found. The category is the raw rational finite-stage pair category, not an envelope substituted into its definition. Its scheme hypotheses are noetherian, finite-dimensional, with ell invertible, and finite stages are finite-dimensional extensions of Q_l in the chosen algebraic closure. No global finite-field hypothesis is added. Definitions, target statements, unit route and maintainer-owned fields are unchanged.

I read the chapter and `sk-prop-sf-cbc` unit records. This is auxiliary coefficient-category work, not the unit's key base-change statement; its recorded proof-step list is empty. No unit realization record is changed. The three cross-unit generic tools remain requested in `split_report.tool_uses`, as in the imported route: finite-stage Karoubianity, full faithfulness of the envelope inclusion, and triangulation of the envelope. No top-level approval is asserted. The full-faithfulness input is independently a current Mathlib leaf.

## Existing-node and Mathlib checks

The whole-blueprint search `idempotent complete` returns eleven records. The nearby `lem-weil-qbar-idempotent-complete` concerns the global finite-field datum and the separate rationalization interface, and supplies no identification with this general-T pair category. It is not substituted here. The stronger same-unit triangulation theorem depends on this item and cannot be cited as an input. `blueprint.is` remains this imported item, `from` remains null and `same_as=[]`.

All eleven inherited search entries match actual tool/query entries of `searches.jsonl`; no unrun query is added. Earlier semantic phrasings and Loogle/source searches found conditional Karoubi equivalences and complex-category infrastructure, not the whole theorem. LeanSearch's actual Internal Server Error remains recorded as `unavailable`. The general `toKaroubi_isEquivalence`/`toKaroubiEquivalence` inputs assume idempotent completeness and do not establish the pair category's completeness or its exact triangulated structure. Thus no whole-item leaf or attachment is claimed. There are no new nodes requiring new searches.

## Not duplicates

No new nodes. All nine existing inputs are reused; no elementary helper or clause of this item has been moved into a child.

## Review by N2

I reread the brief, delivery-errors B–E, stage-1 rules, SETUP's three levels, GOAL.md, coord/dag-sync.md, the chapter/unit records, the original blueprint and every cited statement. The blueprint proof is agent-written, so `proof_origin.by=agent` remains appropriate. For source conventions I read Stacks homology labels `definition-karoubian`, `lemma-karoubian` and `lemma-projectors-have-images` (Tags 09SG, 09SH, 05QV). They supply criteria, not a theorem about filtered coefficient categories. Balmer–Schlichting Definition 1.2 and Remark 1.4 give the envelope and full faithfulness; Theorem 1.5 and Definition 1.10/Theorem 1.12 give its exact inclusion and retract triangulation. There is no new node whose source needs a separate review.

Step 1 uses `def-weil-pbc-qbar-category` and `def-weil-pbc-finite-stage-pair-category` for the actual raw rational categories and scheme/coefficient hypotheses. `thm-weil-pbc-finite-stage-karoubian` states completeness of exactly these finite stages, not an envelope of them. This discharges exactly the assumption of `prop-weil-filtered-retract-descent`, whose statement says both that every idempotent splits and that a splitting is represented over one finite field. The step uses that stated conclusion. It does not assume an arbitrary representative already satisfies its idempotent equation.

Step 2 uses `thm-weil-pbc-verdier-axioms`, whose statement explicitly gives ordinary triangulation, hence additivity of this category. The functor is exactly the inclusion defined by `def-weil-karoubi-envelope`, and `lem-weil-karoubi-envelope-fully-faithful` applies to an additive category. No hypothesis or notion is borrowed from a theorem's proof.

Step 3 is a direct calculation using `def-weil-karoubi-envelope`: for a splitting p i=id and i p=e, e i=i and p e=p give the two morphism conditions. The two composites are id_S and e; e is the envelope object's identity. Thus the exhibited maps really are inverses. This calculation needs no new lemma.

Step 4 uses the same envelope definition and already obtained splittings. From u=d u e one gets d u=u=u e. Inserting i_R p_R=d proves the composition law for G(u)=p_R u i_Q; p_Q i_Q=id proves its identity law. Trivial splittings on J(X) give GJ=id. The i_Q and p_Q are mutually inverse and natural, and their images give the triangle identities. The new displayed distributivity formula proves additivity of G and its preservation of zero. Ordinary classical choice only chooses existing splittings. These elementary equations construct the equivalence itself rather than cite an unstated equivalence criterion.

Step 5 uses the exact actual common-stage triangulation stated by `thm-weil-pbc-verdier-axioms`. Applying `lem-weil-karoubi-envelope-triangulated` to it gives the envelope shift, retract triangulation and exact canonical inclusion. `def-weil-triangulated-category` states the shift-compatible distinguished-triangle meaning of exactness. This is the same inclusion proved an equivalence in step 4. The source's Balmer–Schlichting result supplies this input; none of the Stacks tags is misrepresented as constructing an envelope.

For E I tested identity and zero projectors, diag(1,0) on a direct sum, and the zero-category/empty-scheme case. With trivial splitting for identity projectors, and the zero object splitting the zero projector, every displayed inverse, identity, composition and additivity equation holds. The finite-stage index set contains Q_l; there is no empty-index assumption. No countable product/coproduct existence, coefficient comparison theorem or scalar-extension compatibility absent from the cited statements is needed.

For B the exact imported statement, TeX, blueprint data and sources are preserved; there is no new statement-only/Mathlib leaf subject. For C every non-elementary input is a cited statement, with each hypothesis checked above, all twelve pairs have literal quotes, and `proof_deps` equals the union of uses. For D no new node relabels the parent, and the detailed envelope/equivalence equations remain in the parent proof. For E the object, projector identity and coefficient category are those actually stated; no source error was found.

## Validation and unfinished work

The direct generic `check_dag.py` invocation reports inherited global dependency/reach/route errors outside this item. The direct `review_split.py` invocation fails before reviewing: its `head_version` tries to make `/home/ubuntu/weil-nt-live-dag/nodes/...` relative to `/home/ubuntu/weil-newtargets-shared`. I did not alter that script or work around its hardcoded path. The required delivery wrapper uses its own temporary overlay and runs maintainer preflight against its baseline; its result is the handover criterion.

The first fresh dry-run invocation was queued at the delivery lock; I stopped only that invocation to finish the sandbox edits before validation. The final repaired dry run is captured in `repair-current-dry-run.log`. Historical logs from earlier attempts are not evidence for this repair. No mathematical work remains beyond the fresh second reader's review and delivery. Nothing is pushed by this worker.


## Earlier second reading (a previous round; superseded)

I independently read delivery-errors B–E, GOAL.md, coord/dag-sync.md, the stage-1 contract, the chapter/unit records, the original blueprint theorem and all nine current cited node statements. The blueprint theorem at `/home/ubuntu/work-bp/sheaf/literature/blueprint/master/blueprint/sec-smooth-purity/sk-prop-sf-cbc/thm-weil-pbc-qbar-idempotent-complete.md` has exactly the delivered statement, including both completeness and exact equivalence. Its definition dependency supplies the prime, algebraic closure, noetherian finite-dimensional scheme and invertibility hypotheses; neither a finite-field base nor an already completed pair category has been substituted. No statement dispute was found.

- Step 1: checked the four cited statements, including the raw-stage definition and the conditional statement of filtered retract descent; every finite intermediate extension satisfies the finite-stage theorem, so descent gives exactly the two splitting equations and completeness. PASS.
- Step 2: checked the actual Verdier theorem's ordinary triangulation conclusion and the full-faithfulness node's additive-category hypothesis; also read Mathlib `Karoubi.lean` lines 139–149, where the same inclusion and its fully faithful structure are defined. PASS.
- Step 3: checked Balmer–Schlichting Definition 1.2 and the cited envelope definition; the equations e i=i and p e=p give both morphism conditions, and the composites are respectively identity and e, the latter being Q's envelope identity. PASS, elementary.
- Step 4: checked all formulas against the same envelope definition and the splittings already obtained: identity, composition (inserting i_R p_R=d), both naturality equations, normalized identity splittings, triangle identities, addition and zero. Expanded the absorption equations and inverse naturality explicitly. PASS, elementary equations and choice of existing splittings.
- Step 5: checked the particular common-stage triangulation in the cited Verdier statement, the full statement of the envelope triangulation node, Balmer–Schlichting Theorem 1.5 and Definition 1.10/Theorem 1.12, and the cited definition of exactness; these give the stated shift, retract triangles and exactness of the same canonical functor proved an equivalence. PASS.
- New nodes: none; there is no helper, clause restatement, duplicate or new Mathlib leaf to retain, remove or check under B1–B7.

I read the retained `sources/homology.tex` at `definition-karoubian`, `lemma-karoubian` and `lemma-projectors-have-images`, and `sources/derived.tex` at `lemma-projectors-have-images-triangulated` and `definition-exact-functor-triangulated-categories`. The project's `literature/stacks-tags-cited.tsv` identifies the first four as Tags 09SG, 09SH, 05QV and 05QW. These give criteria under their stated hypotheses; none is misused as a filtered coefficient-category or Karoubi-envelope construction. Balmer–Schlichting supplies that construction and its triangulation. In particular no countable product or coproduct hypothesis is assumed here.

Small cases checked: e=1 gives the chosen trivial splitting and GJ=id; e=0 splits through the zero object with both envelope composites zero; e=diag(1,0) splits by the first inclusion and projection. For the empty scheme the zero category satisfies the same equations. The coefficient-stage poset includes Q_l and is therefore nonempty. No scalar-extension functor needs to be faithful to apply the cited descent statement.

The whole-DAG search for idempotent-complete Qbar categories found the existing `lem-weil-qbar-idempotent-complete`, the bounded-t-structure theorem and the later same-unit triangulation theorem. The first concerns the global finite-field/framework datum, the second needs a bounded t-structure not supplied at this step, and the last depends on this item; none replaces this proof. The direct slopmaster2 node-id/qbar-idempotent search produced no exact attachment; the `ClosedImmersionStages` Karoubi rational stage is a different category. Upstream master was used only as reference, with no sorry declaration treated as proved.

My independent Loogle query `CategoryTheory.Idempotents.toKaroubi, CategoryTheory.Functor.EssSurj` returned `CategoryTheory.Idempotents.instEssSurjKaroubiToKaroubiOfIsIdempotentComplete`. I read its source at `Mathlib/CategoryTheory/Idempotents/Karoubi.lean` lines 222–240: it assumes the input category is idempotent complete and thus does not finish the whole item. The exact result is in searches.jsonl and its partial-match verdict is now in the item's search record.

Changes made: expanded d u=u and u e=u using the two projector equations, and wrote the inverse-counit naturality equation instead of leaving it implicit; recorded the fresh Loogle result and this independent reading. The first worker's sections, including `## Review by N2`, remain in place. All twelve citation quotes remain literal current statement substrings and cover exactly the proof's uses; proof_deps is their union. Zero new nodes, zero new Mathlib leaves. The three generic cross-unit inputs remain requested as tools only in split_report, for maintainer review.

Required fresh dry run: `python3 /home/ubuntu/weil-launcher-nt/deliver.py N2 thm-weil-pbc-qbar-idempotent-complete --no-push` exited 0 and printed `OK (not pushed) deliver/N2/thm-weil-pbc-qbar-idempotent-complete at 8ff9a5feb8: preflight passed`. The command waited for the shared fetch lock and then succeeded without a workaround. This is the validation for this independent second reading. No Lean, compiler, Lake or build tool was run.


## Second reading by N2

Fresh independent reading on 2026-10-16, after the preceding round. I read delivery-errors B–E, GOAL.md, coord/dag-sync.md, the stage-1 contract, the chapter/unit records, the original blueprint theorem and all nine currently cited node statements. The theorem's statement agrees verbatim with the blueprint, with both conclusions preserved. Its definition introduces a noetherian finite-dimensional scheme with ell invertible, a prime and its chosen algebraic closure, and the raw rational finite-stage pair category. No finite-field-base hypothesis or formal completion is substituted. No STATEMENT-DISPUTED arises.

- Step 1: compared all four cited statements and the blueprint Proof's first sentence; finite-stage completeness is precisely the hypothesis of filtered retract descent, which supplies actual splittings and their finite-stage representation. PASS; no representative is assumed idempotent before descent.
- Step 2: compared the envelope definition, the actual Verdier theorem and the fully-faithful leaf; the Verdier conclusion gives additivity, and the cited leaf concerns exactly X mapped to (X,id), as Mathlib Karoubi.lean lines 139–149 confirms. PASS.
- Step 3: compared the envelope definition and Balmer–Schlichting Definition 1.2; e i=i and p e=p verify morphism conditions, and the two composites are id_S and e, the latter the envelope identity. PASS, elementary equations.
- Step 4: checked each formula against the same definition and step 1's splitting equations; d u=u=u e proves the functor laws, i_R p_R=d gives composition, the two displayed naturality equations give the counit and inverse, and normalized identity splittings give the unit and triangle identities. Addition and zero follow by bilinearity. PASS, explicit elementary equations and choice of existing splittings.
- Step 5: compared the precise common-stage triangulation in the Verdier theorem, the entire envelope-triangulation statement and the definition of exact functor; Balmer–Schlichting Theorem 1.5, Definition 1.10 and Theorem 1.12 give this retract triangulation and exact canonical inclusion. PASS; the inclusion is the equivalence constructed in step 4.
- New nodes: none. B1–B7 and the elementary/duplicate/clause-restatement tests introduce no node to repair or remove; all nine dependencies already exist.

Source checks: the retained sandbox sources/homology.tex at definition-karoubian, lemma-karoubian and lemma-projectors-have-images are Tags 09SG, 09SH and 05QV, as the repository's stacks-tags-cited.tsv confirms. The retained sources/derived.tex at lemma-projectors-have-images-triangulated is Tag 05QW, and definition-exact-functor-triangulated-categories is Tag 014V. These are criteria and definitions, not assertions about this coefficient category or an envelope construction. I read the retained Balmer–Schlichting text at Definitions 1.1/1.2, Remark 1.4, Theorem 1.5, Definition 1.10 and Theorem 1.12 for the actual construction and triangulation. The shared tree does not physically contain literature/stacks-project, so the sandbox's retained .tex files are the source passages read; no missing-source download is claimed.

Small cases: identity projectors use the trivial splitting; the zero projector splits through the zero object; diag(1,0) splits by the first summand inclusion/projection. In each case the functor and counit formulas give the stated composites. For the empty scheme they reduce to the zero-category equations. The coefficient index contains Q_l, so the argument never needs an empty filtered diagram. All coefficient/scheme hypotheses in step 1 remain in force through step 5; the proof uses neither countable products nor coproducts.

Reuse/search check: the whole-blueprint search for “idempotent complete” and the DAG tag/keyword search recover the separate global-finite-field coefficient lemma, the bounded-t-structure theorem, and the later same-unit triangulation theorem. Their respective different category, extra t-structure input, or dependency on this item prevents substituting them here. Read-only slopmaster2 and upstream-master searches by item id and qbar/idempotent vocabulary find no exact attachment; master is reference material only. My independent msearch.py Loogle query `"toKaroubiEquivalence"` returned exactly CategoryTheory.Idempotents.toKaroubiEquivalence and CategoryTheory.Idempotents.toKaroubiEquivalence_functor_additive. I read their declarations and the surrounding instance at Karoubi.lean lines 222–243: they assume IsIdempotentComplete C, so they are a partial match and do not make the whole item a Mathlib leaf. The actual query/results are retained in searches.jsonl and the item's search record.

Changes: no mathematical statement or proof step needed repair. Added this fresh review and the independent actual Loogle result, and refreshed the sandbox-only dependency snapshot. Preserved every earlier section, including ## Review by N2. All twelve step/node quotes are still literal current-statement excerpts, cover exactly the uses, and their union equals proof_deps. A read-only traversal found no cycle among 2,197 available closure nodes; it also encountered two inherited missing ids (def-weil-pbc-etale-morphism and lem-weil-pbc-category-colimit), neither a direct citation of this split. The required delivery wrapper's preflight remains the scoped acceptance check. Zero new nodes, zero new Mathlib leaves. No agent, Lean write, compiler, Lake, build, direct git command, shared-tree edit or launcher edit was used.

Fresh validation and delivery results follow below; earlier-round dry-run commit hashes above are historical evidence only.

Fresh required dry run: `python3 /home/ubuntu/weil-launcher-nt/deliver.py N2 thm-weil-pbc-qbar-idempotent-complete --no-push` exited 0: `OK (not pushed) deliver/N2/thm-weil-pbc-qbar-idempotent-complete at 6739a8d5d0: preflight passed`. No failure or workaround occurred. This is the dry run for the fresh reading above.
