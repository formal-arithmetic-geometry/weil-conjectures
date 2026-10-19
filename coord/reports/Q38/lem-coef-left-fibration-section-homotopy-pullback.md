# Q38 stage-1 worker report

## Files written

- `dag/nodes/sec-six-functors/lem-coef-left-fibration-section-homotopy-pullback.json`: the assigned statement, unchanged, split into five proof steps. Zero new nodes, zero Mathlib leaves.
- `citations.json`: twelve entries, one per node use in the five proof steps, with literal excerpts from the cited statements.
- `searches.jsonl`: twelve actual Mathlib searches made through the required msearch.py command; their exact query texts and returned log records are appended to the item's existing mathlib_searches with no-match verdicts.
- `write_split.py`: sandbox-only preparation script; not a delivery file.

Only the assigned sandbox was written. No Lean, compiler, Lake, local DAG checker, live-project write, git command, or agent was used. Required server checks and packaging are run through the supplied srvcheck.py/deliver.py wrappers.

## Attachments

None. The read-only slopmaster2 project was searched for the exact blueprint id and left-fibration/classification vocabulary under WeilConjectures. It contains no project declaration stating this complete theorem. The upstream master source was searched by exact item id only and was not treated as evidence of a proof. There was no lean_audit entry requiring an open-sorry attachment.

## Wanted sources

WANTED: archived Lurie, Higher Topos Theory, Lemma 2.1.3.3 (printed p.66), Theorem 2.2.1.2, Corollary 5.1.2.3 (printed p.319) and the proof of Lemma 5.5.4.13 (printed pp.479-480), for this item. The book was read online at https://people.math.harvard.edu/~lurie/papers/HTT.pdf; the node retains its existing URL source. The proof is marked proof_origin.by = agent because the document is not archived under literature/.

WANTED: archived Kerodon Corollary 4.4.3.8 (01NV), Proposition 3.4.0.7 (0329) and Construction 3.4.0.3 (010B), used to check the already existing right-fibration-space-fiber and pullback-path-comparison statements. All three were read online. These are Kerodon tags, not Stacks tags. There is no applicable Stacks theorem for this quasicategorical assertion, and no SGA source is used.

## Audit findings and corrections

The item is true as stated, and its statement, hypotheses, source, ancestry and statement dependencies were preserved. No STATEMENT-DISPUTED correction is needed. The original node had no argument; its reference to straightening alone did not explain the strict-pullback comparison. The split now isolates the exact reason it works: the comparison map f is a left fibration, so each map on strict vertex fibers is a Kan fibration. The ordinary vertex pullback is therefore a homotopy pullback. Coherent transport takes the entire cone, including both projections and the commutation homotopy, to the classified span. The general objectwise-limit theorem then proves the desired universal property in the functor category.

The apparent need for additional nodes was resolved by reading existing statements across the whole DAG. In particular, lem-coef-infinity-yoneda-presheaf-limits contains the GENERAL small-simplicial-set objectwise-limit clause, beyond its presheaf/ Yoneda title. It applies to arbitrary B, not only the nerve of a category or a quasicategory. Likewise lem-cbc-right-fibration-space-fiber already says the map lifts every horn when its base is Kan. Opposite-simplex reversal, written out in the proof, supplies the left-handed version without another node.

The assigned node is not a unit key node. I read the chapter record sec-six-functors, the unit record sk-prop-sf-biduality-general, the current main-20261015 proof of prop-coef-integral-exceptional-adjoint (paragraph 2) and the parent's use of this item in Step 3 of lem-coef-compact-relative-cocone-factorization. The inherited ancestry supplies a generic homotopical foundation beneath that mapping-complex infrastructure. No unit or chapter metadata was changed. Two generic cross-unit tools are proposed in split_report.tool_uses: right-fibration-space-fiber for the Kan upgrade, and enhanced-functor-cone-calculus for coherent uniqueness of limiting cones. Neither replaces a unit proof route; the maintainer decides acceptance.

## Not duplicates

No new nodes are proposed. Whole-DAG statement searches for left fibrations, Kan fibrations, pointwise limits, functor categories and 5.1.2.3 identified the existing tools reused here. Whole-blueprint searches for left fibration, pointwise limits, functor limits, 5.1.2.3 and homotopy pullback found no imported statement equivalent to this item. Its same_as remains empty. The existing isofibration-pullback-limit concerns Cat_infinity and requires a quasicategorical base; it was read but is not applied to arbitrary B. The present split does not create a duplicate of it or of the pointwise-limit theorem.

## Review by Q38

I checked the item against HTT's displayed pullback Y and homotopy-pullback sentence in Lemma 5.5.4.13, printed pp.479-480. The generic formulation has all the needed hypotheses: the base is any small simplicial set, p and p' are left fibrations, f is over the base and is itself a left fibration, and s is an actual section. The argument does not use a filteredness, nonemptiness, quasicategory, colimit, or compactness assumption on B. HTT Lemma 2.1.3.3 and Kerodon 01NV give the crucial Kan-fibration upgrade; Corollary 5.1.2.3, dualized, gives the objectwise criterion. Kerodon 0329 and 010B supply the strict-to-path comparison used in the proof. There are no new node statements to audit against additional sources.

For Step 1 I read the definition node's actual horn lifting property, including the convention 0 <= i < n. The filler against f, with lower simplex sv, explicitly produces the pair (v,w) in the pullback and preserves the whole supplied horn. Stability under pullback is proved directly here, rather than cited without a node. This step is elementary from that definition.

For Step 2 I read the full statement of lem-cbc-right-fibration-space-fiber: it requires a Kan base, concludes that the map lifts ALL horns, and allows empty fibers. I first apply it over the point, then apply it to f_t over the now-established Kan fiber of p'. Reversing dimension-n vertex labels takes horn i to horn n-i, so the existing right-handed conclusion supplies exactly the needed left-handed result. I did not cite a right-fibration definition as though it were the upgrade theorem, and did not assume B Kan. The maps f_t are genuine pullbacks of f along X'_t, because p'f=p. These are all the hypotheses needed at this step.

For Step 3 I read both statements being used: pullback-path-comparison assumes Kan input spaces and a Kan-fibration leg; kan-quillen-right-proper explicitly identifies a fibration-replaced ordinary pullback with the homotopy pullback of spaces. Step 2 supplies these hypotheses with the original f_t, so no replacement changes the actual projection. The map into the displayed path complex inserts the constant path, and hence retains the specified commutation homotopy and both projection maps. This is an argument about the canonical cone, not merely a weak equivalence of two apex spaces.

For Step 4 I read transport-classification's complete mapping-space, composition, constant-product and base-pullback clauses. They transport the WHOLE commuting square to a coherent cone on a, b, and identify its evaluations with the strict fiber cones. I then use the exact general clause of infinity-yoneda-presheaf-limits, which characterizes limit diagrams objectwise for any small simplicial set K. Its first clause says spaces have all small limits, satisfying the existence assumption for the finite span. This supplies the functor-category universal property without an uncited pointwise theorem or an invalid restriction to a quasicategorical B.

For Step 5 I checked the restriction isomorphism degree by degree: forgetting repeated base coordinates gives C times over u^*X' with u^*X, commutes with both projections and with successive pullbacks. Transport classification states compatibility with base pullback, and the objectwise theorem makes these restricted cones limiting. The definition node says limiting cones are terminal objects of the coherent cone category. The enhanced-functor-cone-calculus statement explicitly makes the full terminal-object subcategory contractible Kan, which provides coherent uniqueness as cones. Thus the final equivalence preserves projections and arbitrary base restrictions, including a coherent cocone parameter. Neither this conclusion nor the existence of pointwise limits is inferred from a definition node alone.

Small cases checked: B empty (its functor category and cone categories have the unique diagram); B a point (the theorem is the Kan-fibration strict/path-fiber comparison); f an identity (the section pullback is the terminal diagram); X empty (Y and every path fiber are empty); terminal fibers; and fibers containing several components. The Kan-fibration conclusions and comparison remain valid with empty fibers. I also tested the f hypothesis by dropping it: let B be a point, X a point, X' the Kan nerve of the groupoid with two isomorphic objects and a unique arrow between each pair, f include object 0, and s select object 1. The strict pullback is empty, while the homotopy fiber is contractible and nonempty. Thus merely assuming p,p' are left fibrations would be false; the actual statement correctly requires f itself to be one.

Against delivery-errors B-E: the item is self-contained with its defining notions cited; no statement-only new node carries a proof; no clause was moved to a relabelled helper; all non-elementary tools have cited nodes whose statements were opened; elementary base change and reversal are written out; no stronger hypothesis is inserted; and all twelve citation excerpts are literal substrings of the statements. A read-only traversal of the cited statement/proof closures reached 376 existing nodes and did not reach this item, so the citations create no cycle. No forbidden SGA route, target statement, or coefficient category was touched.

Mathlib checks used two semantic phrasings, two Loogle patterns and three source greps, through msearch.py only. I read the returned signatures and the relevant source at HasFibers.lean:165-191, Over/Pullback.lean:54-65, CategoryWithFibrations.lean:35-90 and the two simplicial-set PushoutProduct.lean files around line 70. The Grothendieck/Over/Bundle results concern ordinary categorical or dependent-type pullback. The Cech-nerve results construct a simplicial object in an ordinary category. The SSet results give strict limits or all-horn/inner-fibration exponentiation. None gives the classified coherent homotopy-pullback comparison here or its clauses by a one-line specialization. Every new record was copied from a query actually logged by msearch.py; all twelve additional searches returned successfully. The inherited search records were preserved.

## Unfinished work

No mathematical step or new node is left to finish in this one-level split. Independent second reading and delivery belong to the next worker; this worker runs only --no-push.

## Validation

The first server dry run failed at packaging: a stale origin base and unrelated generated coord/blueprint-index.tsv and coord/queue.md/tsv were included by the temporary-worktree wrapper. No such files exist in this sandbox. The required wrapper was retried without editing the shared repository. The wrapper retry printed OK (not pushed) at c5702c67ec: preflight passed. This report and the four continuation search records are included in the final confirmation dry run. No branch is pushed by this worker.

## Continuation review by Q38

I reopened all eight dependency statements and checked the twelve excerpts against the current DAG: every quote is verbatim and the entries cover exactly every step use. The current dependency closure has 376 nodes and does not reach the item. I reread HTT Lemma 2.1.3.3 (printed p.66), Lemma 5.5.4.13 (printed pp.479-480, the displayed Y square), and Corollary 5.1.2.3 (printed p.319), plus Kerodon 01NV, 0329 and 010B online. These confirm the Kan-base hypothesis in Step 2, the constant-path map in Step 3 and the arbitrary-simplicial-set base of Step 4. The current ancestor proof is literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-thm-sf-package/prop-coef-integral-exceptional-adjoint.proof.md, paragraph 2; its inherited unit metadata remains untouched. The strict reversal formulas in Step 2 and degreewise coordinate-forgetting in Step 5 give the needed elementary constructions explicitly. No mathematical repair or statement correction was needed.

I also repeated the project-source attachment search with the exact id and broader left/right-fibration, straightening and homotopy-pullback vocabulary in both permitted read-only checkouts. The only broad matches were unrelated homotopy-category sections. Whole-blueprint searches for left fibration and homotopy pullback again returned no equivalent imported node. Four fresh msearch.py queries (LeanFinder, Loogle, grep, LeanSearch) are recorded verbatim from their log in addition to the earlier eight; the ordinary model-category and Kan-extension hits were read and do not state this theorem.

## Second reading by Q38

- Item statement: checked against HTT Lemma 5.5.4.13, proof pp. 479–480 (the displayed pullback $Y$ and homotopy-pullback conclusion); all hypotheses and the generic section-pullback formulation agree, including the left-fibration hypothesis on $f$ and the projection and restriction clauses; verdict: pass.
- Step 1: checked the pullback horn calculation against [def-coef-infinity-fibrations]; the supplied lower simplex and lifted simplex give the required pair in $Y$, with no hidden fibrancy assumption on $B$; verdict: pass.
- Step 2: checked both uses of [lem-cbc-right-fibration-space-fiber] against its Kan-base and all-horn hypotheses, and checked the explicit opposite-simplex reversal; empty and nonempty fibers are covered; verdict: pass.
- Step 3: checked the strict fiber pullback and constant-path map against [lem-coef-kan-pullback-path-comparison] and [lem-coef-kan-quillen-right-proper]; Step 2 supplies Kan spaces and a Kan-fibration leg, and the actual projections are retained; verdict: pass.
- Step 4: checked whole-square transport against [lem-coef-space-transport-classification] and the arbitrary-small-simplicial-set objectwise criterion in [lem-coef-infinity-yoneda-presheaf-limits]; the pointwise path model and limiting-cone conclusion use exactly the cited clauses; verdict: pass.
- Step 5: checked degreewise base restriction, projection compatibility, and coherent uniqueness against [lem-coef-space-transport-classification], [lem-coef-infinity-yoneda-presheaf-limits], [def-cbc-enhanced-diagrams-cones], and [lem-cbc-enhanced-functor-cone-calculus]; verdict: pass.
- New nodes: none; no additional node statements require B1–B7 or duplicate searches.

I repaired the item node's `created` metadata: it incorrectly named `lem-coef-compact-relative-cocone-factorization` and group Q77, so it now names this item and Q38. No proof, statement, citation, or search record required mathematical changes. I retested the zero, terminal, empty, identity, and multi-component fiber cases and the counterexample obtained by dropping the hypothesis that $f$ is a left fibration; all give the reported verdicts. The required source and DAG dependency statements were reopened, and every citation quote remains a verbatim substring.
