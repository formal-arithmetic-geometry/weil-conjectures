## Worker report

Q14, stage 1, 2026-10-24. Read GOAL.md, the three blueprint levels in SETUP.md, the stage-1 brief, worker role, chapter/unit records, current blueprint, and delivery-errors B–E. No Lean was written, compiled, or built. No repository or launcher file was written and no direct git command was run.

Files written: `dag/nodes/sec-six-functors-basics/lem-sfb-weighted-composition-derivative-bound.json` (existing statement, now split), `citations.json`, `report.md`, and sandbox-only `write_split.py`. Search commands appended `searches.jsonl`. There was no earlier item copy, report, or search log in this sandbox. The item retains its statement, source, creation record, inherited searches, and blueprint ancestry.

## New nodes

None: 0 new nodes, 0 new Mathlib leaves. The three prerequisites already exist as Mathlib leaves: `lem-sfb-real-smooth-differentiation`, `lem-sfb-real-second-derivative-symmetry`, `lem-sfb-compact-continuous-norm-bound`.

## Attachments

None. Searched `lean/WeilConjectures/` by the blueprint id and weighted-composition vocabulary, then by `ContDiff`, `HasFDeriv`, and derivative-composition vocabulary. No declaration states the item. General project uses of “weighted” concern point counts or polynomial norms and are unrelated. A Mathlib result is not a project attachment.

## Sources and searches

WANTED: Demailly, `literature/demailly-hodge-ams.pdf`, Part I §3.A–3.B, inherited printed pp.11–13 (page attribution unverified), for lem-sfb-weighted-composition-derivative-bound. The file is absent locally. I do not assert that it states this formula or that I read it. This is an explicitly agent-written elementary analytic assembly from existing Mathlib leaves.

Read the current `literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md`, unit proof and direct-images proof. The latter's (3) supplies the inherited high-level direct-image route but does not state the analytic estimate. Read `lem-sfb-test-operations-continuous`: steps 2–4 require precisely arbitrary smooth matrix weights, compact source sets and the same derivative order, rather than diffeomorphisms or compact support. The unchanged item supplies all those hypotheses. The present proof stays below the inherited route and uses no SGA source.

Whole-DAG statement and declaration searches found the three existing leaves above. The Sobolev chart-overlap node uses a related induction but assumes additional chart/cutoff hypotheses and concludes a Sobolev estimate, so it is not a replacement for this item. Whole-blueprint searches with `tools/blueprint_refs.py search` for “chain rule”, “compact bounded”, “partial derivative”, “Leibniz”, “weighted composition”, “IsCompact”, “Frechet”, “continuous compact”, and “smooth functions” found no blueprint duplicate. `ancestor` prints that this inherited chain has `blueprint.from.node = None`. I retain that existing null and its via chain, and record the precise final supporting place rather than invent a blueprint ancestor.

Q14 Mathlib searches were run solely through the prescribed msearch command and their actual records are appended to the item's earlier searches. Read hits for `norm_iteratedFDeriv_comp_le'` (Bounds.lean:500), `norm_iteratedFDeriv_comp_le` (:513), and `norm_iteratedFDeriv_clm_apply` (:537): these bound pointwise iterated Frechet derivatives separately and do not directly state the compact coordinate-derivative weighted-composition estimate. Two semantic phrasings of the item found these pointwise estimates and distribution seminorm/structure maps, not a one-line specialization. The remaining searches confirmed existing component calculus leaves, so no new nodes were made. The grep confined to Topology had no hits for exists_bound_of_continuousOn; the successful semantic search locates it in Analysis/Normed/Group/Bounded.lean. No unavailable service was recorded as a mathematical absence.

## Problems found and corrections

The item was an unsplit statement with no argument, rather than a false statement. Its smoothness convention, all dimensions including zero, and the positive constant independent of f remain unchanged. I supplied the derivative-order induction and wrote every coefficient update explicitly; I did not create a new node restating the estimate. I also made mixed-partial commutation explicit, rather than silently sorting derivative words, and explained why the compact-bound node on all of Euclidean space applies to coefficients defined only on O: zero extensions are continuous on S locally, with no boundary regularity claimed. Boundedness of the f derivatives is proved on S via their compositions with g, so it does not presume differentiability on g(S). No statement dispute was found.

## Not duplicates

No new nodes. All three component facts are cited by their existing ids. No Stacks tag is relevant to these real calculus facts; exact Mathlib source declarations and lines supply their sources.

## Review by Q14

I reread the unchanged statement against its downstream use in `lem-sfb-test-operations-continuous` and its inherited, unavailable Demailly attribution. I read the actual statements of all three cited nodes, not just their names or proofs, and inspected their Mathlib signatures: ContDiffAt.comp (ContDiff/Comp.lean:223), ContDiffAt.fderiv_right (:724), ContDiffAt.add (Operations.lean:184), ContDiffAt.mul (:450), HasFDerivAt.comp (FDeriv/Comp.lean:105), HasFDerivAt.mul (Mul.lean:205), ContDiffAt.isSymmSndFDerivAt (Symmetric.lean:533) and its equality (:98), and the additive compact-bound declaration generated at Bounded.lean:96–100. These checks concern the existing leaves; no new-node sources need review.

Step 1 uses exactly the smooth-calculus leaf's sum/product/composition clauses and smooth-differential clause. Coordinate evaluation is a continuous linear map in finite dimensions, which the same statement covers. Matrix multiplication is the displayed finite scalar sum. Open domains ensure the differential rules apply at each point, with g(z) in P; no global smooth extension is used.

Step 2 uses the symmetry leaf's actual equality for real finite-dimensional C2 maps and the calculus leaf's differentiability and linear-composition rules. Applied to each already smooth derivative, it swaps adjacent coordinate derivatives. Repeated adjacent swaps give the stated multi-index reordering without assuming an unquoted higher-symmetry theorem. The relevant functions are smooth, hence C2, on their open domains, and all coordinate vectors belong to the stated finite-dimensional real spaces.

Step 3 uses the smooth-calculus leaf's actual product and chain formulas. The induction starts at c(0,0,a,b)=A(a,b). For alpha>0 it fixes i with alpha_i>0, applies the previous-order expansion, and the displayed recurrence accounts for both differentiating a coefficient and differentiating f through g. Reordering is step 2, not an additional unquoted result. Every term has f derivative order at most |alpha|, and coefficients depend only on A and g. This is the argument of the item itself, not an auxiliary node carrying its conclusion.

Step 4 uses the compact-bound leaf exactly with ambient R^d and scalar target R^1. The coefficient zero extension is continuous only on S, which is exactly what that node requires; it is not asserted continuous at boundary points outside O. The finite maxima include 1 and handle missing or empty coefficient families. Hence the chosen M is independent of f.

Step 5 again uses the compact-bound leaf, now with target R^q, and the smooth-calculus leaf to ensure continuity of the derivative compositions on S. This yields finite suprema on g(S) without needing a compact-image theorem as an uncited black box: the short open-cover argument is written. The scalar-coordinate versus vector-norm comparison is immediate from the Euclidean sum-of-squares formula. All hypotheses of both cited leaves hold on the given open domains and compact S.

Step 6 is elementary finite-sum arithmetic from the previous steps. The Euclidean triangle calculation gives the explicit factor r q N M, and C=1+r q N M is strictly positive even when one factor vanishes. Taking bounded suprema and finite maxima preserves the inequality.

Checked B1–B10: no new statement-only obligations, duplicates, missing new-node notions, unsourced Stacks tags or false Mathlib match. Checked C1–C8: every non-elementary input is among the three cited statements; no definition is used as an unstated theorem; no proof internals are borrowed; the citations.json quotes are verbatim full statements for every step citation; all three leaves are in the same unit and introduce no cycle. Checked D1–D5: the actual induction is in the item, with explicit base, recurrence and assembly; no relabelled clause node or hidden “standard” step. Checked E1–E7: no added global-extension, invertibility, injectivity, compact-support, nonempty-image or positive-dimension hypothesis. All steps are under 2000 characters.

Small cases checked mathematically: S empty (C=1); q=0 or r=0 (H identically zero); d=0 (only alpha=0); m=0 (only beta=0, chain sum empty); k=0 (ordinary weighted value bound); A=0; constant g; and the scalar first-order case, whose two terms are exactly A' f(g)+A f'(g)g'. None requires dividing by P_f, so f=0 and seminorm-zero cases are covered.

This direct-delivery review is my own reading, as authorized by the brief, not a claim of independent second-worker review. The maintainer will independently review the pushed result. No Lean work remains in this stage-1 item; required delivery checks follow.
