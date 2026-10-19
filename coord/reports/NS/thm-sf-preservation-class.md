# thm-sf-preservation-class — stage 1 repair, NS

## Files written

- `dag/nodes/sec-six-functors/thm-sf-preservation-class.json`: statement node, status `split`, no Mathlib match. Five proof steps use nine existing dependencies after the second reading. This repair updates Steps 2–3 for the current chart corollary's omission of empty charts, retaining the original arbitrary-chart statement.
- `citations.json`: thirteen verbatim statements, one for every current step/dependency pair. The two excerpts from `cor-pur-general-admissibility-datum` were refreshed against its current statement.
- `report.md`: rewritten with the five required report sections in order, explicit source corrections, the NS review, and the repair record.
- `searches.jsonl`: inherited actual msearch output plus the fresh second reader's three independent searches. `dry-run.log` records the required preflight. There are **0 new nodes and 0 Mathlib leaves**.

The item realizes clause (iv) of `sk-prop-sf-rf-shriek-preservation`, not its entire four-clause statement. No unit realization file is changed. Chapter and unit texts remain untouched.

## Attachments

None. I searched `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/` by item id, blueprint tag and preservation declaration names and read the following actual statements:

- `AlgebraicGeometry.Etale.exists_constructibleTorAmplitudeIn_rightDerivedUpperShriek_of_topologicalKrullDim_le`, `WeilConjectures/SixFunctors/Etale/Derived/Stability/UpperShriek.lean:246`: its input is the combined constructible-and-Tor predicate, and its chart maximum is existential. It does not give the item's interval bound on arbitrary bounded constructible inputs without a Tor hypothesis, nor its prescribed arbitrary chart maximum and relative pro-étale interpretation.
- `AlgebraicGeometry.Etale.boundedConstructible_rightDerivedUpperShriek`, `UpperShriekConstructible.lean:164`: qualitative bounded constructibility, without the specified interval.
- `AlgebraicGeometry.Etale.torAmplitudeIn_preservation`, `Matrix.lean:220`: its exceptional-inverse-image entry uses the combined predicate and existential constant, not the full conjunction here.

Their docstrings do not enlarge their formal statements. No exact attachment is asserted, and no master sorry declaration is treated as a finished proof. No compiler or sorry-map regeneration was run.

## WANTED

None. The first worker's missing-source entry is resolved: the blueprint and Stacks sources are available read-only under `/home/ubuntu/weil-launcher-nt/literature/`. I read the original item, its unit, and `cor-pur-general-admissibility-datum.md` in `blueprint/master/blueprint/sec-six-functors/sk-prop-sf-rf-shriek-preservation/`. The source is agent-written blueprint material, so `proof_origin.by` remains `agent`. No literature was downloaded.

## Errors and corrections

The substantive imported statement errors are recorded under `## Source error` below. The earlier split already corrected the unrestricted ambient-adjoint assertion, the converse claim about étale origin, and undefined empty maxima; retained both numerical bounds and coefficient-stage uniformity; restored an explicit finite affine cover of Y and quantification of the Tor interval; and directly cited the statement's definitions.

This return says preparation for review failed with `[Errno 2] No such file or directory: '/home/ubuntu/weil-launcher-nt/blobcache/2f653a7f56ba61cb14e59d419ea4a0ff214f5cb7.tmp'`, and asks for the report sections listed in the brief. The report now has separate Files written, Attachments, WANTED, Errors and corrections, and Unfinished work sections, followed by the mathematical review. The stale WANTED paragraph and contradictory historical validation wording have been removed. The transient cache file belongs to the launcher, which I did not edit; the required supported dry-run invocation successfully got past that failure.

On rereading dependencies I found that the current chart corollary explicitly omits empty source charts. This item allows arbitrary chosen chart families. Steps 2–3 now apply the corollary to the nonempty charts with maximum D_0, calculate its upper endpoint, and use D_0 ≤ D to widen the lower endpoint to a−2D. This preserves the entire statement, including families containing empty charts. Both corollary quotes now copy its current statement verbatim. These are concrete sandbox repairs, not an unchanged rebase.

## Unfinished work

No remaining one-level split work. Existing cited results remain separate DAG items; this split uses their statements without certifying their proofs. The fresh second reading and delivery validation are recorded below. The first worker did not push. Only stage 1 was performed: no Lean file was written and no Lean/compiler/Lake/build tool was run.

## Source error

STATEMENT-DISPUTED: the original item and Proof Steps 1 and 4 upgrade the class-relative adjoint to the unrestricted ambient datum. The type check is explicit: `thm-sf-ambient-adjoint-class` supplies the Hom bijection for bounded-below K **of étale origin**, whereas `def-weil-ambient-exceptional-adjoint` and clause (1) of `def-weil-exceptional-adjoint-admissibility` quantify over every complex of ordinary pro-étale module sheaves. Restricting the first variable cannot establish the latter assertion. `cor-sf-ambient-adjoint-discharge` expressly excludes that unrestricted conclusion. Its recorded elliptic-curve counterexample is supporting context; the correction relies on the quantified domain mismatch, not on an unproved reconstruction of the counterexample.

The corrected statement uses the constructible functor `nu_X^* f^times R nu_{Y,*}` of `def-weil-exceptional-inverse-image`. It retains all four finite-stage conclusions, interpreting the final clause as the constructible analogues of admissibility clauses (2)–(3), exactly as the unit statement and the warning of the admissibility definition prescribe. It neither assumes nor concludes unrestricted ambient admissibility. This changes the faulty imported node formulation, not an immutable `nt-target-*` declaration or the unit/chapter statement. The present brief explicitly authorizes correction of ill-typed imported statements followed by continued splitting; the second reader/maintainer should confirm this recorded correction and handle any upward reporting.

STATEMENT-DISPUTED: the original claim that bounded constructible and finite-Tor inputs are “exactly the complexes of étale origin” is false. On Spec k, the infinite direct sum of copies of A is of étale origin but has an infinite degree-zero stalk, so is not constructible with finite stalks. `lem-sf-proetale-constructible-origin` identifies the two **bounded constructible** categories. The item now states the implication actually needed: bounded constructible inputs have étale origin, and finite-Tor inputs lie in that category.

The original maximum has no value for an empty chart family. The split sets D=0 for that family and treats empty X directly. If Y is empty then X is empty too, and e=0 avoids using the dimension of the empty scheme. No geometric nonemptiness hypothesis is added; for nonempty schemes the original endpoints remain unchanged.

## Searches and reuse

The original msearch log contains all ten recorded searches. Two LeanFinder phrasings returned scheme-morphism and general sheaf facts, not exceptional inverse-image interval preservation. The independent second-reading phrasing about a right adjoint to compact support returned ordinary pushforward-adjoint and condensed-module structures. Loogle `"shriek"` and `"upperShriek"` and the three recorded source grep patterns returned no hits. The first Loogle query's unknown-identifier response is recorded as an invalid query. LeanSearch's Internal Server Error is recorded `unavailable`, not as absence. No query or result was fabricated or added during this report repair; searches.jsonl remains the actual log.

I reran whole-blueprint preservation search and inspected the existing general-admissibility corollary. It already supplies the chart bounds used here, so creating a preservation or arithmetic child would duplicate it or create an elementary helper. The item retains `blueprint.is` equal to itself, `from=null` for an imported blueprint node, `same_as=[]`, and a `split_report.blueprint` mapping its steps to original Proof Steps 1–4 and unit proof (iv).

## Not duplicates

No new nodes. The affine-chart corollary is reused. Integer cancellation, widening of an interval, tensor-unit testing, finite-Tor membership, and quantifier instantiation remain proof steps. No clause of the item has been renamed as a child lemma.

## Review by NS

I read the worker brief, stage-1 rules, SETUP's three levels, GOAL, dag-sync and delivery-errors B–E. I read the item and unit in the available master blueprint, the six-functors chapter record, the original general-admissibility corollary, and every current proof-dependency statement. For the site comparison I opened Stacks `proetale.tex`, Tag 09AK / `lemma-compare-constructible`, and Tag 09AL / `lemma-compare-constructible-derived`, verifying both labels in `tags/tags`. They require a Noetherian coefficient ring, satisfied by the finite ring A, and support only the bounded constructible comparison used here. No new node requires a separate source audit.

Step 1: `def-weil-exceptional-inverse-image` is used only for its defining composite and domain, not its preservation paragraph that points back to this theorem. Clause (ii) of `lem-sf-proetale-constructible-origin` supplies bounded constructible étale origin. `def-weil-finite-tor-amplitude` places finite-Tor objects inside that category. `cor-sf-ambient-adjoint-discharge` supplies the relative adjoint and excludes the unrestricted ambient conclusion. I checked the same finite coefficient stage and sites throughout. The site-origin equivalence is the sole declared generic off-unit tool use; no lemma of this unit gives that comparison. The other existence interface follows the unit's cited route.

Step 2: the current statement of `cor-pur-general-admissibility-datum` introduces finite-type X,Y over the same algebraically closed finite field, separated finite-type f, the constructible exceptional functor, nonempty affine charts, c_U=2(d_U+dim Y), and the two interval conclusions. `def-pur-conventions` fixes exactly these finite coefficient categories. All these hypotheses occur in the item. The target's separatedness is retained. Restricting its chosen cover to nonempty U still covers nonempty X, so the corollary applies with D_0; no unmentioned open-complement or ambient datum is assumed. I refreshed the quotes after noticing the corollary's current wording. The corollary is already in this unit and packages the source's smooth/closed-immersion assembly.

Step 3: I checked the displayed cancellation with D_0, and a−2D ≤ a−2D_0. The cohomology and tensor-test vanishing implications follow by inclusion of the corresponding intervals. The tensor-unit test K tensor^L A ≅ K supplies the cohomological interval for a finite-Tor input; bounded constructibility plus the Tor bound then supplies finite-Tor membership by its cited definition. These are explicit elementary calculations, not an uncited preservation theorem. For an empty X, every site object is empty and its empty covering forces a module sheaf to be zero on every object. Hence all output complexes vanish and satisfy every interval. A morphism to empty Y forces X empty, covering the e=0 convention.

Step 4: I checked universal instantiation of `cor-pur-general-admissibility-datum` in the fixed-stage setting of `def-pur-conventions`. After retaining the fixed chosen charts, D_0, D and dim Y are geometric integers independent of n. The same cancellation and widening therefore hold at every stage. This conclusion is numerical uniformity; it requires no transition-map, integral-reconstruction or scalar-extension assertion.

Step 5: I read the actual formulas of admissibility clauses (2)–(3) and their warning. Substitution of −2D and 2e+1 gives exactly the constructible interval and finite-Tor conclusions already proved. `cor-sf-ambient-adjoint-discharge` expressly forbids inferring the stronger unrestricted datum. The final finite-stage consequence is preserved with that precise scope.

For B1–B10, there are no new unsplit proofs, no leaf claims without declarations, and no new definitions to duplicate. Objects and coefficient stages are introduced, definition references exist and are unmerged, and imported metadata is retained. For C1–C8, each non-elementary input is a cited current statement; all eleven quotes are verbatim; proof_deps equals the union of step uses; no proof's internal data are borrowed; and the only generic off-unit use is declared in split_report for maintainer review. For D1–D5, no new child restates a clause and the actual arithmetic, membership and uniformity arguments remain in this item. For E1–E7, I checked the finite-type/separatedness and coefficient hypotheses at Step 2, distinguished Tor and cohomological intervals, and recorded the two source-domain errors rather than silently weakening them.

Small cases: zero complexes; X empty with empty or nonempty chosen chart families; Y empty; identity on Spec k with d_U=D=0; a=b; negative a; a chart with d_U<D; coefficient stages n=1 and n>1; and smooth affine-space projections of relative dimension r. The identity's original interval lies inside the claimed enlarged interval, and the smooth shift −2r is allowed when D=r. Adding an empty chart with arbitrarily large d_U increases D and only widens the lower bound; deleting empty charts is therefore harmless by the explicit Step-3 inequality. For nonempty Y the output width is (b−a)+2D+2 dim Y+1 ≥ 0. No claim that bounded constructibility alone implies finite Tor amplitude is made for n>1.

## Earlier second reading (a previous round; superseded)

The sandbox's previous second reader had checked the same item/unit sources and all seven proof interfaces, restored the finite affine cover of Y and explicit a≤b in the Tor clause, and read the three candidate Lean declarations listed under Attachments. That reading also supplied the final independent Mathlib searches now retained in searches.jsonl. This section records that earlier reading's scope; the present returned repair is handed to a fresh second reader as required by the dispatcher, rather than claiming that the earlier signature approves these subsequent edits.

## Return-L repair and validation

The only return entry names the missing transient blobcache file and the report requirements. The report has now been structurally repaired, its missing-source status resolved, current corollary quotes refreshed, and the empty-chart interface handled explicitly in the proof. I did not write the live repository, the live launcher or any other worker's files. The delivery tool alone creates its authorized temporary review commit.

A durable retry before these final repairs printed `OK (not pushed) deliver/NS/thm-sf-preservation-class at 89bd6d2b8c: preflight passed`, demonstrating that the transient preparation failure did not recur. The final exact revision is subjected next to `python3 /home/ubuntu/weil-launcher-nt/deliver.py NS thm-sf-preservation-class --no-push`; its output is saved in `dry-run.log`. The installed parser accepts no trailing dot. Only a successful final dry run permits READY. No push is performed.

## Second reading by NS

Statement: read archived `thm-sf-preservation-class.md` (order 2085), `cor-pur-general-admissibility-datum.md` (2079), and the unit `_section.md`, clause/proof (iv), beside the current node. The finite field, separated finite-type target and morphism, fixed coefficient quotient, finite affine presentations, both interval bounds and stage uniformity agree. The recorded STATEMENT-DISPUTED corrections faithfully distinguish the relative constructible adjoint from the ill-typed unrestricted ambient assertion; the infinite-rank constant sheaf on Spec k refutes the asserted converse about étale origin. Empty maxima have explicit conventions, without removing an empty-scheme case. These corrections are necessary and retained.

Step 1: opened all four cited statements, the actual relative Hom formula in `thm-sf-ambient-adjoint-class`, Stacks 09AK / `proetale-lemma-compare-constructible` (`proetale.tex:5239`) and 09AL / `proetale-lemma-compare-constructible-derived` (`:5357`); verdict PASS: a finite coefficient ring is Noetherian, bounded constructible inputs have étale origin, and no unrestricted first-variable adjunction follows or is used. The definition's preservation paragraph pointing back to this item is not used.
Step 2: opened the current chart-corollary and conventions statements; verdict PASS: X,Y are finite type over the specified k, f is separated of finite type, n is positive, and the corollary already states both cohomological and Tor intervals and finite-Tor membership. For X nonempty the nonempty source charts form a nonempty finite cover, with D_0 at most the originally chosen D; the corollary is in this unit, rather than a newly invented preservation child.
Step 3: opened the finite-Tor, constructible-interval and small-pro-étale-site definition statements; verdict PASS after repair: cancellation gives c_0=2D_0+2e+1 and the upper endpoint b+2e+1, while a-2D is at most a-2D_0, so both vanishing conditions persist in the larger interval. Finite-Tor membership is already given by Step 2. On the empty scheme the empty cover makes every module-sheaf value zero, hence every output complex has the required bounds. Y empty forces X empty.
Step 4: checked the universal n quantifier and the corollary's formulas against the conventions; verdict PASS after repair: the cancellation and endpoint inequality are now written explicitly at each n. No coefficient-comparison map or compatibility theorem is inferred from numerical uniformity.
Step 5: opened admissibility clauses (2)–(3), their scope warning, and the discharge corollary; verdict PASS: substitution gives the two constructible preservation formulas, while the statement expressly avoids the stronger ambient datum.
New nodes: NONE; verdict PASS for B1–B10 and D1–D2, with zero new Mathlib leaves. No elementary arithmetic or restated clause was made a node. The existing chart-corollary supplies the exact required input, so no new preservation lemma is needed.

Independent reuse check: I read the three slopmaster2 declarations named in Attachments. The first and matrix entry assume the combined constructible/Tor predicate and existential D; the qualitative bounded-constructible theorem has no prescribed interval. None states the full item. My new LeanFinder query about uniformly bounded extraordinary inverse image over a finite torsion ring returned only eight generic derived-category t-structure declarations; Loogle `"extraordinary"` and Mathlib/AlgebraicGeometry grep `upperShriek|TorAmplitude|extraordinary|exceptional` returned zero hits. Their actual outputs were appended by msearch.py to searches.jsonl and the item metadata records them. No finished proof is inferred from an upstream sorry declaration, and no compiler was run.

Small cases checked independently: zero input; identity on Spec k with D=e=0, where [a,b] is contained in [a,b+1]; a=b and negative endpoints; X empty with either no charts or only empty charts; Y empty; adding an empty chart with larger embedding dimension, which only lowers the lower endpoint; n=1 and n>1, without asserting finite Tor for all constructible inputs. For a smooth affine-space projection of relative dimension r, the expected shift by -2r is contained in the displayed interval when D=r.

Changes made in this reading:

- Aligned the dimension-definition citation with the chart corollary's topological Krull dimension; this avoids silently invoking the equality with the local-ring formulation of scheme dimension and retains the source's intended bound.
- Added direct Step-3 citations of the interval and site definitions, so its vanishing and empty-cover arguments can be checked from cited statements.
- Removed the redundant tensor-unit detour for membership: Step 2 already supplies membership of the output in D^b_ctf.
- Replaced Step 4's reference to the same calculation with its cancellation and widening inequality at each stage.
- Expanded citation excerpts to complete current statements and added the two new definition citations: 13 exact quotes for 13 step/dependency pairs, with proof_deps equal to the nine-node union. Earlier excerpts were valid substrings; this is an auditability improvement, not a repaired false quotation.
- Appended this fresh reading while retaining `## Review by NS` and the prior review history; updated report counts and recorded three actual independent Mathlib searches. Statement and bounds were retained.

The installed delivery parser accepts only GROUP ITEM and optional --no-push; the literal trailing-dot command printed its usage and did not run preflight. Validation uses the documented accepted interface. The initial supported dry run queued behind the shared NS delivery lock; its exact result and final push are recorded below when available.

Final second-reader validation: the supported command `python3 /home/ubuntu/weil-launcher-nt/deliver.py NS thm-sf-preservation-class --no-push` exited 0 and printed `OK (not pushed) deliver/NS/thm-sf-preservation-class at e5f9184ee2: preflight passed`. This tested the repaired node and complete second reading after shared NS/fetch lock serialization. The authorized push follows through the same delivery tool and repeats preflight; no direct git command or live-repository edit was performed.
