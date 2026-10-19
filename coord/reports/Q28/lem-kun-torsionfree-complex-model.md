# Worker report: lem-kun-torsionfree-complex-model

## Files written

- dag/nodes/sec-smooth-purity/lem-kun-torsionfree-complex-model.json — existing statement, split into nine steps; no whole-item Mathlib match.
- citations.json — seven step/node citations with verbatim statement excerpts.
- report.md — this report. searches.jsonl is the search tool's own log.

There are **0 new nodes and 0 new Mathlib leaves**. The proof reuses five existing nodes, all Mathlib leaves. No unit record is changed: this item is an auxiliary node, not the unit's key statement.

## Attachments

None. Searches for the exact blueprint tag/id in WeilConjectures and for torsion-free, flat-complex, K-flat and bounded-representative terminology found no declaration stating this item. The generic project theorem CochainComplex.exists_quasiIso_flat_kFlat in WeilConjectures/CategoryTheory/DerivedCategory/FlatModel.lean supplies flat terms but no lower termwise bound. Its bounded resolution variant supplies an upper bound. Neither attaches this item. The etale/pro-etale bounded-flat-model theorems concern finite Tor intervals and different coefficient categories. No sorry declaration from master was counted as finished.

## WANTED

WANTED: literature/stacks-project/etale-cohomology.tex, Tag 0F0E (lemma-pull-out-constant), first model paragraph, for lem-kun-torsionfree-complex-model.

WANTED: literature/stacks-project/more-algebra.tex, Tags 0653 (lemma-last-one-flat) and 0AUW (lemma-dedekind-torsion-free-flat), for lem-kun-torsionfree-complex-model.

WANTED: literature/stacks-project/algebra.tex, Tag 00HD (lemma-flat), for lem-kun-torsionfree-complex-model.

The local literature checkout is absent in the shared repository. I read the official Stacks pages online at https://stacks.math.columbia.edu/tag/0F0E, https://stacks.math.columbia.edu/tag/0653, https://stacks.math.columbia.edu/tag/0AUW and https://stacks.math.columbia.edu/tag/00HD. I downloaded nothing and changed no literature files. The explicit construction is marked proof_origin.by = agent. The blueprint ancestor text was also read from the existing reference copy /home/ubuntu/work-bp/sheaf/literature/blueprint/master/blueprint/sec-smooth-purity/sk-prop-sf-kunneth-ordinary/lem-kun-0f0e.md.

## What was wrong and what changed

The item had an empty proof. Its statement is correct and is unchanged, including preservation of short exact sequences and the absence of any finite-generation assumption. Its source points to the model assertion in Stacks 0F0E and the truncation criterion 0653. The latter has bounded-above and finite-Tor-interval hypotheses; it cannot simply be applied to an arbitrary unbounded-above K-flat representative. I avoid assuming that missing applicability: a two-row construction proves the needed lower-bounded flat model directly, within the node-level freedom of SETUP.md. No unit/chapter proof step is replaced: this unit has no prescribed steps.

A complex of finite-support free groups F maps degreewise surjectively onto a lower-bounded representative C. The kernel G is torsion free term by term, and the cone of G -> F maps quasi-isomorphically to C. The formulas for the differential and the lifts of cycles prove that assertion directly. The existing PID-flatness and flat-tensor-exact leaves supply the only non-elementary algebraic inputs. This neither assumes subgroups of free groups are free nor asserts bounded-below flat models over arbitrary rings.

## Searches and reuse

Ran msearch.py for this item with two different LeanFinder phrasings, Loogle `CochainComplex, Module.Flat`, grep `flat|torsionFree|torsion_free` restricted to Algebra/Homology/DerivedCategory, and LeanSearch. Exact queries/results are appended to mathlib_searches and are in searches.jsonl. The first semantic result set consisted of derived support and representing-complex facts; the second additionally contained injective constructions. Reading the support and project flat-model sources confirmed that none gives both flat terms and a lower termwise bound. Loogle and grep returned no matches. LeanSearch returned Internal Server Error and is recorded unavailable. Earlier search records inherited from the item were preserved.

Searched the whole DAG and blueprint for flat resolution, flat model, torsion-free complex, torsion free, bounded below complex, and the relevant tags. Existing etale K-flat resolution nodes are sheaf-specific and do not supply the lower bound here. Existing bounded flat models need a finite Tor interval. Instead of creating a duplicate PID-flatness lemma, reused lem-weil-pbc-pid-torsion-free-module-flat. All five proof dependencies are existing Mathlib leaves, so no undeclared off-unit theorem is used. blueprint.from retains the exact general-K reduction in lem-kun-0f0e, and same_as is empty.

## What remains unfinished

No part of the stage-1 split. No Lean was written and no compiler, Lake or build was run. Delivery is left to the second reader after the accepted dry run.

## Review by Q28

I read the item, its parent lem-kun-0f0e, the chapter and unit records, the ancestor blueprint proof, and the four Stacks tags listed above. The source's purpose is precisely a lower-bounded torsion-free representative over the integers. The statement needs no properness, finiteness or finite Tor-interval hypothesis. The local-source absence is explicitly reported and the new proof is labelled agent-written, rather than presented as a transcription of an unavailable source.

Step 1 uses the exact D-plus union formula in def-weil-pbc-bounded-derived-subcategories and the explicit representing-complex equivalence in def-sbc-standard-tstructure-derived-category. I opened both statements: the second really gives a complex with zero TERMS below a, rather than merely cohomology vanishing. This avoids the common C4 error of citing only the definition of D-plus for termwise bounds.

Steps 2 and 3 are explicit constructions. A_n is set to zero BELOW a, not the free group on the underlying singleton of the zero group. This distinction is essential to the bound. Above a, evaluation on finite-support functions is surjective, and coordinate cancellation proves torsion-freeness without any subgroup-freeness theorem. The formula d_F(x,y)=(0,x) has target A_(n+1) direct sum A_n, so the indices and the chain-map equation both check.

Step 4 cites the actual cone formula in def-weil-abstract-derived-category. Its statement gives exactly F^n direct sum G^(n+1) with the displayed minus sign. q being a chain map ensures its kernel is a subcomplex. The bound is a-1, since G may contribute in that degree. No claim of a bound a is made.

Steps 5 and 6 do the full cohomology argument. For surjectivity I checked the sign in (f,-d_F f), including the second differential component. For injectivity, subtracting d_P(t,0) keeps g unchanged, leaves the first component in G, and the resulting element is exactly d_P(0,f_1). Thus this is not an uncited cone-quasi-isomorphism theorem. Step 6 cites only the definition of quasi-isomorphism, which is verbatim in the abstract-derived statement.

Step 7 uses the statement of lem-weil-pbc-pid-torsion-free-module-flat with R = Z. The statement has no finite-generation hypothesis and says torsion-free modules over every PID are flat; the direct-sum/subgroup cancellation verifies its hypothesis for each term of P. I checked its Mathlib match in RingTheory/Flat/TorsionFree.lean:93 against Stacks 0AUW(1). The elementary PID property of Z is justified by division with remainder in the proof.

During self-review I found that flatness in that leaf refers to preservation of injections, whereas the item explicitly requests short exact sequences. I added step 8 and read lem-weil-pbc-flat-tensor-exact in full. It states preservation of exact triples and of the left endpoint. Applying it also to V -> W -> 0 gives the right endpoint after tensoring zero. Its Mathlib declarations Module.Flat.lTensor_exact and rTensor_exact were read in RingTheory/Flat/Basic.lean:323,340, and the source Tag 00HD was opened. The step now uses the actual theorem, not merely a flatness definition. Step 9 uses localization's inversion of quasi-isomorphisms, explicitly stated in def-weil-abstract-derived-category, to finish the isomorphism.

For B1-B10 there is no new node to be underspecified, duplicate, unsearched or improperly attached; every retained notion is inline or already represented. For C1-C8 each non-elementary input is cited, the seven quotes were copied from the statements read, no dependency uses this item, and every cited node is a Mathlib leaf. For D1-D5 the actual construction and both cohomology calculations stay in this item's steps; there is no renamed child carrying its conclusion or hidden induction. For E1-E7 I checked the coefficients, every degree and sign, and the only ring-specific input (Z is a PID). Tested the zero object, a group Z/m in one degree, and complexes unbounded above with a fixed lower bound. Torsion in C is permitted: only F, G and P need be torsion free. For C = 0 the construction may give a nonzero acyclic model above the bound, which is allowed; no acyclicity of F alone is asserted. Shifting the lower bound changes only the indexing. No statement dispute or false small case remains.


## Second reading by Q28

- Item statement: checked against Stacks Tags 0F0E, 0653, 0AUW and 00HD and the current DAG dependencies, hypothesis by hypothesis; verdict pass.
- Step 1: checked the D-plus union and standard t-structure representative statements; verdict pass.
- Step 2: checked finite-support evaluation, surjectivity, and coordinate torsion cancellation, including zero groups; verdict pass.
- Step 3: checked the disk differential, chain-map identity, degree indexing, surjectivity, and lower bound; verdict pass.
- Step 4: checked the cone formula, differential-square expansion, kernel subcomplex, and bound $b=a-1$; verdict pass.
- Step 5: checked the explicit cycle lift and both differential components; verdict pass.
- Step 6: checked the boundary correction in degree $n-1$, the resulting kernel element, and quasi-isomorphism criterion; verdict pass.
- Step 7: checked torsion-freeness of kernels and direct sums and the PID argument for $\mathbf Z$, including the zero ideal; verdict pass.
- Step 8: checked all three exact triples and the tensor-zero endpoint to obtain preservation of short exact sequences; verdict pass.
- Step 9: checked localization sends the quasi-isomorphism to an isomorphism and the final composition has the stated direction; verdict pass.
- New nodes: none; the five dependencies are existing Mathlib leaves, and duplicate/blueprint/Mathlib searches were checked in the DAG and searches log; verdict pass.

Changes made: rebuilt against the current `origin/newtargets-dag`, re-read all five cited dependency statements and all seven citation quotes, and added this explicit second-reading section required by the delivery contract. No mathematical or node changes were needed.

## Earlier second reading (a previous round; superseded)

Independent reader, 2026-10-16. I opened the item, its parent `lem-kun-0f0e` (especially step 7), the unit and chapter JSON, all five dependency statements, and the official raw Stacks TeX at `https://raw.githubusercontent.com/stacks/stacks-project/master/etale-cohomology.tex` (`lemma-pull-out-constant`, Tag 0F0E), `more-algebra.tex` (`lemma-last-one-flat`, Tag 0653; `lemma-dedekind-torsion-free-flat`, Tag 0AUW), and `algebra.tex` (`lemma-flat`, Tag 00HD). The shared literature directory has no Stacks checkout, so the raw upstream files were read online without changing the shared repository. I also opened the Mathlib source declarations in `DerivedCategory/TStructure.lean:34–38`, `RingTheory/Flat/TorsionFree.lean:93–94`, and `RingTheory/Flat/Basic.lean:323–343`.

- Item statement: agrees with the bounded-below torsion-free-model assertion in 0F0E, over precisely the integers, without a finite-generation or upper-bound hypothesis; the flatness interpretation agrees with 0AUW(1) and 00HD. Its source also mentions 0653, whose bounded-above/finite-amplitude hypotheses do not justify this application directly; the agent-written proof does not invoke it. Verdict: pass, unchanged.
- Step 1: checked the union formula in `def-weil-pbc-bounded-derived-subcategories` and the strictly termwise bounded representing-complex clause of `def-sbc-standard-tstructure-derived-category`; the cited statements supply both the integer a and C. This is their direct specialization to abelian groups. Verdict: pass.
- Step 2: checked finite-support evaluation and torsion cancellation in each integer coordinate; a basis vector maps to every c, and setting A_n=0 below a avoids the nonzero free group on the zero group's singleton. These are explicit elementary arguments, with no freeness theorem used. Verdict: pass.
- Step 3: checked every degree: d_F maps A_n⊕A_(n−1) to A_(n+1)⊕A_n, its square is zero, and qd=dq follows from d_C²=0. Surjectivity and the bound follow immediately from step 2. Verdict: pass.
- Step 4: checked the exact cone statement in `def-weil-abstract-derived-category`, the restriction to ker q, the minus sign, and the bound a−1. Expanded d_P^(n+1)d_P^n into both components so the cancellation is displayed rather than implicit. Verdict: pass after clarification.
- Step 5: checked the cycle lift (f,−d_F f) against the differential formula; both components vanish and p sends it to c, so every cohomology class lifts. This is an elementary quotient-of-cycles argument. Verdict: pass.
- Step 6: checked the boundary correction in degree n−1; q(f−d_F t)=0, the remaining cycle equation says g=−d_G f_1, and d_P(0,f_1) is exactly the remaining pair. The definition of quasi-isomorphism in `def-weil-abstract-derived-category` then applies. Verdict: pass.
- Step 7: checked `lem-weil-pbc-pid-torsion-free-module-flat` against 0AUW(1) and Mathlib's Bezout-domain declaration; it has no finite-generation condition. A subgroup and a two-summand direct sum inherit torsion cancellation coordinatewise; the least-positive-generator argument supplies the PID property of Z (the zero ideal is generated by 0). Verdict: pass.
- Step 8: checked the exact-triple and left-endpoint clauses of `lem-weil-pbc-flat-tensor-exact` against 00HD and the actual lTensor_exact/rTensor_exact declarations; the three displayed triples respectively give the left, middle and right endpoints, using 0⊗P=0. No separate right-exactness theorem is silently needed. Verdict: pass.
- Step 9: checked localization at quasi-isomorphisms in `def-weil-abstract-derived-category`; Q(p) is invertible and composition with the step-1 isomorphism gives precisely Q(P)≅K, with b=a−1. Verdict: pass.
- New nodes: none. All five dependencies already exist and have status mathlib; there is no new elementary, duplicate, restated-clause or unsearched node, and no off-unit unfinished tool lemma. B1–B7 new-node cases are empty. The item's notions are inline or defined by its two statement dependencies. Verdict: pass.

Small cases checked independently: C=0 (a possibly nonzero acyclic P is allowed); C=Z/m in degree 0 or 1, including m=1 (torsion in C is allowed and is resolved by G); C=Q in one degree (no finite-generation assumption); and C with Z in every nonnegative degree and zero differential (no upper bound is introduced). The lower-bound edge n=a−1 permits G^a and n<a−1 forces both summands zero. A field or empty scheme is not a parameter of this integer-module statement. Zero modules in the flatness and exactness clauses cause no exception.

Independent Mathlib searches were run through msearch.py with the new query “Over a hereditary ring, every complex with cohomology bounded below admits a bounded below flat resolution” and the grep pattern `exists.*[Ff]lat|[Ff]lat.*exists|[Tt]orsion[Ff]ree` over Algebra/Homology. The eight semantic hits concern support, K-projectivity/injectivity, or resolutions of single objects; none supplies this model theorem. Grep returned zero hits. Both records were appended unchanged to searches.jsonl and their actual results added to the item. There are no new leaves. All seven step/node citation quotes were independently checked as verbatim substrings of the current cited statements, and the five dependencies do not cite the item.

Changes: expanded the cone differential-square calculation to show both components; updated proof provenance to record the independent raw-TeX reading; recorded two independent Mathlib searches and their verdicts; appended this second reading. The statement, route, nine-step structure, and citations are otherwise retained. The first worker's `## Review by Q28` remains above.

## Rebase repair audit

For the returned-delivery repair I compared the current DAG copies of every cited node with the versions read by the second reader: `def-weil-pbc-bounded-derived-subcategories`, `def-sbc-standard-tstructure-derived-category`, `def-weil-abstract-derived-category`, `lem-weil-pbc-pid-torsion-free-module-flat`, and `lem-weil-pbc-flat-tensor-exact`. Their statements and statuses are unchanged. I re-read the full statements and rechecked the quote entries in `citations.json`; the current abstract-derived-category statement still supplies both localization and the cone formula, while the two flatness leaves supply exactly the torsion-free implication and tensor exactness used. The split was adjusted in step 9 to spell out the direction of `Q(p)` and its composition with `Q(C) ≅ K`, eliminating any ambiguity in the final isomorphism. No dependency or hypothesis was added or removed.

## Source error

The raw 0F0E proof starts with vanishing for i≥a and j≥b while its hypotheses are D-plus. Those inequalities should be i<a and j<b for lower bounds: the complex with Z in every nonnegative degree and zero differential lies in D-plus but has no upper cohomology bound. Moreover 0653 explicitly assumes bounded above and finite Tor amplitude, so it cannot be directly applied to an arbitrary unbounded-above K-flat representative in that sentence. These source defects do not affect the item's correct model assertion; the explicit construction in steps 2–6 proves it without either faulty inference. No item statement correction is required.


## Current merge-lock return repair by Q28

The return reports a landing lock timeout, not a mathematical rejection. Its requested action is to rebuild the delivery on the current DAG, re-read every changed citation, and adjust before resubmission. I have re-read all five current dependency statements, not only the excerpts: D-plus supplies an existential lower cohomology bound, the standard-t-structure statement supplies a representative with a lower termwise bound, the derived-category statement supplies the cone differential and inversion of quasi-isomorphisms, the PID lemma supplies flatness without finite generation, and the exact-tensor lemma supplies all three exact triples. All seven existing citation quotes remain verbatim in these current statements. The item is still unsplit in the shared DAG; none of the five dependencies is merged away or depends on this item. All five currently have status mathlib. No new off-unit theorem or new node is needed.

For the source rereading I opened the official pages of Tags 0F0E (lemma-pull-out-constant), 0653 (lemma-last-one-flat), 0AUW (lemma-dedekind-torsion-free-flat), and 00HD (lemma-flat), as well as the stored ancestor blueprint text. The mismatch between D-plus and the displayed upper-vanishing inequalities in 0F0E, and the extra hypotheses of 0653, are still present. The explicit cone construction avoids those inferences. I re-read Mathlib's TStructure.t, flat_iff_torsion_eq_bot_of_isBezout and lTensor_exact/rTensor_exact, and the project's three flat-model declarations. The latter give an upper bound or require finite Tor amplitude; none is an attachment for this item. No compiler was invoked.

I checked steps 1 through 9 against these current statements and the explicit formulas. Step 1 directly specializes the two boundedness statements. Steps 2 and 3 verify evaluation, torsion cancellation, the disk differential and the map q. Step 4 uses the actual cone formula, with the negative kernel differential. Step 5 lifts cycles. For step 6 I expanded the missing displayed equality q(f-dt)=dc_0-dc_0=0 and specified that (0,f_1) lies in P^(n-1), so its boundary has the required degree. Step 7 now explicitly includes the zero ideal in the elementary verification that Z is a PID; coordinate cancellation still supplies torsion-freeness. Step 8 uses exactly the three exact triples in the cited statement. Step 9 now names both steps 7 and 8 when asserting the final flatness clause. These are actual changes to the split, with its statement and dependency list retained.

The small cases were rechecked: zero C is permitted to have a nonzero acyclic model; C=Z/2 in degree a may require P^(a-1) and shows why the construction uses b=a-1; C=Q requires no finite generation; and the zero-differential complex with Z in every degree at least a introduces no upper bound. At n<a-1 both cone summands vanish; at n=a-1 the kernel summand may remain. For arbitrary integer shifts the cycle and boundary calculations keep the same signs. Thus the non-elementary facts remain exactly the cited flatness leaves and representing-complex clause, rather than an uncited resolution theorem or a new child restating the item.

No direct git operation, shared-repository write, Lean edit, compiler or build is used. As required by this worker brief, only deliver.py --no-push packages the repaired sandbox on the current origin/newtargets-dag and runs preflight; the second reader performs any eventual push.

Current dependency file fingerprints at this reading (SHA-256; for the next reader to identify changes):

- def-weil-pbc-bounded-derived-subcategories: 5f312b22a4dd23f6bc1c9a18e6c971c84bfc1b6249909e612fa23a4cd51a18b2
- def-sbc-standard-tstructure-derived-category: ec2c32663171ace50d49f427ce35b89af77df1180574ae3028ab067b46ef80f5
- def-weil-abstract-derived-category: bee6e7c54dd139994552aac0e953292ff7ead57eda0b2371c8c505f80b36a0b1
- lem-weil-pbc-pid-torsion-free-module-flat: 99c5196b295d172d8c3beb8c2a1b77120ec6954c59fc983bc8f09e32e87c6622
- lem-weil-pbc-flat-tensor-exact: 95b917b32a0b2332656f2e3b1b7d29b33e703d115caf33b7ec3ed2942ea7cfe9
