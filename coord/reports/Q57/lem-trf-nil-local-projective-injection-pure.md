# Worker report: lem-trf-nil-local-projective-injection-pure

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-nil-local-projective-injection-pure.json`: statement node, now split; no Mathlib match. Seven proof steps, with the original statement and ancestry preserved. Added the direct Stacks reference 05GP to the existing source list.
- `citations.json`: nine step/node entries with verbatim quotations from the cited statements. The tensor definition is quoted in full because its generating property, universal property, and functoriality are used at different places.
- `report.md`: this report.
- `searches.jsonl`: the six genuine wrapper searches made during this attempt, retaining their actual results.

No new nodes and no Mathlib leaves were created. The initial sandbox contained only dispatcher brief markers, so there was no earlier split or report to supersede. I copied the item and retained all its original search records, source information, and blueprint ancestry.

## Attachments

None. Searched the read-only slopmaster2 `WeilConjectures/` tree for the exact id and for projective/pure maps, then the RingTheory and LinearAlgebra trees for universal injectivity and nil maximal ideals. No project declaration states this item. The master source was also searched as reference only; its declarations were not used as finished evidence.

## WANTED

None. All mathematical sources needed for this split are present locally.

## Findings and changes

The statement is correct, including the absence of finite-generation, Noetherian, Artinian, or nilpotent-maximal-ideal hypotheses. It is the nil-local specialization of Stacks 05GP, `lemma-P-universally-injective`, which is the actual proof behind 05GQ (1) implies (2). The original source named 05GQ but omitted this intervening tag; I added it. There is no statement correction or statement dispute.

The original node had no proof. I supply the finite-source induction, including the retraction formula, rather than citing a new node that restates the result. For the arbitrary source, a tensor element uses only finitely many source basis vectors. Applying the finite-source retraction to this one element proves it zero. Neither tensor-colimit exactness nor the claim that the whole infinite-rank injection splits is used.

The item records a historical nearby-cycle/semistable-alteration ancestry below `lem-trf-local-term-locality`. I read its chapter and unit, the current main-20261015 unit statement, and retained that ancestry as historical supporting algebra. This delivery changes neither the unit nor its contracting-correspondence route. It cites no SGA source.

## Existing nodes and duplicate search

Before deciding whether a new node was needed, searched the whole DAG for 05GM, 05GN, 05GP, 05GQ, auto-associated rings, universal injectivity, nilpotent ideals, annihilators, and splitting maps. Used `tools/blueprint_refs.py ancestor` and whole-blueprint searches for `projective injective`, `nilpotent ideal`, `split injective`, `auto-associated`, `projective`, `projective modules`, and `universally injective`. No other blueprint node states the item. `blueprint.same_as` remains empty.

Reused `lem-trf-projective-over-local-free`, which explicitly covers arbitrary-rank projective modules, and the Mathlib leaf `lem-weil-pbc-local-ring-unit-criterion`. Reused the existing free-module and tensor-product definition nodes. The nearby residue-field criterion `lem-trf-local-universal-injective-residue` assumes residue-field injectivity, so it is not used to manufacture that missing hypothesis. The nilpotent-generated-ideal calculation and the coordinate kernel checks are elementary arguments written out in the proof, not new nodes.

## Not duplicates

No new-node/existing-node pairs: this delivery creates no nodes.

## Mathlib search results

The original search records were read and retained. Ran the mandated wrapper for LeanFinder, Loogle, LeanSearch, and grep, with a second semantic phrasing. All services were available. Exact queries and returned summaries are in `searches.jsonl` and appended without alteration to the item's `mathlib_searches` queries.

Read `Mathlib/RingTheory/LocalRing/Module.lean:329-365`, especially `IsLocalRing.split_injective_iff_lTensor_residueField_injective` at line 334. It assumes finite source and target, a free target, and injectivity after tensoring with the residue field in the relevant direction; it does not supply the missing implication from ordinary injectivity. The basis/freeness hits assume finite presentation or flatness. The invertible-module and flat-tensor hits constrain the tensor factor, whereas our factor T is arbitrary. Read `Mathlib/RingTheory/SimpleModule/InjectiveProjective.lean`; it assumes a semisimple ring and is unrelated to nil local rings in general.

The second grep passed a single file to the wrapper, whose output parser printed line numbers 33/334 as file names. The raw log and the result record preserve this exactly; the report and verdict identify the actual file and directly read declaration. This caused no ambiguity about the candidate and no tool was patched.

## Review by Q57

I read Stacks `more-algebra.tex`, Tags 05GM (`definition-auto-ass`), 05GN (`lemma-auto-ass-implies-P`), 05GP (`lemma-P-universally-injective`), and 05GQ (`lemma-P-fPD-zero`), including the following infinite-rank counterexample. The theorem in the item agrees with the (1) to (2) direction after the nil-local specialization. The local specialization of property (P) was checked directly: finitely many nilpotent generators give a nilpotent ideal by expanding products, and its last nonzero power has a nonzero element annihilating the ideal. No common exponent for the whole maximal ideal is inferred. I also read `algebra.tex` Tag 0593 (`theorem-projective-free-over-local-ring`) and Tag 00E9 (`lemma-characterize-local-ring`) for the reused tools. There are no new-node sources to review.

For step 1 I opened `lem-trf-projective-over-local-free` and verified that its statement has exactly the required local-ring and arbitrary-projective-module hypotheses. It gives bases for both P and Q, not merely finite projective freeness. I opened `def-weil-pbc-free-module` and used its unique finite basis expansions. The nonzero-ring observation uses only that a maximal ideal is proper.

Step 2 uses no node: the finite monomial pigeonhole argument and the choice of an element in the last nonzero ideal power are written out. The empty list uses 1; this is nonzero because A has a maximal ideal. This is a few-line elementary specialization, not an uncited invocation of 05GN or of a theorem about weakly associated primes.

For step 3 I checked the basis statement again and opened `lem-weil-pbc-local-ring-unit-criterion`: it says precisely that a coefficient outside the unique maximal ideal has a multiplicative inverse. Applying step 2 to the finite first-column support gives a nonzero kernel vector if all coefficients lie in the maximal ideal. The induction is quantified over every free target, so changing the target during its step is legitimate. The base rank zero is explicit.

Step 4 uses only the free-basis definition and the earlier induction setup. I checked that H is the span of the original basis vectors other than the pivot vector q_b0, since lambda is a nonzero unit multiple of that coordinate; it is not an unsupported assertion that a general submodule is free. I substituted the definition of pi to verify the displayed kernel relation and used source-coordinate independence to prove w injective. Thus the induction hypothesis applies with rank n-1 and this free H, even when the original target is infinite.

Step 5 uses that same basis definition. I evaluated the retraction formula on v(e_1) and each v(e_i) separately. Its first coordinate subtracts the off-diagonal coefficients c_i; omitting that subtraction would not give a left inverse. These explicit evaluations complete the inductive construction, rather than citing an external splitting theorem.

For step 6 I opened `def-weil-pbc-module-tensor-product`: its statement says that elementary tensors generate, gives the bilinear universal property and functoriality, and so supplies exactly the tensor operations taken here. The free-module definition supplies finite support of every p_k. I checked that j_E is injective, that u j_E is injective by the item's hypothesis, and that the already proved finite-source induction applies with target Q free. Applying 1 tensor r_E to the displayed zero element proves z_E=0 without assuming injectivity of 1 tensor j_E. This avoids both an implicit flatness assumption on T and an uncited colimit theorem.

Step 7 uses the tensor universal property from the same definition. The factor-switching maps are given on generators, and their composites and the required square commute on generators. This proves the right-tensor residue-field clause as well as the left-tensor conclusion of step 6.

For B--E I checked self-contained objects and hypotheses, verbatim citation content, acyclicity of the used existing tools relative to this item, the absence of new restatements, and the elementary status of the written coordinate calculations. All seven steps are below 2000 characters. The only externally used non-elementary algebraic tools are the explicitly cited local-projective-freeness theorem and local-unit criterion. The rank induction is the item's argument, with its invariant, base, reduction, and retraction formula all present.

The small cases checked were rank zero and empty basis support; n=1, where s has zero target and the formula reduces to lambda; a field (maximal ideal zero); dual numbers k[epsilon]/(epsilon^2), where multiplication by epsilon is not injective and cannot furnish a false pivot; and a local ring with nil but nonnilpotent maximal ideal, such as k[x_1,x_2,...]/(x_i^2). In the last case only finitely many coefficients are used at a time. Stacks' infinite-rank map e_i to f_i-x_i f_{i+1} illustrates why the proof concludes purity without asserting a global retraction. No hypothesis was added in any of these checks.

Corrections made during this review: supplied 05GP in the source, wrote the full complementary-map kernel calculation and off-diagonal retraction correction, and made the final tensor-factor switch explicit. No outstanding mathematical gap was found.

## Unfinished work

None in the stage-1 split. No Lean was written and no compiler, Lake, or build tool was run. Required server dry run and delivery follow this report.
