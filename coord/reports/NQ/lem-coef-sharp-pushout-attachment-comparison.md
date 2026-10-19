# Stage-1 delivery: lem-coef-sharp-pushout-attachment-comparison

## Worker report

Group NQ, direct-delivery worker, 2026-10-17. Only stage 1; no Lean edits, compilers, Lake, or builds. The shared project and the source checkouts were read only. There was no pre-existing item, split, report, citation file, or search log in this item's sandbox, only dispatcher marker files.

Files written:

- `dag/nodes/sec-six-functors/lem-coef-sharp-pushout-attachment-comparison.json`: existing statement node, now split into six steps; no Mathlib match for the full statement. Statement, statement dependencies, chapter, unit, source, ancestry and original search records retained.
- `citations.json`: eight literal statement quotations, one for each step/node citation.
- `report.md`: this report.
- `searches.jsonl`: written by the mandated msearch command. Every new search record in the node is copied from that command's actual log.

New nodes: none. New Mathlib leaves: none.

Attachments: none. Searches by the exact blueprint tag and by `sharp map`, `SharpMap`, `IsSharp`, and `sharpMap` in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/` found no declaration stating the item; the upstream name table has no corresponding declaration. No sorry declaration of master was treated as a proof.

WANTED: Charles Rezk, *Fibrations and homotopy colimits of simplicial sheaves*, https://rezk.web.illinois.edu/rezk-sharp-maps.pdf, especially Proposition 2.7, Proposition 3.7 and Lemma 8.3 (printed pp. 4, 6, 16), for lem-coef-sharp-pushout-attachment-comparison. No copy is archived under literature/. I read the author's PDF online. Following the brief's absent-archive rule, the expanded DAG argument is marked `proof_origin.by = agent`; no download or literature edit was made.

The original statement agrees with Lemma 8.3, including both alternatives in the monomorphism hypothesis, so no STATEMENT-DISPUTED correction is needed. The original proof list was empty. Its references to model structure, sharpness and colimits were appropriate statement dependencies, but those definitions alone would not justify left properness or distribution over the pushout. The split now cites the existing statements giving those inputs. Nothing mathematical remains unfinished at this one-level split; the cited unsplit nodes remain separate work items.

## Blueprint and duplicate searches

Read `dag/chapters/sec-six-functors.json`, `dag/units/sk-prop-sf-biduality-general.json`, the inherited ancestor's master text, and the current `main-20261015/blueprint/sec-six-functors/sk-thm-sf-package/prop-coef-integral-exceptional-adjoint.proof.md`. Both ancestor proofs retain the second-paragraph mapping-complex comparison. This item is a technical descendant of that comparison through the recorded completion/diagonal ancestry and the span gluing lemma. Its role is exactly Rezk Lemma 8.3 in the two span normalizations of Proposition 8.1(2); it changes no unit or chapter route. The unit record is not this item's key node and is untouched.

`tools/blueprint_refs.py ancestor lem-coef-sharp-pushout-attachment-comparison` identifies `prop-coef-integral-exceptional-adjoint`, matching the preserved ancestry. Whole-blueprint searches for `sharp`, `pushout`, and `weak equivalence` found no equivalent statement; `same_as` stays empty. Whole-DAG searches for universal weak equivalences, sharp/weak, Lemma 8.3, pushout attachments and left properness located the already-existing inputs, rather than new helper nodes. The source is Rezk, not a Stacks theorem; no invented Stacks tag or prohibited SGA route is cited.

## Mathlib searches

The old records were retained exactly. New searches were run using only `/home/ubuntu/weil-launcher-nt/msearch.py NQ lem-coef-sharp-pushout-attachment-comparison ...`, with the exact queries and results recorded in the node and searches.jsonl:

- LeanFinder: the sharp pushout attachment, then a second phrasing in terms of pullbacks of weak equivalences between sharp maps and cobase change.
- Loogle: `"SSet", "pullback"`.
- LeanSearch: `Rezk sharp map pushout attachment weak equivalence simplicial sets`.
- grep: `SharpMap|IsSharp|homotopy.?cartesian|Rezk` in AlgebraicTopology, and two generic pushout-stability patterns in ModelCategory.

The services were available. Loogle returned strict pullback/finiteness/fibration facts, not the sharp-map assertion. LeanFinder's first results are monomorphism closure, horns and strict pushouts. The second phrasing and LeanSearch give generic pushouts of trivial cofibrations. I read Mathlib's `AlgebraicTopology/ModelCategory/Instances.lean`, including its weak-equivalence cancellation lemmas, the fibrations-LLP identification, pushout stability and the pushout weak-equivalence instances, and `SimplicialSet/Monomorphisms.lean`. These support individual generic inputs but do not specialize in one line to the full attachment theorem. The matching generic lifting-closure fact already has `lem-coef-lifting-class-closure`, so no new Mathlib leaf was introduced. One grep against a single filename reports line numbers as its file column; it is retained as emitted, with no claimed new file/line attachment based on that output.

## Not duplicates

No new node pairs: this delivery creates zero nodes. It reuses `lem-coef-sharp-pullback-calculus`, `lem-coef-sset-pullback-preserves-colimits`, `lem-coef-sset-gluing-filtered-equivalences`, `lem-coef-kan-quillen-model-right-proper-core`, and `lem-coef-lifting-class-closure`. In particular neither universal base change of f nor sharpness of q was repackaged as a new node.

## Review by NQ

I read Rezk Lemma 8.3 and its entire proof on printed p. 16, with Proposition 2.7 and the distributive law Proposition 3.7. The imported statement has exactly its pushout, three sharpness hypotheses p, pf, qg, weak equivalence f, and disjunction that either i or f is mono. There is no unstated Kan, fibrancy, properness-of-a-map, or nonemptiness hypothesis. The model category used is the one on simplicial sets, not a different coefficient category. There are no new nodes whose statements or sources need a separate audit.

For step 1, I opened the full statement of `lem-coef-sharp-pullback-calculus`. Its comparison criterion is explicitly for a square over a sharp map, and its next sentence explicitly supplies arbitrary further base-change comparisons when both vertical maps are sharp. Here the lower map is the identity of A, the target sharp map is p, the source sharp map is pf, and the canonical comparison is the assumed weak equivalence f. Thus the node's statement itself, not a construction hidden in its proof, gives the required conclusion for every T to A. This fills Rezk's last sentence without creating a node that merely restates a clause.

Step 2 writes the actual comparison T = U times_B A and the mutually inverse coordinate formulas. The composite to B is hpf = qgif on X and hp = qj on X-prime, so these are the correct pullbacks. The formulas commute with all simplicial operators and intertwine f. This is only a two-line pullback identity following step 1 and is marked elementary; it does not assume arbitrary pullbacks preserve weak equivalences or that h is sharp.

For step 3, I opened `lem-coef-sset-pullback-preserves-colimits`. It states preservation for every small diagram in the slice over a fixed base, with colimits formed degreewise. The span over B has precisely those compatible structure maps, so its comparison is the needed pulled-back pushout. The mono assertion is justified separately by the degreewise injectivity argument in the step, not attributed to a colimit-definition node. U to B may be arbitrary, and the indexing span is small.

For step 4, I opened `lem-coef-sset-gluing-filtered-equivalences`. Its first paragraph requires monomorphisms in the designated first leg of BOTH spans and weak equivalences at all three components. Both legs here are the same i_U; the components are identity, identity, f_U. The first pushout is Y_U by its universal property and the second is Y-prime_U from step 3; the induced map is g_U. Thus every hypothesis holds even when f itself is not mono. The model-core node explicitly supplies the model structure in which identity maps are weak equivalences. I did not cite the gluing node for a one-sided mono condition it does not state.

For step 5, I opened both the model-core statement and `lem-coef-lifting-class-closure`. The core identifies cofibrations with degreewise injections. A mono weak equivalence is therefore a trivial cofibration and, by the model lifting/factorization axioms, is in the left orthogonal of the Kan fibrations. The lifting-closure statement explicitly includes closure of that left orthogonal under every existing pushout. Applying it to f_U, then using the same model identification in reverse, gives a weak equivalence g_U. This treats the other branch of the disjunction without assuming i mono and without silently appealing to left properness. The generic closure theorem is an existing Mathlib leaf, not a new helper equivalent to the item.

For step 6, the first iff in the calculus statement tests sharpness on ALL weak equivalences over B. Apply it first to qg, obtaining a_Y for an arbitrary weak equivalence a:U to V over B. The coordinate formula proves the commutation relation for g_U and g_V. The model-core's model axioms give composition and two-out-of-three, so the already established weak equivalences g_U and g_V imply a_Y-prime is a weak equivalence. The iff then applies to q. This elementary cancellation uses no invariance-of-homotopy-pullbacks lemma left uncited.

I checked the B--E return cases against the written files. B1--B7 introduce no new unsplit or leaf statement; the item remains self-contained with its definition dependencies and single-escaped TeX. B8 is respected by retaining the partial Mathlib hits as no match for this item. B9 ancestry and same_as were checked above, and B10 has no project attachment. C1--C4 are covered step by step by the eight literal quotations in citations.json; no step borrows a dependency's proof, or uses only a tag as a citation. C5 searches reused existing inputs; no new duplicate. C6 is left to the mandatory server DAG check as well. C7--C8 introduce no off-route statement: the non-Mathlib proof inputs are in this same unit, and lifting closure is already a Mathlib leaf. D1--D5: the six steps carry the actual argument and move no clause into a new node. E1--E6: the source/target maps, base A versus base B, both mono cases and the naturality formula were individually checked above. E7 found no source error in the statement or the argument specialized to simplicial sets.

Small cases: U empty gives empty pullbacks and identity maps; A empty forces X and X-prime empty, whence g identifies Y with Y-prime and the sharpness hypothesis on qg is precisely the conclusion. With f identity the pushout identifies g with the identity on Y. To distinguish the two branches, collapsing a face Delta^1 of Delta^2 to a point has i mono and f not mono, while taking X = Delta^1, X-prime = Delta^1 times Delta^1 with f the bottom-edge inclusion, and Y a point with the collapse i, has f mono and i not mono; over A = B = a point both fit the argument. Nothing excludes these cases or requires Kan objects. Empty test domains are retained in the final universal test.

All six steps have fewer than 800 characters. I checked each for a hidden sublemma: the only comparison is the coordinate pullback identity of step 2, written out; base-change comparison, pushout distribution, gluing, and lifting closure are actual cited statements. Corrections made during this review were to separate the two monomorphism cases explicitly and to replace a tacit homotopy-cartesian invariance argument at the end by the written two-out-of-three square. No statement changes or new nodes were needed.

## Validation

The required server-side review_split request was started before this report and is queued. The final deliver.py dry run and direct push are recorded by the delivery tool after this self-review.
