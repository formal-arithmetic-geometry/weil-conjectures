# Q13: lem-coef-presheaf-cylinder-model-recognition

## Files written

- `dag/nodes/sec-six-functors/lem-coef-presheaf-cylinder-model-recognition.json`: unchanged statement, now split into 13 argument steps; no Mathlib match.
- `dag/nodes/sec-six-functors/lem-coef-presheaf-naive-fibration-whitehead.json`: new statement-only lemma; no Mathlib match.
- `dag/nodes/sec-six-functors/lem-coef-presheaf-weak-mono-bounded-enlargement.json`: new statement-only lemma; no Mathlib match.
- `citations.json`: 16 verbatim quotations, one for every step/node citation.

The three never-delivered helper files of the earlier sandbox attempt were removed. They are replaced by two smaller inputs, rather than added to the DAG. Existing provenance (`created.item`, group Q65) of the assigned item is retained: that records its original creation by the Joyal-model worker, not the worker now splitting it.

## Attachments

None. Searches of `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` for the exact blueprint tag and item id, cylinder/model recognition, Cisinski, anodyne, and naive-fibration terminology found no declaration stating the item or either new lemma. No upstream-master sorry declaration is treated as a finished proof.

## WANTED:

WANTED: D.-C. Cisinski, *Higher Categories and Homotopical Algebra*, `https://cisinski.app.uni-regensburg.de/CatLR.pdf`, Example 2.1.11 and Section 2.4, especially Lemmas 2.4.28 and 2.4.38, for the item and both new nodes. I read these portions online; this document is not archived in `literature/`. The item's proof origin is therefore agent-written. No Stacks tag states the exact-interval recognition theorem or these interval-specific lemmas; no irrelevant Stacks tag is substituted for their actual source.

## What was wrong or changed

The assigned repository item is unsplit. Its statement is correct and retained byte-for-byte. The earlier sandbox attempt was not a valid split:

1. Its representable-boundary generator is false for arbitrary small categories. For a nontrivial group G, presheaves on BG are G-sets and the representable is the regular free G-set. Its only subobjects are empty and itself. Pushouts, transfinite compositions and retracts of those boundary inclusions starting at the empty set produce free G-sets. Thus the inclusion of the empty G-set into a one-point trivial G-set is missed. Cisinski Example 2.1.11 instead uses subobjects of **quotients** of representables. Step 1 writes the correct element filtration directly; no replacement generator node is needed.
2. The perfect-weak-equivalence recognition node requires closure under all filtered colimits. The prior accessibility helper only provided lambda-filtered colimits. Those hypotheses do not agree. I removed that recognition application, rather than silently strengthening a helper. The current proof follows Cisinski's own lifting and bounded-subobject construction of both weak factorization systems.
3. The old interval-properties helper bundled most of the result's work into an unsplit node, and its accessibility helper was not self-contained. Both are removed. The new nodes introduce all their own category, interval, anodyne and test-class data and have statements only.
4. I found a stray non-JSON `PYTEST` line in the inherited `searches.jsonl` and removed only that line. All genuine search records were retained. New searches were run through the prescribed command; their exact queries and actual responses are recorded. Loogle identifier errors are reported as errors/no useful match, not successful mathematical absence evidence. LeanFinder, LeanSearch and grep supply the actual concept searches.

No statement of the repository item was corrected or weakened. The counterexample concerns only a never-delivered helper in the prior sandbox. No STATEMENT-DISPUTED applies to the assigned statement. No SGA source is used. No unit, chapter or live repository file is changed.

## What remains

The two new lemmas are intentionally unsplit: the Whitehead lemma (Cisinski 2.4.28) and the uniform bounded-enlargement lemma (2.4.38). They will be independent subsequent stage-1 items. No Lean work is part of this delivery.

## Not duplicates

- lem-coef-presheaf-naive-fibration-whitehead vs lem-coef-presheaf-cylinder-model-recognition: the new lemma proves a lifting criterion only for naive fibrations with naive fibrant codomain; it asserts no model structure, generating sets, arbitrary fibrations or weak factorization systems.
- lem-coef-presheaf-naive-fibration-whitehead vs lem-coef-kan-quillen-right-proper: the latter concerns the already given Kan-Quillen simplicial-set structure; the new lemma concerns arbitrary set-valued presheaves and interval/anodyne input, with no model structure.
- lem-coef-presheaf-weak-mono-bounded-enlargement vs lem-coef-presheaf-cylinder-model-recognition: bounded enlargement is a uniform local size assertion about subpresheaves of one weak monomorphism. It is not a clause of the model-structure statement. Steps 8-11 still prove saturation, set generation and both lifting systems.
- lem-coef-presheaf-weak-mono-bounded-enlargement vs lem-coef-accessible-intersection-generators: that existing lemma assumes an accessible arrow class and gives a generating set; the new lemma assumes interval/anodyne data and gives bounded subobjects, without assuming accessibility or asserting a generating set.
- lem-coef-presheaf-weak-mono-bounded-enlargement vs lem-coef-simplicial-small-chunks: the latter is about finite/coherent diagram chunks in simplicial sets, not intersections of uniformly bounded subpresheaves inside interval-tested weak monomorphisms.

## Review by Q13

I read the worker brief, delivery-errors B-E in full, the three levels in SETUP, stage 1, GOAL, dag-sync, the six-functors chapter and biduality unit, the current ancestor node and its blueprint provenance. I searched the whole DAG and whole blueprint for the new statements, their source places 2.4.28/2.4.38, quotient-representable generation, naive fibrations, interval homotopy and bounded subpresheaves. There is no existing blueprint statement giving either new lemma. Their blueprint ancestry includes the assigned item followed by its original via list. The new nodes inherit the chapter and unit and do not change the unit route: they supply the generic interval-recognition input before the existing Joyal specialization.

I read Cisinski Example 2.1.11, Lemma 2.4.24, Proposition 2.4.25, Lemma 2.4.28, Corollary 2.4.29, Proposition 2.4.30, Corollary 2.4.31, Lemmas 2.4.37-2.4.39 and the end of the proof of 2.4.19 online. The two new statements are exactly the smaller source lemmas in this product-cylinder setting. For the size lemma, choosing alpha above the size of A makes total-element size equivalent to the source's category-of-elements size. No regular-cardinal assumption or preservation of all filtered colimits is inferred from it. The difficult bounded-subobject existence assertion is explicitly a new unsplit lemma, not hidden behind an elementary step.

Step 1 uses the presheaf presentability leaf for the ambient locally presentable category and small colimits, and the well-ordering/recursion leaves for the filtration. The missing completeness and Hom-smallness are written objectwise. The quotient representable and union/pushout descriptions are explicit, including the free-versus-nonfree orbit counterexample above. Step 2 uses the actual accessible-small-object theorem statement for factorizations; it does not take WFS equality from a theorem that supplies only a factorization. It proves the two lifting equalities and retract characterization itself, using precisely the lifting-closure and transfinite-left-lifting statements. I checked the direction of the diagonal and its two arrow maps.

Steps 3-5 use only the input definitions and explicit filling arguments: the three-face inclusion is e0 square (delta times K); delta square a extends a homotopy across an anodyne map; and a map lifting against all monomorphisms has a section and an over-base homotopy of section-composite to identity. These steps prove the closure and anodyne facts formerly bundled into the old helper. Step 6 uses the new Whitehead lemma only after checking that q is naive fibrant, has naive fibrant codomain, and is in W by two-out-of-three. It obtains anodyne recognition with fibrant codomain by an explicit arrow retract.

Step 7 derives the left-lifting characterization D = left-perp(N_f) using the already proved steps. In the converse I explicitly included TWO diagonals: the lift against i gives d:L to T, then the lift against the anodyne j gives r:L' to T with pr=1. This second diagonal is necessary for the claimed retract of k; d alone has the wrong domain. It also proves monicity of i, rather than assuming it merely because it is in a left lifting class. Step 8 uses the lifting-closure and transfinite-left-lifting statements with exactly the same right class N_f to establish weak saturation.

Step 9 uses the new bounded-enlargement lemma at the residual inclusion H into Y; this residual is weak by the induction invariant and two-out-of-three. The subpresheaf generated by the chosen element is bounded because alpha exceeds the size of Mor(A). The pushout is H into H union V. Well-ordering and recursion are the cited statements that authorize the continuous construction, and coding bounded presheaves by subsets/functions proves the chosen generators form a set. Step 10 applies the same small-object theorem to that set and invokes the same lifting closure statements; it obtains the second WFS, rather than citing the result being proved.

Step 11 uses the exact arrow-retract closure statement to identify the intersection of fibrations with W; all four retraction equations are written. Step 12 simply assembles the model axioms from the two constructed systems. Step 13 checks both directions of fibrancy using D = left-perp(N_f); the terminal presheaf is naive fibrant, so the codomain condition is satisfied. Smallness is tracked in the same input universe throughout, including the testing objects.

I tested the new statements and steps on the empty category A, the empty presheaf, a one-object nontrivial group category, isomorphisms, identities, empty generating sets when compatible with the interval axioms, and the maximal choice An = all monomorphisms. An empty generating set is not assumed compatible with the endpoint hypotheses in a nontrivial presheaf category. No argument assumes a nonempty source or target, an ordering on A, or freeness of element-generated subpresheaves. New nodes have no proofs or proof dependencies; neither is elementary, a duplicate, or a restatement of a model-structure clause. The item statement remains unchanged, and the only changes are in the sandbox.

Validation: the required `python3 /home/ubuntu/weil-launcher-nt/deliver.py Q13 lem-coef-presheaf-cylinder-model-recognition --no-push .` printed `OK (not pushed)` at commit 7de73b8236, with server preflight passed. The final report update is checked by one further no-push run. No delivery was pushed; the sandbox is left for the second reader.

## Second reading by Q13

- Item statement: checked the interval, endpoint, anodyne, homotopy-class, universe, and model-structure clauses against Cisinski Section 2.4 and the cited definitions; verdict: retained unchanged.
- Step 1: checked the presheaf ambient category, quotient-of-representable element filtration, objectwise pushouts, limit stages, and small coding against Example 2.1.11 and the three cited DAG statements; verdict: argument retained and reclassified non-elementary because the generation proof is substantive.
- Step 2: checked both small-object factorizations, the lifting-closure directions, transfinite closure, retract argument, and the definitions of (C,R_0,N); verdict: dependencies and orientations agree.
- Step 3: checked the three-face filler and the endpoint restrictions against Lemma 2.4.24 and the endpoint/anodyne hypotheses; verdict: elementary direct argument.
- Step 4: checked extension, injectivity, two-out-of-three, and retract closure of interval tests against Proposition 2.4.25; verdict: elementary direct argument.
- Step 5: checked the section and over-base homotopy obtained from (delta\times X), including the endpoint maps; verdict: elementary direct argument.
- Step 6: checked the factorization orientation (i=qj), fibrant-codomain hypothesis for the Whitehead node, and the arrow-retract maps; verdict: cited statement supplies exactly the needed criterion.
- Step 7: checked both directions of (D={}^\square N_f), the fibrant replacement of (L), both diagonals in the converse, and monicity recovery; verdict: argument and hypotheses agree.
- Step 8: checked weak saturation of (D) from the lifting classes and transfinite composites; verdict: cited closure statements suffice.
- Step 9: checked the bounded-enlargement application to (H\hookrightarrow Y), generated-subpresheaf size bound, pushout successor, limit unions, and set coding; verdict: hypotheses and induction invariant agree.
- Step 10: checked the second small-object factorization and its right class (J^\square); verdict: dependencies match the stated weak factorization system.
- Step 11: checked (R_0=F\cap W_I), factorization orientation, lifting square, and both retract equations; verdict: correct.
- Step 12: checked assembly of finite limits/colimits, two-out-of-three, retract closure, and both functorial weak factorization systems; verdict: exactly the item conclusion.
- Step 13: checked both fibrancy implications and the fixed input universe; verdict: terminal presheaf and (D={}^\square N_f) are used with the required directions.
- New node `lem-coef-presheaf-naive-fibration-whitehead`: checked self-contained (A, \mathcal P, I, \mathrm{An}, W_I) definitions and the Lemma 2.4.28 source place; verdict: strictly smaller statement-only input, retained.
- New node `lem-coef-presheaf-weak-mono-bounded-enlargement`: checked the monomorphism, cardinal, size, intersection, and uniformity clauses against Lemma 2.4.38 and its predecessor; verdict: strictly smaller statement-only input, retained.

Changes made in this second reading: corrected Step 1's elementary flag to `false` because its quotient-representable generation and universe-coding argument is a substantive lemma; retained the two statement-only helper nodes and all verbatim citation records; added this per-step and per-node audit. The inherited stray non-JSON search line remains removed, and no source, unit, or live repository file was changed.
