# Q66: lem-coef-dgcat-model-structure

## Files written

- `dag/nodes/sec-six-functors/lem-coef-dgcat-model-structure.json`: item, split into twelve argument steps; its statement and hypotheses are preserved.
- `dag/nodes/sec-six-functors/lem-coef-dgcat-free-cell-calculus.json`: new statement-only lemma; no Mathlib match. Free presentations, filtered colimits and the explicit arrow-word filtration, rather than a model-structure conclusion.
- `dag/nodes/sec-six-functors/lem-coef-dgcat-equivalence-cell-calculus.json`: new statement-only lemma; no Mathlib match. The explicitly presented coherent equivalence cell, its realization, a single-cell pushout calculation and prescribed-data lifting.
- `dag/nodes/sec-six-functors/lem-coef-projective-complex-cell-calculus.json`: new statement-only lemma; no Mathlib match. General unbounded complexes over a commutative ring, including the projective cell and tensor calculus.
- `citations.json`: one verbatim statement quote for each of the 22 step/node pairs.

## Attachments

None. Searches in the read-only project sources by the blueprint tag and by dg-category/model/quasi-equivalence terminology did not find a project declaration giving the item. Neither upstream sorry declarations nor generic Mathlib model-category declarations are treated as attachments.

## Literature wanted

WANTED: Toën, *The homotopy theory of dg-categories and derived Morita theory*, arXiv:math/0408337, section 2, Definition 2.1, model-structure paragraph, Proposition 2.3 and its proof, for lem-coef-dgcat-model-structure.

WANTED: Tabuada, thesis arXiv:0710.4303, chapter 1, section 1.3.1, printed pages 27–32, definition of K, Proposition 1.7, Lemmas 1.10–1.12 and Proposition 1.13, for lem-coef-dgcat-free-cell-calculus and lem-coef-dgcat-equivalence-cell-calculus.

WANTED: Hovey, *Model Categories*, Theorem 2.3.11, Propositions 2.3.4, 2.3.5, 2.3.9 and 4.2.13, for lem-coef-projective-complex-cell-calculus.

These documents were read online, not downloaded into the project. The item proof is accordingly marked agent-written. None of these dg-category packages has an applicable Stacks tag; a tag about ordinary categories or bounded complexes would not supply the statements. No prohibited SGA route is used.

## Corrections and route

The imported item is mathematically consistent with Toën section 2 and needs no statement dispute or weakening. Its previous proof was empty. The replacement proof stays on the coefficient-enrichment infrastructure route in the recorded ancestor, the finite adjunction before total inverse limit; the unit record is not this item's key statement and is not edited.

An initial undelivered draft divided the conclusions into five children. On self-review I removed those files: model recognition, fixed-object replacement, local cofibrancy, homotopy representation and universe invariance would largely have repeated the parent's clauses. The present three children instead supply constructions and independent algebraic calculations. The twelve parent steps carry the model-structure construction and all its further conclusions.

I used the thesis's ordinary dg-category argument, with the empty initial category. The early 2004 preprint's pointed-category convention is not silently substituted. I wrote the terminal object as the zero-endomorphism category, not the one-object category with endomorphism ring Z. The source's word sums are interpreted with their length-zero old-Hom term; a K-cell adds an object, while an arrow/disk cell does not.

## Unfinished work

No stage-1 proof step is intentionally deferred outside the three stated children and the existing cited generic tools. The new children remain unsplit as required. Their future Lean proofs are not claimed to exist. No Lean was written and no compiler, Lake or build tool was run. Validation is unfinished: the required delivery dry run has NOT printed OK. After the duplicate-gate correction, three attempts ended with exit status 143 (SIGTERM), without a preflight result. The observed waits were on the shared Q66 delivery/worktree/fetch locks. No tool, lock, repository or launcher file was modified to bypass this. The worker therefore returns BLOCKED, not READY. The mathematical split, source review, citations and logged searches remain available for a later retry.

## Not duplicates

Whole-DAG and current-blueprint searches by free dg category, word filtration, coherent equivalence cell, projective complexes, source identifiers and proposed ids found no node stating these three packages. No Stacks tags are attached to the new nodes, hence there are no shared-tag pairs to justify.

lem-coef-dgcat-equivalence-cell-calculus vs lem-weil-pbc-extension-by-zero-stalks: the new node concerns explicit dg-category cells over a ring; the existing node concerns geometric stalks of open-immersion extension by zero. The shared text 0710 comes only from the arXiv identifier 0710.4303, not a Stacks citation; the existing source actually cites Stacks tag 0710. Neither statement implies the other.

lem-coef-dgcat-equivalence-cell-calculus vs lem-amb-etale-sum-stalks: the new node concerns explicit dg-category cells over a ring; the existing node concerns the direct-sum formula for geometric stalks of etale extension by zero. The shared text 0710 comes only from the arXiv identifier 0710.4303, not a Stacks citation; the existing source actually cites Stacks tag 0710. Neither statement implies the other.

lem-coef-dgcat-free-cell-calculus vs lem-weil-pbc-extension-by-zero-stalks: the new node concerns explicit dg-category cells over a ring; the existing node concerns geometric stalks of open-immersion extension by zero. The shared text 0710 comes only from the arXiv identifier 0710.4303, not a Stacks citation; the existing source actually cites Stacks tag 0710. Neither statement implies the other.

lem-coef-dgcat-free-cell-calculus vs lem-amb-etale-sum-stalks: the new node concerns explicit dg-category cells over a ring; the existing node concerns the direct-sum formula for geometric stalks of etale extension by zero. The shared text 0710 comes only from the arXiv identifier 0710.4303, not a Stacks citation; the existing source actually cites Stacks tag 0710. Neither statement implies the other.

The free-cell child differs from lem-coef-cardinal-small-object-factorization and lem-coef-presentable-cellular-factorization: it proves dgcat's presentation/colimit and word algebra hypotheses; those two existing nodes assume them and give general factorizations. The complex child differs from existing bounded/perfect-complex and projective-module nodes: it concerns the unbounded projective model, its generating sphere/disk maps, cofibration criterion and tensor-flat retracts. The coherent interval child is a dg presentation and single-pushout calculation, not an ordinary isomorphism-lifting definition. General localization/mapping-space facts are reused via lem-coef-cosimplicial-frame-mapping rather than recreated.

## Review by Q66

I read Toën's section 2 through Proposition 2.3 and its sketch, the thesis's actual formulas for K and the I,J generators and its small-object proof on printed pages 27–32, and Hovey's indicated projective-complex statements and monoidal theorem. Hovey uses chain degrees; the new complex statement negates indices to use cochain degrees. The K formulas already use the cochain convention: d(t)=f r_0-r_1 f has square zero because f(gf-1)-(fg-1)f=0. The empty category, zero ring/zero complexes, zero or identity attaching class, coincident arrow endpoints, negative degrees and zero-length words are allowed. In particular K's old-Hom assertion also applies if the attaching object's identity is zero. Free word filtrations include length zero and, for loops, all positive tensor lengths; they impose no boundedness or flatness on a disk attachment. Homotopical flatness in the complex child follows by tensoring a semi-free filtration: every graded quotient is a sum of shifts of the tested acyclic cone, successor steps are split extensions, filtered limits are exact elementwise, and retracts preserve acyclicity. The tensor/cofibration assertions use the commutativity hypothesis on R.

For step 1 I checked that the three new statements actually give T, K, sphere/disk objects, their differentials, completeness/cocompleteness and finite presentability. Small generator domains preserve omega-chains, so the regular cardinal in the existing functorial factorization node can be omega. The sets of integers and attaching maps belong to the fixed universe. Finite dg presentations here mean actual homogeneous presentations with differential compatibility, not arbitrary unproved enriched-category presentability.

Step 2 spells out the two-out-of-three argument, including the otherwise easy-to-miss case requiring object replacement and the action of an invertible H^0 class on every H^n Hom. Retracts transport both local cohomology inverses and the object-isomorphism witnesses. It uses definitions and explicit arguments, not an uncited recognition theorem.

For step 3 I read each cited statement against its use: the free-cell node supplies the T adjunction, the complex node gives BOTH lifting tests, and interval parts (a) and (c) respectively realize a bottom H^0-isomorphism and lift all its coherent data. A lift of an H^0 class is not automatically a strict lift of its representative. The degree -1 boundary adjustment is therefore included before applying (c); local surjectivity is exactly the hypothesis needed. The equality I-inj=F intersect W checks exact object preimages, not merely essential surjectivity.

For step 4 the free-cell direct-sum formula applies to whole disk complexes, whereas its filtered formula applies to a single arrow with prescribed boundary. I did not mix these two formulas. Every positive disk word contracts by its disk factor even with nonflat old Homs. The K-node's part (b) states both local quasi-isomorphisms and the new object's H^0-isomorphism; neither is being inferred from a definition. Filtered exactness is proved by moving a cycle and its finite equation to a common stage. The transfinite essential-surjectivity induction also covers newly adjoined objects.

For steps 5–6 I opened the two existing factorization nodes. The cardinal node promises functorial LLP/RLP factorizations, but DOES NOT promise cellular left maps. The presentable-cellular node promises explicit continuous relative-cell factorizations, but DOES NOT promise functoriality. I keep their roles separate and supply the retract arguments. Both have their small-Hom/colimit hypotheses provided by the free-cell child. The equality of trivial cofibrations with C intersect W is proved in the item, using J-cell weak equivalences and I-inj=F intersect W, rather than delegated to a child that restates model existence. Sequential fillers and the colimit universal property give the required LLP for cell maps.

For step 7 I checked the degenerate terminal category and empty source explicitly: the terminal identity is zero, the unique isomorphism lifts by an upstairs identity, and there is no source object to check in the empty case.

For step 8 the cited free-cell statement provides preservation of objects and finite presentation of both boundary and disk categories; the complex statement supplies the local acyclic-surjection lifting test. The proof builds the replacement by ALL lifting squares at each stage, so functoriality includes nonidentity object maps. It does not claim that an unspecified existing factorization preserves objects. Objects are fixed even for A empty, where the construction remains empty.

For steps 9–10 the existing cellular factorization makes a cofibrant dg category a retract of a genuine I-cell object. The free-cell statement supplies a degreewise split filtration with its exact tensor quotient, and the complex child supplies tensor cofibrancy, split-cokernel cofibrations, transfinite closure and retract closure. I verified that the structure maps on Homs are cofibrations before using a limit; a filtered colimit of arbitrary cofibrant complexes alone would not suffice. Tensor flatness is then literally the last clause of the cited complex statement, and includes unbounded complexes.

For step 11 I read the existing frame statement, not just its title. It gives a frame with X^0=X, objectwise weak-equivalent augmentation, cofibrant latching maps, and a Kan function complex computing the infinity localization for fibrant targets. The constructed model category meets all its hypotheses and every target is fibrant. In degree one the latching object is exactly A coproduct A, so the frame edge is a cylinder; the converse for any cylinder follows because its contraction is inverted. This checks the precise equivalence relation in the item.

For step 12 I checked the universe comparison rather than citing a universe slogan. The free constructions and small colimits agree in the larger universe. The existing cellular factorization plus retract argument shows old cofibrations remain cofibrations, including the latching maps of an old frame. The frame theorem therefore applies to that same old frame on both sides, with literally the same simplicial Hom sets. No new large zigzag or arbitrary large replacement is needed. This proves mapping spaces as well as their component sets, for all original small inputs after the object-preserving QA replacement.

The citation manifest quotes the full statement of every cited node, copied verbatim, so the second reader can check each of these uses without relying on names. All new children are statement-only, their mathematical notions are introduced inline or by their explicit statement dependency, and their blueprint provenance points to the recorded ancestor through this item. Search records are selected from this task's actual msearch log, preserving exact tools and queries; broad semantic hits were read and rejected for the category/model hypotheses described in each verdict.

During the B–E review I also replaced the new statements' plain-text formulas with TeX, added the cochain and lifting definitions explicitly, and made the source object in the interval lifting clause explicit. This changes no mathematical claim. The two blueprint search hits for projective models were read: def-trf-categorical-trace defines a perfect-complex trace, and prop-pod-perfect-local-model concerns a finite projective sheaf; neither states the unbounded complex lemma.

The unbounded-complex child explicitly fixes the existing size convention as its statement dependency; its inline cochain definition is retained. I checked the other cochain-definition search hit, def-pc-cochain-complex-modules: it is for sheaves on a site, so I did not cite it as if it directly defined ordinary R-module complexes.

The first completed dry run stopped at the duplicate gate because its tag regular expression interpreted the arXiv source identifier 0710.4303 as Stacks tag 0710. I opened both flagged stalk statements and recorded all four new/existing pairs under Not duplicates. Their ordinary etale-sheaf stalk formulas are unrelated to either free dg cells or the coherent interval. I retained the accurate arXiv source rather than obscuring the identifier.

## Dry-run outcome

The completed early attempt reported the arXiv/Stacks 0710 duplicate collision; all four required pair explanations were then added. The delivery tool's citation_check, search_check and dup_check subsequently all returned OK against the sandbox and shared baseline. Nevertheless each of the next three full `python3 -u /home/ubuntu/weil-launcher-nt/deliver.py Q66 lem-coef-dgcat-model-structure --no-push` attempts was externally terminated with status 143 before any full preflight result. The last redirected `dry-run.log` is empty. See `dry-run-status.txt` for the precise limitation. Nothing was pushed, and a successful dry run is still required before this sandbox can be treated as accepted.

## Second reading by Q66

I reopened Toën, *The homotopy theory of dg-categories and derived Morita theory*, §2 Definition 2.1, the fibration/model-structure paragraph, and Proposition 2.3, and checked the item statement hypothesis by hypothesis: the quasi-equivalence, fibration, trivial-fibration, fibrancy, object-preserving replacement, cofibrant Hom complexes, cylinder-homotopy, and universe-comparison clauses agree with the source (with the source's mapping-space equivalence understood in the localization).

Step 1: checked the explicit (I,J,T,S^n,D^n,K_R) constructions against Tabuada §1.3.1 and the three cited statements; verdict, dependencies state the required presentations, filtrations, and complex model data.
Step 2: checked retract and two-out-of-three arguments directly against the definition of quasi-equivalence; verdict, elementary and no external fact is hidden.
Step 3: checked both lifting tests against the free-cell, coherent-interval, and projective-complex statements; verdict, the degree (-1) representative correction and simultaneous interval lift are explicitly supplied.
Step 4: checked disk and (K_R) pushouts against the word filtration and interval pushout clauses; verdict, the contractible disk factor and filtered-colimit argument are stated.
Step 5: checked the two small-object factorizations against the cardinal and cellular factorization statements; verdict, functoriality and cellularity are kept as separate cited conclusions.
Step 6: checked the retract proof of (Acof=C\cap W) against the cellular factorization statement and Step 4; verdict, both inclusions and the lifting-at-limits argument are present.
Step 7: checked the terminal zero-endomorphism dg category and empty source; verdict, all objects are fibrant, including the zero and empty cases.
Step 8: checked the object-preserving replacement construction against Proposition 2.3(2), the free presentations, and the complex lifting test; verdict, every finite boundary square is addressed at a later stage and no object is added.
Step 9: checked the transfinite Hom-filtration argument against Proposition 2.3(3), the free-word filtration, and projective cofibrancy; verdict, split filtration quotients and retract closure supply the claim.
Step 10: checked the homotopical-flatness conclusion against the final clause of the projective-complex statement; verdict, it applies to every unbounded quasi-isomorphism.
Step 11: checked strict-functor representatives, cylinder edges, and localization mapping spaces against the full cosimplicial-frame statement; verdict, the target is fibrant and the frame latching map supplies the cylinder relation.
Step 12: checked the universe comparison against Toën's §2 universe paragraph and the free/cellular/frame statements; verdict, the same small generators and frame give the asserted equivalences for original small inputs.

New node `lem-coef-dgcat-free-cell-calculus`: checked its cochain, (R)-linear dg-category, finite-presentation, filtered-colimit, free-arrow, and word-filtration clauses against Tabuada pp. 28–30 and the stated definition dependency; verdict, self-contained statement-only node, including the zero and length-zero cases.
New node `lem-coef-dgcat-equivalence-cell-calculus`: checked the five generators and all three realization/pushout/lifting clauses against Tabuada pp. 27–32 and the free-cell dependency; verdict, self-contained statement-only node, with prescribed source and strict differential identities.
New node `lem-coef-projective-complex-cell-calculus`: checked the cochain convention, sphere/disk generators, lifting characterizations, cofibration criterion, transfinite cells, tensor closure, and homotopical flatness against Hovey §§2.3 and 4.2; verdict, self-contained statement-only node for arbitrary commutative (R), including (R=0), zero complexes, and all integer degrees.

Changes made in this second reading: added this source-based review section; retained all four mathematically substantive node files and their verbatim citation manifest; recorded that no statement, proof step, or node required mathematical repair. The previously recorded blocked dry-run note is superseded once the required delivery command completes successfully.
