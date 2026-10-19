# Stage-1 report: lem-coef-enriched-projective-diagram-model

## Files written

- `dag/nodes/sec-six-functors/lem-coef-enriched-projective-diagram-model.json`: statement, split; corrected the missing tensor-cell acyclicity hypothesis and wrote ten argument steps. Mathlib searches found no theorem giving the enriched projective transfer.
- `dag/nodes/sec-six-functors/lem-coef-cocontinuous-monad-presentability.json`: statement, unsplit; ordinary local presentability of algebras for a colimit-preserving monad on a small family category. Mathlib has ordinary functor-category presentability and creates monad (co)limits, but not the whole algebra-presentability assertion. It carries no proof or proof dependencies.
- `citations.json`: every step/node pair, with verbatim statements as quotes.
- `report.md`: this report. `searches.jsonl` is the search tool's log.

## Attachments

None. Read-only searches of `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/` for the blueprint tag, projective model structure, enriched diagram terminology, and monad/algebra presentability found no exact closed project declaration. The upstream master is reference material only. No Lean was written or compiled.

## WANTED

WANTED: Bertrand Toën, *The homotopy theory of dg-categories and derived Morita theory*, Section 3, Definition 3.1, model-structure paragraphs and Propositions 3.2–3.3, for the item; read online at https://arxiv.org/pdf/math/0408337, not archived in `literature/`.

WANTED: Adámek and Rosický, *Locally Presentable and Accessible Categories*, Corollary 1.54 and Theorem 2.78, for `lem-coef-cocontinuous-monad-presentability`. Read the identification of the algebra theorem in Ching–Riehl, *Coalgebraic models for combinatorial model categories*, Appendix A, page 9, after Proposition A.1, https://math.jhu.edu/~eriehl/coalgebraic.pdf. The latter is read online, not archived. Its coalgebra theorem is not being cited as if it were the monad-algebra theorem.

WANTED: Hovey, *Model Categories*, Theorem 2.3.13, for the injective-model counterexample below; no archived copy was found. The counterexample's enriched compatibility and failure are checked directly below.

The proof is marked agent-written, following the blueprint's finite mapping-complex comparison and the external dg-module route, with the actual transfer and lifting arguments supplied. No Stacks tag states the arbitrary enriched-diagram model theorem or the ordinary accessible-monad theorem; none is invented. No SGA reference is used.

## Statement dispute and source error

STATEMENT-DISPUTED: the original assertion for every cofibrantly generated complex-enriched model category and every small dg index is false without an acyclicity condition. This also affects the unqualified generalized-model paragraph following Toën Definition 3.1, as read with the ordinary enriched-model-category meaning specified in the item.

Take N to be unbounded cochain complexes of abelian groups with the injective model structure: weak equivalences are quasi-isomorphisms and cofibrations are all degreewise injections. This is a cofibrantly generated model structure on a locally presentable category, and every object is cofibrant, so all generating cofibration endpoints are cofibrant. It is enriched, tensored and cotensored over projective Ch(Z). To check that compatibility explicitly, a generating projective sphere-to-disk cofibration has a degreewise split free cokernel. Its pushout product with any injective cofibration is still an injection with a shift of the latter's cokernel; it is a quasi-isomorphism if the latter is trivial. A generating projective trivial cofibration is zero-to-disk; its pushout product has a contractible disk tensor cokernel for any injection. Tensor preserves the attaching colimits and retracts, so the generating checks give the mixed pushout-product axiom and therefore exactly the relative-Hom axiom in the original statement. Thus this N meets the original enriched hypotheses; it need not be monoidal for its own injective cofibrations.

Let C have one object and endomorphism dg algebra Z/p concentrated in degree zero, for a prime p. Strict C-diagrams are precisely complexes of Z/p-modules, viewed as abelian-group complexes. If a projective model structure with the asserted fibrations existed, each fibrant C-diagram would be injectively fibrant as an abelian-group complex. Its terms would be injective abelian groups: for a mono A→B, the acyclic disk mono D^n(A)→D^n(B) is a trivial cofibration, and lifting against X→0 extends every A→X^n to B→X^n. Hence X^n is divisible. But its Z/p action says pX^n=0; divisibility by p then forces X^n=0. The only fibrant diagram would be zero. Fibrant replacement of Z/p[0] would force the nonzero complex Z/p[0] to be quasi-isomorphic to zero, a contradiction. This is an existence failure, rather than merely a failure of the chosen transfer proof.

The correction adds the tensor-cell acyclicity condition for the saturated class generated by K⊗j with K arbitrary and j a trivial cofibration. The closure operations are stated in full, including retracts. This is the missing condition the relative free-cell transfer actually uses. The statement also records its inheritance by projective diagram categories, proved in step 9, so that the intended repeated application beginning at projective Ch(Z) remains available. Step 10 proves this condition for Ch(Z) by split inclusions with contractible cokernels, including an explicit contraction after arbitrary tensor and the transfinite direct-sum argument. Thus no coefficient category is silently changed. General callers using another target model must verify this hypothesis; in particular `lem-coef-locally-cofibrant-dg-restriction` repeats the old broad target hypotheses and needs a maintainer/owner review of its use of this corrected theorem. I have not edited that other item.

The target statements in GOAL.md and their base-change transformations are not changed. This is foundation below the finite exceptional-adjoint mapping comparison, not a change of chapter or unit route. The inherited unit binding `sk-prop-sf-biduality-general` and blueprint ancestry are retained.

## Not duplicates

- `lem-coef-cocontinuous-monad-presentability` vs `lem-coef-algebroid-presentability`: the new statement is about ordinary Eilenberg–Moore algebras for a fixed ordinary monad on a family category. The existing statement concerns presentability of an infinity category of variable-object enriched algebroids and does not assert local presentability of strict ordinary dg functor categories.
- `lem-coef-cocontinuous-monad-presentability` vs `lem-coef-enriched-category-tensor-calculus`: the existing statement is about homotopy coherent enrichment over a presentable infinity category; it does not identify strict dg diagrams with a locally presentable ordinary algebra category.
- `lem-coef-cocontinuous-monad-presentability` vs the item: the new statement has no model structure, dg enrichment, objectwise fibrations, generating cells, or cofibrant-evaluation conclusion. It is an independent ordinary categorical input. The item carries the actual transfer argument; it does not say “apply a new projective-diagram theorem.”

Whole-DAG and whole-blueprint searches were made for monad, accessible monad, ordinary algebra presentability, representable tensors and objectwise enriched model structures. The existing cochain-model node and both small-object nodes were opened and reused. The other local-presentability nodes concern Grothendieck abelian categories, object ranks or localization of model categories, and do not assert this new theorem. There are no same-tag pairs: the new categorical theorem has no Stacks tag.

## Review by Q28

I read the item's source, the main-20261015 proof of `prop-coef-integral-exceptional-adjoint`, especially its second paragraph. That paragraph asks for a simultaneous finite derived mapping-complex comparison before derived inverse limit. I also read Toën's Section 3, including the model-structure paragraph following Definition 3.1, the free generators in the proof of Proposition 3.2, and the exact proof of Proposition 3.3. I compared those with the actual imported hypotheses, rather than assuming the source's blanket existence claim was sufficient. The injective-model counterexample above is the substantive correction. For the one new node I read Ching–Riehl Appendix A: it explicitly points to the accessible-monad algebra theorem, while its written proposition is for coalgebras. AR 1.54/2.78 remain WANTED. The ordinary product and algebra theorem is therefore isolated as a statement-only input; its future split may use the ordinary product construction, an accessible inserter of T and identity, and equifiers imposing the two algebra identities, followed by the accessible-complete criterion. None of that proof sketch is inserted into the unsplit node's statement.

I opened the entire statements of `lem-coef-projective-cochain-monoidal-model`, `lem-coef-presentable-cellular-factorization`, `lem-coef-presentable-small-object-factorization`, and `lem-coef-dgcat-model-structure`. The precise uses are:

1. Step 1 defines the graded-natural transformation subcomplex, pointwise tensors/cotensors, and pointwise (co)limits. Differential preservation uses the given chain-map composition rule and the displayed sign; it does not borrow a theorem about ordinary-index enriched ends as a theorem for dg indices.
2. Step 2 uses the new monad statement only for ordinary local presentability. The coproduct formula for T, the unit/composition formulas, its preservation of all colimits, and the identification of algebra equations with dg actions are written in the step. N is complete and locally presentable and S is a set, exactly as the new statement requires. No same-cardinal conclusion is taken from it.
3. Step 3 writes the free/evaluation adjunction, including homogeneous signs. The two lifting-class equalities are the generating hypotheses of the item, not an unsupported Yoneda citation.
4. Step 4 uses the cellular factorization node for relative cell factorizations, and the separate functorial factorization node for functorial choices. These statements really contain those distinct conclusions. The extension of fillers and the arrow retract are written out.
5. Step 5 again uses the cellular statement for the J-cell/retract presentation and the dgcat node's explicit definition of the model axioms. The essential W assertion comes from the newly stated tensor-cell hypothesis after evaluating each attached free cell. Two-out-of-three gives the reverse left-class equality; arbitrary pushouts of weak equivalences are never assumed.
6. Step 6 uses the cochain model statement at Z for the fibrations, quasi-isomorphisms, and generating lifting tests on complexes, and the cellular statement to pass from diagram generators to all cofibrations. It proves the tensor pushout-product property by transposing the original enriched axiom, and transposes back for the actual transformation complex. A limit of degreewise surjections is not assumed surjective.
7. Step 7 derives free endpoint cofibrancy and objectwise fibrancy directly from the classes already proved. It makes no local-cofibrancy assumption on C here.
8. Step 8 uses the cellular statement to reduce evaluation to I/J generators. The extra hypothesis that every C(c,d) is projectively cofibrant is used exactly in the pushout product with its initial map. Evaluation preserves the needed attaching colimits by step 1.
9. Step 9 uses the J-cell retract presentation in the cellular statement, tensors it and evaluates it. The saturated class in the corrected hypothesis is closed under exactly the operations being used. Thus the added hypothesis really is inherited, rather than being silently assumed for a second diagram category.
10. Step 10 uses the existing projective cochain node for the entire combinatorial closed monoidal structure, explicit generators and split/dg-projective characterization. The sphere and disk checks, all-object fibrancy, split retraction of a trivial cofibration, Hom(E,E) contraction, Koszul tensor contraction, and transfinite sum of contractible cokernels are supplied in the step. This verifies the added condition in the intended base case.

For every citation I copied the actual statement into `citations.json`, after reading it and checking that it supplies the claim above. No proof-internal construction of a cited node is used. The two small-object nodes and the cochain node are in the same inherited unit; no outside-unit statement tool is needed.

I tested the new statement on S empty (the family/algebra category is terminal), the identity monad (ordinary small products), and a one-sorted ring-module monad (ordinary module actions). T preserves all small colimits, hence the needed filtered colimits; no unsupported “all monads preserve colimits” premise is used. I tested the item on the empty dg category, the single object Z, the noncofibrant dg algebra Z/p, and zero/trivial generating maps. The corrected theorem admits Z/p as an index for projective Ch(Z); its free endpoints can be diagram-cofibrant although their underlying complexes need not be. This distinguishes the unrestricted free-endpoint claim from the additional locally cofibrant evaluation claim. Cochain degrees of S^{n+1}→D^n and the contraction sign were checked explicitly.

Against delivery-errors B–E, the new node is self-contained, statement-only, correctly named, and has full blueprint ancestry and exact executed Mathlib searches. No clause of the item is moved into a child. The item's proof contains the model transfer and evaluation arguments; there is no circularity or added off-route proof. Its only statement change is explicitly disputed and justified above. The Mathlib candidates were read at their source lines: monad limits and ordinary presheaf presentability give only parts of the new theorem; the model-category constructor takes the weak factorization systems as inputs. Rejected unquoted Loogle identifiers are recorded as unavailable queries, never as evidence of absence. No writes were made outside this sandbox; no git command, compiler, Lake, download or agent was started.

## Earlier second reading (a previous round; superseded)

Step 1: checked the strict dg natural-transformation equations, Koszul signs, pointwise tensors/cotensors, and componentwise limits/colimits against the item statement and blueprint proof paragraph; verdict: elementary and correct.

Step 2: checked the action monad, its unit and multiplication, colimit preservation, and the use of the ordinary monad-presentability node against that node's statement; verdict: all hypotheses are present and the step uses only its local-presentability conclusion.

Step 3: checked the enriched free/evaluation adjunction, homogeneous sign, and transposed lifting classes against the stated dg action equations and generating hypotheses; verdict: correct and sufficiently explicit.

Step 4: checked both cellular and functorial factorizations, transfinite fillers, and the arrow-retract argument against the two cited small-object nodes; verdict: the citations supply the claimed conclusions and the retract argument is written out.

Step 5: checked the weak-factorization transfer, saturated tensor-cell acyclicity, retract argument, and two-out-of-three reasoning against the corrected item statement and dg-model conventions; verdict: correct under the added hypothesis.

Step 6: checked both pushout-product transpositions, cell filtration, retract closure, and the final relative-Hom test against the cellular and projective cochain statements; verdict: correct, with no unsupported closure of arbitrary weak equivalences.

Step 7: checked free-generator endpoint cofibrancy and objectwise fibrancy against the lifting classes established in steps 5–6; verdict: elementary and correct.

Step 8: checked the locally cofibrant source-complex hypothesis, evaluation on generators and cells, and preservation of cofibrant diagrams against the cellular node; verdict: correct with exactly the stated extra hypothesis.

Step 9: checked inheritance of the saturated tensor-cell class through tensoring, evaluation, cells, and retracts against the corrected closure operations; verdict: correct and no arbitrary weak-equivalence closure is assumed.

Step 10: checked the Ch(Z) generators, split retraction, contractible cokernel and tensor contraction, transfinite direct-sum argument, and retracts against the projective cochain node; verdict: correct.

New node `lem-coef-cocontinuous-monad-presentability`: checked its statement-only B1–B7 form, self-contained ordinary-monad terminology, source paragraph, blueprint ancestry, and the executed grep/LeanFinder/Loogle/LeanSearch searches; verdict: an independent unsplit categorical input, with no duplicate found.

Item statement: checked every hypothesis and clause, including the corrected tensor-cell acyclicity condition and the Ch(Z) specialization, on empty and one-object dg categories, zero maps, fields, and Z/p; verdict: the unrestricted source assertion is false and the repaired statement records the needed condition and counterexample.

Changes made in this repair: re-read the current `lem-coef-dgcat-model-structure` node after its reviewed statement changed, and replaced the step 5 citation with the node statement verbatim, including its explicit projective-cochain dependency reference. The earlier projective-cochain citation repair remains verbatim. No proof step or item statement required mathematical repair.

## Unfinished work

The one new categorical foundation remains unsplit, as the one-level contract requires. No other argument of the item is deferred. An independent second reader must review the statement correction and deliver; this worker only dry-runs.

## Validation

Validation command: `python3 /home/ubuntu/weil-launcher-nt/deliver.py Q28 lem-coef-enriched-projective-diagram-model --no-push`. The local overlay check passed JSON validity, dependency-union equality, every citation quote, and reachable-DAG acyclicity (45 reachable nodes). The required delivery tool additionally checks source/route metadata and the exact search log; its final result is reported in the worker handoff. No push or Lean compilation is requested.

## Earlier second reading (a previous round; superseded)

Step 1: checked the graded natural-transformation complex, Koszul signs, pointwise tensor/cotensor, and componentwise limits/colimits against the item's definitions and the blueprint proof paragraph; verdict: elementary and correct.
Step 2: checked the action monad, its unit/multiplication identities, colimit preservation, and the application of `lem-coef-cocontinuous-monad-presentability` against that node's complete statement; verdict: correct and all hypotheses are named.
Step 3: checked the enriched free/evaluation adjunction, homogeneous sign, and transposed lifting classes against the stated dg action equations and generating hypotheses; verdict: elementary and correct.
Step 4: checked both cellular and functorial small-object factorizations, transfinite fillers, and the arrow-retract argument against the two cited factorization nodes; verdict: correct and the citations supply the claimed conclusions.
Step 5: checked the objectwise weak-factorization transfer, tensor-cell acyclicity use, retract argument, and two-out-of-three conclusion against the corrected item statement and `lem-coef-dgcat-model-structure`; verdict: correct under the added saturated acyclicity hypothesis.
Step 6: checked both enriched pushout-product transpositions, the cell filtration, retract closure, and final relative-Hom test against the cited cellular and projective cochain model statements; verdict: correct, with no illicit closure of arbitrary weak equivalences.
Step 7: checked free-generator endpoint cofibrancy and objectwise fibrancy against Step 6 and the projective lifting classes; verdict: elementary and correct.
Step 8: checked the extra cofibrancy hypothesis on every `C(c,d)`, evaluation on generators and cells, and the cofibrant-diagram conclusion against the cellular node; verdict: correct with the stated hypothesis.
Step 9: checked inheritance of the saturated tensor-cell class through tensoring, evaluation, cells, and retracts; verdict: correct and uses exactly the corrected closure operations.
Step 10: checked the `Ch(\mathbf Z)` specialization, generators, split retraction, contractible cokernel argument, tensor contraction sign, transfinite sums, and retracts against `lem-coef-projective-cochain-monoidal-model`; verdict: correct.
New node `lem-coef-cocontinuous-monad-presentability`: checked statement-only B1–B7 form, self-contained definitions and dependencies, blueprint ancestry, source paragraph, and executed LeanFinder/Loogle/grep/LeanSearch logs; verdict: appropriate unsplit categorical input, no duplicate found.
Item statement: checked the corrected tensor-cell acyclicity hypothesis, all dg/model hypotheses, the projective diagram clauses, evaluation clause, and `Ch(\mathbf Z)` clause on empty, one-object, zero, field, and `\mathbf Z/p` cases; verdict: the original unrestricted assertion is false and the repaired statement is faithful to the intended theorem.

Changes made in this second reading: repaired the step 6 and step 10 citations for `lem-coef-projective-cochain-monoidal-model` by copying the node statement verbatim, including its termwise-split-injection sentence; no mathematical proof text or node statement required change. This audit section was also added as required for delivery.

## Second reading by Q28

- Item statement: checked every clause against the current blueprint proof paragraph for `prop-coef-integral-exceptional-adjoint`, Toën Section 3, and the existing model and cochain nodes; verdict: the tensor-cell correction and its injective `\mathbf Z/p` counterexample are mathematically necessary and retained.
- Step 1: checked the strict dg natural-transformation complex, Koszul signs, pointwise tensor/cotensor, and componentwise limits and colimits against the item definitions; verdict: elementary and correct.
- Step 2: checked the action monad and its algebra identification against the existing `lem-coef-accessible-monad-presentability` statement; verdict: repaired to cite the existing more general node, with all hypotheses supplied (`\mathcal N^S` is a small product of locally presentable categories and the colimit-preserving monad preserves filtered colimits).
- Step 3: checked the enriched free/evaluation adjunction, homogeneous sign, and transposed lifting classes against the dg action equations and generating hypotheses; verdict: correct and explicit.
- Step 4: checked cellular and functorial factorizations, transfinite fillers, and the arrow-retract argument against both cited small-object nodes; verdict: correct and the citations supply the distinct conclusions.
- Step 5: checked the weak-factorization transfer, saturated tensor-cell acyclicity, retract argument, and two-out-of-three reasoning against the corrected item and `lem-coef-dgcat-model-structure`; verdict: correct under the repaired hypothesis.
- Step 6: checked both pushout-product transpositions, cell filtration, retract closure, and the relative-Hom test against the cited cellular and projective cochain statements; verdict: correct, with no unsupported closure of arbitrary weak equivalences.
- Step 7: checked free-generator endpoint cofibrancy and objectwise fibrancy against the established lifting classes; verdict: elementary and correct.
- Step 8: checked the locally cofibrant source-complex hypothesis, evaluation on generators and cells, and preservation of cofibrant diagrams against the cellular node; verdict: correct with exactly the stated extra hypothesis.
- Step 9: checked inheritance of the saturated tensor-cell class through tensoring, evaluation, cells, and retracts; verdict: correct and uses exactly the corrected closure operations.
- Step 10: checked the `\mathrm{Ch}(\mathbf Z)` specialization, generators, split retraction, contractible cokernel argument, tensor contraction, transfinite sums, and retracts against the projective cochain node; verdict: correct.
- New nodes: the proposed `lem-coef-cocontinuous-monad-presentability` was a duplicate of existing `lem-coef-accessible-monad-presentability`, whose statement strictly generalizes it; removed the duplicate node file and redirected Step 2, `proof_deps`, and its citation quote to the existing node. No other new node is elementary, a restatement, or a Mathlib theorem.
- Citation and form checks: every remaining citation quote is verbatim from the current shared node statement, the proof dependency list is the union of step uses, and the item retains blueprint ancestry and its explicit statement dispute. Small cases checked: empty index, one-object `\mathbf Z`, zero maps, fields, and `\mathbf Z/p`; verdict: no further statement change.

