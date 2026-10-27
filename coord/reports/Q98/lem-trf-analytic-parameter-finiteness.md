# Stage-1 worker report: Q98

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-analytic-parameter-finiteness.json`: item, statement unchanged; five proof steps assemble the separable reduction, dense algebraic approximation, degree comparison and purely inseparable return.
- `dag/nodes/sec-trace-formula/lem-trf-dense-subfield-separable-descent.json`: statement, unsplit; no Mathlib match after LeanFinder twice, Loogle, LeanSearch and source grep.
- `dag/nodes/sec-trace-formula/lem-trf-nearby-parameter-isometric-substitution.json`: statement, unsplit; no Mathlib match after the same five searches with its own mathematical questions.
- `citations.json`: verbatim statement evidence for every use in every proof step. `searches.jsonl` and `search-results/` retain actual tool output.

## Attachments

None. Searches under `lean/WeilConjectures/` for the exact blueprint tag, analytic parameters, Temkin, completed rational subfields, isometric substitution and dense separable descent found no declaration stating the item or either new node. The existing Padics/Extension proof is a specialized Krasner application over Q_l, not this statement. No Lean was written or compiled.

## Literature wanted

WANTED: Michael Temkin, Stable modification of relative curves, arXiv:0707.3953v3, printed pp. 48–49, Lemmas 6.3.2–6.3.3 and Corollary 6.3.4, local path `literature/temkin-stable-modification-arXiv-0707.3953v3.pdf`, for the item and both new nodes. The cited local PDF is absent. I read the public PDF at https://math.huji.ac.il/~temkin/papers/Stable_Modification.pdf through the web reader (PDF pages 48–49, zero-based pages 47–48), without downloading or writing to the repository. Its title and arXiv version agree. Following the absent-local-source rule I conservatively mark the assembly proof as agent-written and record the public source and exact places.

## Problems and corrections

The imported item had a statement and Mathlib searches but no proof. The statement is a valid specialization of Corollary 6.3.4; no statement correction or dispute is needed. The proof must not invoke additivity of topological transcendence degree: Temkin's Remark 6.3.5 specifically warns that it fails in general. I use only the algebraic transcendence-degree tower formula in the dense finite function field.

Two potential gaps were made explicit: the relative separable subfield is complete because it is finite-dimensional over the already complete base, and the degree comparison is applied with the known finite image first. The weaker existing close-embedding node assumes one finite index; using it in the reverse direction without first swapping the embeddings would not justify the conclusion. I also separate characteristic zero from characteristic p and check that taking p-powers does not turn a nonconstant parameter into a constant.

I read the current chapter and unit records and the latest blueprint's `lem-trf-local-term-locality.proof.md` and `sk-i-curve-zero/_section.md`. The latest blueprint expresses the contracting-correspondence input at a higher level; the live node already locates this analytic input in its inherited Temkin/semistable-alteration branch. This delivery refines only the requested node, preserves that ancestry and does not redesign the chapter or unit.

## Unfinished work

The two new supporting lemmas are intentionally statement-only stage-1 queue nodes, not proofs of the item in disguise. The separable-descent lemma is a generic theorem over arbitrary dense valued subfields, with no one-dimensional hypothesis or parameter conclusion. The substitution lemma uses no finite-extension hypothesis and gives a uniform estimate; it does not assert parameter finiteness. No other part of this one-level split is left unfinished.

## Not duplicates

lem-trf-dense-subfield-separable-descent vs lem-trf-valued-decompletion-etale: the existing statement starts with an already finite algebraic extension and bounds its completed degree; the new statement descends an arbitrary finite separable extension of a completed field to a finite extension of the given dense subfield inside it.

lem-trf-dense-subfield-separable-descent vs lem-trf-separable-valued-completion-factors: the existing statement decomposes the completion of an already given finite separable extension; it does not construct an algebraic dense model for an arbitrary extension of a completion.

lem-trf-dense-subfield-separable-descent vs lem-per-dense-henselian-field-etale-comparison: the existing statement requires the dense subfield itself henselian and asserts an equivalence on Galois groups and cohomology; the rational subfield here need not be henselian, and the new statement gives an embedded algebraic dense model.

lem-trf-dense-subfield-separable-descent vs lem-sfb-dense-subfield-algebraic-root-approximation: the existing statement gives a nearby algebraic root in an algebraically closed ambient field; it does not ensure the root lies in H, generates H over F, or gives a separable dense subfield of H.

lem-trf-nearby-parameter-isometric-substitution vs lem-trf-analytic-close-embedding-degree: the existing node compares finite indices after two close embeddings have been supplied; the new node constructs an isometric substitution from a parameter-distance bound, with no assumption of finite index.

lem-trf-nearby-parameter-isometric-substitution vs lem-trf-analytic-uniformization: the existing statement supplies an etale parameter with perturbation stability, not a uniformly close isomorphism between two prescribed completed rational subfields; it also depends on this item, so using it here would be circular.

All-chapter DAG and blueprint searches by the source's lemma numbers, analytic fields, dense subfields, Krasner, perturbation, isometric, rational subfield and separable descent found no existing exact statement. `blueprint.same_as` is therefore empty. Both new ids were checked against live nodes and project Lean. No new node carries a Stacks tag; Temkin's named statements are the primary sources. Existing Stacks-based field tools are cited by their existing node ids, rather than duplicated.

## Review by Q98

I read delivery-errors B–E in full and checked the actual statements, not the proofs, of each cited node. For the item I read Temkin Corollary 6.3.4 and its proof on printed pp. 48–49. For the dense-descent node I read the proof's Krasner descent sentence; the formulation records exactly the embedded finite separable model and density required there, generalized to an arbitrary dense subfield. A later proof can approximate a primitive element's separable minimal polynomial, use simple-root stability and Krasner to obtain a root inside H generating H/F, and take l=D(b); density follows from H=F(b). This explanation belongs here, not in the unsplit statement. For nearby substitution I read Lemma 6.3.2 and its proof: factor polynomials over the algebraically closed ground field, control each linear factor relatively, retain the bound under multiplication and inversion, and extend by limits. The new statement uses a closed bound by c<1, so zero is included and limits preserve the inequality.

Step 1 uses `lem-weil-pbc-separable-first-purely-inseparable` for exactly its separable-subfield and p-power clauses. Its hypothesis is algebraicity, supplied by E/F finite. It uses `lem-sfb-finite-dimensional-subspace-closed` with complete nontrivially valued scalar fields F and k and the Hausdorff norm topology; H is finite-dimensional over F, k is one-dimensional over itself. Thus H is complete and the nonconstant x has positive distance from k. Neither henselianity of the uncompleted rational field nor separability of E/F is silently assumed.

Step 2 uses `lem-trf-dense-subfield-separable-descent` with D=k(y), F its closure and H the finite separable subextension. D inherits a nontrivial norm from k, and completeness of F,H was checked in Step 1. Density supplies the strict r/4 approximation, which excludes x' in k. Algebraic closedness excludes algebraic nonconstant elements directly by factorization of a polynomial into linear factors.

Step 3 uses the cardinal formula and algebraicity clause of `lem-kun-transcendence-degree-tower` only for ordinary algebraic fields, giving transcendence degree one. It then uses the last clause of `lem-sfb-curve-function-field-arithmetic`, which is independently quantified over arbitrary finitely generated fields K/k,L/k of equal finite transcendence degree; it does not require either field to be presented as the function field of a smooth scheme. Finally the first sentence of `lem-trf-valued-decompletion-etale` gives the finite completed extension, without any need to prove etaleness or use its later clauses. Both absolute values are compatible and nontrivial because they restrict to k. The closures identify the completions uniquely by their dense inclusions in complete H.

Step 4 uses `lem-trf-nearby-parameter-isometric-substitution` with c=1/4 and the positive distance from Step 1; its full conclusion supplies both the map and the uniform error estimate. `lem-trf-analytic-close-embedding-degree` is then used with first embedding phi and second the inclusion, so its finite-index hypothesis is Step 3 rather than the desired conclusion. The source, target, isometry and completeness hypotheses all agree.

Step 5 is elementary linear algebra: products of two finite spanning sets span the tower, and the same spanning set spans over any larger intermediate scalar field. The displayed inclusion of closures follows from x being z or a p-power of z and monotonicity of closure. This handles the originally inseparable extension without needing a bound on [k(z)^wedge:k(x)^wedge].

I tested the new descent statement on H=F (choose l=D), on dense D=F, and on positive-characteristic finite separable extensions; it deliberately excludes purely inseparable descent. I tested substitution on u=v, v=u+a with |a|<r, c tending to 1 from below, constants v in k (excluded by the bound), and b=0. For the item, E=k is excluded by hypothesis; y in k would force it, p-power parameters stay nonconstant, and degree-one completions cause no exceptional case. No proof step exceeds 2000 characters. Neither new statement duplicates a clause of the item, uses proof-only data from another node, nor creates a dependency cycle. The three off-unit algebraic tools are declared in `split_report.tool_uses`. Every citation is backed by a verbatim entry in `citations.json`; all new-node Mathlib search queries were run with msearch.py and the returned hits were read. No service outage is being called a negative match.

## Delivery checks

The first dry run found missing chapter/unit metadata on the two new nodes. Both now inherit `sec-trace-formula` / `sk-i-curve-zero` from the item. No mathematical finding was reported.
