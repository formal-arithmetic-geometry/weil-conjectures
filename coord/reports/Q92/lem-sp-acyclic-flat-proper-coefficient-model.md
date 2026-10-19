# Worker report

## Files written

- `dag/nodes/sec-smooth-purity/lem-sp-acyclic-flat-proper-coefficient-model.json`: statement item, now split into eight steps, with no change to its statement. Fresh Mathlib searches were appended to the inherited searches.
- `citations.json`: a verbatim quotation for each dependency of each proof step (22 entries).

No new nodes; no Mathlib leaves. No unit record changed: this is a subsidiary model calculation, not the compatibility unit's statement node.

## Attachments

None. Read-only searches of `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/` for the exact blueprint tag and the notions acyclic/flat/projection found no declaration giving every clause. Existing projective-line injective-acyclicity declarations do not state this item. No completed Lean attachment is claimed from upstream master.

## Literature wanted

None.

## Corrections and scope

The imported item had a statement and logged searches but no proof. Its hypotheses and conclusion are retained exactly. The proof uses the general abelian-category clause (3) of `lemma-weil-pbc-leray-acyclicity`, not just that node's final specialization to F_ell-modules. In its inherited sources, the references to Stacks 0732/0733 describe Leray spectral sequences rather than the acyclic-complex comparison; the precise source for that comparison is Stacks 015E (`derived.tex`, `lemma-leray-acyclicity`). Likewise, the existing K-flat node's source says 06YS, but the exact bounded-above flat lemma in the local source is 06YQ (`sites-cohomology.tex`, `lemma-bounded-flat-K-flat`). These are source-pointer observations about existing nodes, which this worker does not edit.

The key issue was retaining the named counit transpose, rather than merely identifying its source and target objects. The existing `lem-pc-pre-derived-adjoint-functors-general` explicitly states the localization formula for its hom bijection. Steps 4 and 6 apply that formula with identity denominators, separately, to the actual A-counit and B-projection maps. This avoids creating a new lemma that simply repackages the item's main clause.

I read the fixed chapter, the current compatibility unit record (clause (7) and its proof), the ancestor `det-sp-reduction-exceptional`, and the main-20261015 Charts proof paragraph. This calculation supplies the already chosen coefficient-compatibility route. It uses neither smooth-purity trace alternatives nor any SGA source. The item's existing blueprint ancestry and unit binding were retained. Off-unit foundational uses are declared in `split_report.tool_uses`.

## Mathlib and duplicate searches

All six fresh searches were run through `msearch.py` and their original records are in `searches.jsonl` and appended verbatim as JSON result strings in the node. I read the hits. Two LeanFinder phrasings returned exact-functor localization maps, generic derived adjunctions, and right-derived functors on degree-zero objects. LeanSearch returned ordinary module flatness and cotangent-complex base-change statements. Loogle found `CategoryTheory.Adjunction.derived_counit`; the targeted grep found `derivedε_fac_app` in `Mathlib/CategoryTheory/Functor/Derived/Adjunction.lean`, lines 125–129. I read that file, including its absolute-derived hypotheses. It supplies an abstract derived-counit identity, not the whole ringed-site acyclic-flat coefficient-model statement, so the item is not a Mathlib leaf. The initial unscoped grep found no hits; it was followed by the successful scoped grep, and both actual outputs are retained. No unavailable service was represented as a negative search.

Whole-DAG title and statement searches, together with blueprint searches for `K-flat`, `bounded above flat`, `derived adjunction`, `acyclic counit`, and `acyclic flat proper coefficient`, found reusable existing nodes. In particular the ringed-site K-flat statement applies directly, and the explicit pre-derived hom formula is already stated. No elementary fact, clause of this item, or duplicate was made into a new node. No new-node duplicate pairs arise.

## Review by Q92

I checked B–E with the item, each cited node's statement, and the local sources open. For the item I read Stacks 0GL6 (`more-etale.tex`, `remark-Rf-lower-shriek-change-of-rings`): it describes the coefficient square and does not itself contain our model-level calculation. Accordingly the proof is marked agent-written, with its elementary calculations exposed. I also read Stacks 015E in `derived.tex`, Stacks 0FND and 09T5 in the same file, and Stacks 06YQ and 07A6 in `sites-cohomology.tex`. I read the existing module Grothendieck/enough-injectives/left-exactness statements and checked their constant-coefficient etale scope. No statement-only new nodes require source validation.

Step 1 uses the etale module Grothendieck and enough-injectives statements for R=A,B; the module pushforward statement gives additivity and left exactness; the exact inverse-image statement gives the actual module adjunction, including the identified constant coefficient rings. These are the hypotheses for applying the general derived-adjunction formula; no pro-etale-only change-of-rings statement is applied on the etale site.

Step 2 uses the generic, rather than F_ell-specialized, clause (3) of `lemma-weil-pbc-leray-acyclicity`. Both complexes are bounded below since they are bounded, and the two given higher-image vanishing conditions are exactly the needed termwise acyclicity. Its conclusion concerns the natural comparison, hence supplies the stated comparison isomorphisms after localization; `def-weil-pbc-direct-image` explicitly supplies that natural transformation. The K-injective construction agrees with the ordinary unbounded computation here. I checked that no assertion of r_*-acyclicity of tensoring an arbitrary injective resolution is slipped into this step.

Step 3 applies the ringed-site bounded-above K-flat statement separately to C and D=r_*C. Both hypotheses are given, and r_* preserves the zero terms. The tensor construction explicitly resolves one factor only, so it applies to arbitrary B. The derived-pullback statement gives naturality on flat models. To keep the result in D(B_T), rather than just its underlying A-complex, I added the existing derived-pullback statement for the identity topos with map A_T→B_T; its K-flat computation states exactly the B-module representative used.

Step 4 uses the displayed characterization of the hom bijection in `lem-pc-pre-derived-adjoint-functors-general`, not an unstated feature of that node's proof. With K=C, M=D, both denominators identities, and f=id_D, its cocone component is alpha_A and its ordinary adjunct is the termwise counit. The exact pullback hypothesis identifies the left-derived cone component. I verified the direction: epsilon_A after r_A^*(alpha_A), not epsilon_A after its inverse, equals Q(e_C).

Step 5 uses preservation of flat K-flat models by ringed-topos pullback, the actual one-factor tensor construction, and the natural flat-model derived-pullback comparisons. The ordinary reassociation map sends the same local tensors to each other; this calculation identifies the chosen lambda inverse and does not infer it from the existence of an unspecified isomorphism. Naturality of lambda and the equation of Step 4 give the transpose of q after T(alpha_A). The intermediate map e_C is between flat K-flat A-complexes, so applying T to it really is tensoring its chain map with B. The A/B constant-ring identifications are those supplied by exact inverse image.

Step 6 uses the same existing hom formula now with K=E and f=pi_C. Naturality of the ordinary adjunction proves the chain-map differential identity written in the step. Both denominators remain identities; the output is alpha_B after Q(pi_C). Its adjunct is the very same chain map a as in Step 5. The B-pullback is exact, so there is no hidden requirement that D⊗B be flat as a B-complex.

Step 7 is elementary injectivity of that explicitly cited hom bijection, followed by inversion of the two established comparison isomorphisms. The equality it yields has exactly the orientations required for the representation in the question. Step 8 writes the naturality equations for a chain map and takes adjuncts; the cited direct-image and derived-pullback statements explicitly give naturality of the comparison and model identifications. No non-elementary fact is justified only by naming a source.

I tested the formulas on C=0, on a complex concentrated in one degree, on B=A (all coefficient maps are identities), on r=id (projection and comparisons become the evident tensor identification), on empty schemes, and on non-flat Z/4→F_2 with r=id and C=A[0]. In the last test B has infinite projective dimension over A, yet the formula is still the ordinary identity on B, confirming that the proof does not need a finite Tor-dimension assumption. Negative shifts of the one-term test give the same degreewise counit and introduce no tensor sign, because B is in degree zero. No strict or canonical injective resolution was assumed. No claim that pi_C is an isomorphism is needed or added.

All eight proof steps have fewer than 2000 characters. The only generic comparison argument is an explicit substitution into a previously stated hom-bijection formula, used twice; it does not hide a new lemma. Every cited dependency has a literal quotation in citations.json, checked against the statement rather than the proof. The proof dependency list is the exact union of the step dependencies. B1–B9 introduce no new-node issue, C3/C4 were checked by reading those statements, and the off-unit citations are declared as foundational tools. The server review_split check passed. The first complete dry run rejected one citation excerpt because it was shorter than 40 characters; I expanded it to include the preservation-of-kernels clause. In the final C4 pass I also used the ringed-topos derived-pullback statement directly for the natural scalar-extension comparisons: its assertion explicitly retains the B-module action and allows our K-flat first factor with arbitrary B, whereas tensor-descent alone states its initial model comparison for two K-flat factors. The complete dry run is repeated after these repairs.

## Unfinished work

None in the stage-1 split. Existing unsplit descendants remain independent project work; no Lean proof or compilation is claimed.
