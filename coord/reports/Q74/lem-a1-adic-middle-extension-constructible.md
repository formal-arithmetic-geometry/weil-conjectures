## Worker report

Item: lem-a1-adic-middle-extension-constructible. Group: Q74. Stage 1 only.

### Files written

- dag/nodes/sec-deligne-laumon-a1/lem-a1-adic-middle-extension-constructible.json: statement node, now split; adic open–closed interface reused; no Mathlib match.
- citations.json: one verbatim statement excerpt for every dependency cited by each of the three proof steps.
- report.md: this report. searches.jsonl contains the searches actually run. bhatt-scholze.txt is a sandbox-only extraction of the existing PDF.

## New nodes

None: 0 new nodes and 0 new Mathlib leaves.

### Attachments

None. Searched slopmaster2 WeilConjectures/ for the exact blueprint tag, middleExtension, middle extension, adic/constructible, and the ordinary direct-image theorem. The closest declaration is AlgebraicGeometry.Scheme.isConstructibleSheaf_lowerStar, WeilConjectures/EtaleCohomology/Purity/RealSheaves/Boundary.lean:245. It assumes a finite coefficient ring and uses isFiniteLocallyConstantSheaf_upperStar_middleExtension (line 227), whose proof at line 234 is sorry. It neither proves the adic item nor qualifies as an attachment. No exact tag occurs in dag/lean_names_upstream.json or the upstream master source. Upstream master was used only as reference material.

### Wanted literature

None. No download was needed.

### Findings and changes

The statement is unchanged. Its imported proof was empty. The finite-ring constructibility assertions in lem-wf-dense-open-pi1-surjective(5) and the finite etale formulation of lem-fin-boundary-sheaf must not be treated as the adic assertion. Instead, the already existing lem-a1-qbar-open-closed-cohomology explicitly states the rational/common-finite-stage adic result, the identification with the standard heart, t-exact boundary pullback, and Frobenius compatibility. This is a stronger existing interface, not a new restatement of either clause of this item. The proof now specializes that interface and spells out the induced Weil isomorphisms.

The three generic base-change/openness tools check the geometric domain; they too are declared in split_report.tool_uses, and their dependency closures were checked for a path back to this item. I read Stacks Tags 01KU (schemes-lemma-separated-permanence), 01T4 (morphisms-lemma-base-change-finite-type), 01VB (morphisms-lemma-base-change-smooth), 02NK (morphisms-lemma-base-change-relative-dimension-d), and 0383 (morphisms-lemma-scheme-over-field-universally-open). These statements match exactly the three cited geometry tools.

The generic adic tool is filed in sk-p-dl-a1-perverse, outside this item's sk-i-dl-a1-local unit. Its use is declared in split_report.tool_uses for maintainer review. This retains the unit's localization/local-duality route and supplies the missing constructible input; it does not substitute a perverse-duality argument. A traversal of statement and proof dependencies found no path from that tool back to this item (2441 reachable nodes at the time of inspection).

### Searches and reuse

Searched the whole dag/nodes tree for ordinary/underived/zeroth direct image, t-exact inverse image, constructible hearts, adic coefficients, and boundary stalks, reading the statements of the candidates rather than taking their titles as evidence. The existing open–closed cohomology node gives precisely the needed assertions. Blueprint-wide searches were run with tools/blueprint_refs.py for "constructible direct image", "middle extension", and "open closed cohomology"; the ancestor command returns prop-a1-curve-boundary-sequence. The blueprint search hits for middle extension are either definitions or different results, while the existing tool is a worker-created node already in the DAG. The item's blueprint ancestry and exact first-sentence/finite-boundary places were retained; same_as remains empty.

Read the item's inherited search queries and result lists. Additionally ran the recorded msearch.py LeanSearch, Loogle, grep and two LeanFinder phrasings. The services returned results successfully. Natural-language hits concern Zariski structure-module restriction/pushforward, underlying scheme images, and discrete condensed-module functors; these do not state the adic theorem. Loogle and the first grep returned no hits. The second grep found Mathlib/AlgebraicGeometry/Sites/ElladicCohomology.lean, which I read: lines 63–79 define the constant Z_l coefficient sheaf and its cohomology, not this ordinary-image constructibility assertion. Every appended mathlib_searches query is copied exactly from the command log; inherited entries were retained as inherited research.

### Unfinished work

No part of this one-level split remains unfinished. The reused adic interface is unsplit in the shared DAG and remains its own future item; no proof of that node or Lean implementation is claimed here.

## Not duplicates

No new nodes, so no new/existing pairs arise. In particular, no new copy of lem-a1-qbar-open-closed-cohomology, prop-constructible-truncations, or the finite-coefficient boundary lemmas was created.

## Review by Q74

I read the current main-20261015 prop-a1-curve-boundary-sequence.proof.md, its first sentence applying recollement to K=j_*F and its finite-boundary sentence. I read the unit sk-i-dl-a1-local and the chapter records, the four statement-dependency definitions, and the full statement of lem-a1-qbar-open-closed-cohomology. I also read the relevant local PDF text of Bhatt–Scholze, Lemma 6.7.2, Lemma 6.7.11, Definitions 6.8.3, 6.8.6, 6.8.8, Proposition 6.8.14, and Remark 6.8.15. The last remark is useful here: for a closed immersion or an etale map the coefficient pullback is naive pullback, and the constructible operations are the restrictions of the ambient ones. The PDF is provenance for the existing interface, not a substitute for a cited DAG statement. The source's Proposition 6.8.14 explains why finite-extension/rationalized coefficients, rather than discrete non-torsion etale sheaves, are being used.

Step 1 cites the existing tool's exact sentence that ordinary j_* sends lisse sheaves to constructible sheaves. Its opening paragraphs say that this is the finite-coefficient-field adic category, whose standard heart consists of constructible sheaves and agrees with the pro-etale representative cohomology. def-wf-middle-extension says the item uses exactly ordinary sheaf pushforward. def-weil-constructible-heart defines the intersection of the two standard halves. All three uses are supported by those statements. The perfect base field is k, its characteristic is p different from ell, and the curve is smooth, separated, finite type and pure dimension one; no geometrical connectedness, properness, or affine hypothesis was inserted. Geometric base change preserves these curve hypotheses (separated finite type and smooth relative dimension one); density of the base-changed open follows since the projection to C_0 is open and the inverse image of a dense open under an open map is dense. Step 1 now explicitly cites these geometric setup facts as lem-pod-separated-finite-type-base-change, lem-sbc-smooth-relative-dimension-permanence, and lem-sc-scheme-over-field-universally-open. The statement already fixes this geometric immersion pair.

Step 2 uses the precise t-exactness of i^* from the same tool, not merely a definition of inverse image or the finiteness of a stalk. A t-exact functor preserves both halves and hence the heart; this last inference is elementary from def-weil-constructible-heart. The tool's agreement with ordinary pro-etale representative cohomology makes the resulting sheaf the degree-zero ordinary inverse image B, in the coefficient conventions of def-weil-derived-pullback-tensor-hom. Thus the argument does not take the whole Rj_*F as a heart object. The boundary is the reduced closed complement specified in both statements.

Step 3 uses the tool's explicit scheme-isomorphism invariance and final Frobenius-compatibility sentence, and def-weil-weil-sheaf-complex clause 3. I checked the directions: c goes from Lg_C^*j_*F to j_*Lg_U^*F, so j_*theta after c has target A. The closed comparison b goes from Lg_Z^*i^*A to i^*Lg_C^*A, so i^*theta_A after b has target B. Their inverses exist because the comparisons are induced by automorphisms and theta is an isomorphism. The section description explains why the square for j has an invertible comparison here; no arbitrary-open base-change theorem is assumed. The common-stage compatibility is explicitly in the tool statement, so it is not inferred just from an unproved change of coefficient category. These constructions agree with the structures specified in the item.

I checked B–E: no new statement-only node, elementary node, duplicate, Mathlib leaf, or disguised clause was introduced; every non-elementary operation used in the three steps is in the statements cited there. The eleven citation entries are verbatim substrings, checked against those statements. Proof dependencies are precisely the union of uses. Step lengths are 1530, 646 and 1360 characters, so none exceeds 2000 or hides a separate long comparison lemma. Small cases: F=0 gives A=B=0; U=C gives A=F and the zero sheaf on the empty boundary; an empty curve gives empty coefficient categories; disconnected curves are permitted by the existing tool's hypotheses. Nontrivial inertia is allowed, so no lissity of A across a missing point is asserted. I corrected the initially tempting finite-coefficient route by reusing the already stated adic interface. There was no prior returned delivery and no statement dispute.

### Dry-run verification

The first complete dry run passed at 7a8166f6dc (not pushed). I then made the geometric domain check explicit in Step 1 and added its three existing-node citations, rather than leaving them only in this review. The final dry run below checks that revision before direct push.
