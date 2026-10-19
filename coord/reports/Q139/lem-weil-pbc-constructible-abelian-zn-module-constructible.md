# Stage-1 report: lem-weil-pbc-constructible-abelian-zn-module-constructible

## Files written

- `dag/nodes/sec-proper-base-change/lem-weil-pbc-constructible-abelian-zn-module-constructible.json`: existing statement, now split into five proof steps; no Mathlib match for the whole item.
- No new nodes and no new Mathlib leaves. The split cites existing Mathlib leaves for cyclic module structures and underlying constant module sheaves.
- `citations.json`: 13 step/node entries, checked as verbatim substrings of the respective current node statements.
- `searches.jsonl`: six actual searches made with msearch.py, with results inspected. The original item's historical searches are retained in its node.

## Attachments

None. Searched the source project's `WeilConjectures/` by the exact blueprint tag, the item id, and the notions of constructible abelian sheaves, cyclic coefficients, and finite local constancy. There is no project declaration giving this general-scheme statement and its same-stratification clause. The generic constructible-sheaf framework and the simple-object lemmas do not give this coefficient comparison. The upstream master is reference material, not an attachment source.

## WANTED

None. All sources used are present locally.

## Audit and changes

The item was unsplit with no Lean declaration and no proof. The mathematical statement is unchanged, including arbitrary schemes and the same-stratification assertion. Its inherited explanatory paragraph already describes the correct comparison; the new proof supplies actual dependencies and handles nonempty versus empty cover members explicitly. The inherited text points to an exchange theorem for an inverse-image comparison. The proof uses the more directly applicable existing `prop-weil-pbc-inverse-image-modules-exact` instead, without depending on derived exchange.

The two constructibility definitions here use a single global finite partition. Stacks 03RW uses an affine-local partition; 095E relates these on qcqs schemes. This proof compares the two recorded global-partition notions on the same arbitrary scheme directly; it does not invoke a false qcqs equivalence without a qcqs hypothesis. No statement correction or statement dispute is needed.

Mathlib searches returned condensed-module constant-sheaf functors, generic abelian sheaf categories, and the group-level `AddCommGroup.zmodModule`. These are not the item's constructibility theorem. Loogle returned no matches; grep found no constructible-sheaf statement in Sites or the whole Mathlib source. The second semantic phrasing likewise returned condensed-module APIs. Each actual query and verdict is recorded. No unavailable service was recorded as a negative result.

Searched the whole DAG and blueprint for constructibility, abelian sheaves, cyclic modules, Stacks 03RU and 03RW, and the constant-stalk calculation; read the existing curve-only comparison and the newer finite-local comparison nodes. The curve-only theorem cannot be applied to an arbitrary scheme with no curve structure, and the finite-local cyclic-module theorem is expressed for ModuleCat-valued sheaves. The direct proof through the existing constant-ring module statements avoids an unmentioned change of coefficient encoding. No new node is required. `blueprint.same_as` is empty because there is no blueprint-imported node stating this general-scheme assertion; the related curve-only node is a worker-created specialization.

## Not duplicates

No new nodes. Existing general-purpose facts are cited rather than recreated. In particular the group-level cyclic module construction, constant-module underlying sheaf, and geometric stalk of a constant sheaf all already have nodes. The curve-only `lem-weil-pbc-constructible-torsion-modules-agree` has extra curve hypotheses and an equivalence, while this item's existing statement is the forward same-stratification result for any scheme; no duplicate node is introduced for either.

## Review by Q139

I read the chapter and sk-thm-p1 unit, the current blueprint's finite-pushforward statement and proof in sk-lem-pbc-p1-injective-fibre, its accepted DAG split, and the current blueprint's detailed curve coefficient comparison. This item supplies the elementary coefficient passage below the finite-pushforward node, not a replacement of a unit's proof route. It is not the unit's key node, so no unit record was changed. I read Stacks etale-cohomology.tex at 03RU (`definition-finite-locally-constant`), 03RW (`definition-constructible`), 095E (`lemma-constructible-quasi-compact-quasi-separated`), 03PT (`lemma-stalk-exact`), and 09Z7 (`lemma-constructible-maps-into-constant-general`), and sites-modules.tex at 03CY (`lemma-sheafification-presheaf-modules`), 03D2 (`lemma-pullback-module`), and 03D3 (`lemma-adjoint-push-pull-modules`). Stacks defines the notions but does not state this precise comparison separately, so proof_origin is agent, with the local Stacks text as its source. No SGA source is used.

For step 1 I read the statement of `lem-weil-pbc-sheaves-killed-by-n-zmod-modules`: (2) gives the unique module structure on the very same abelian sheaf under exactly n>=1 and n id=0; (1) gives annihilation of every underlying module sheaf and (3) upgrades abelian maps and their inverses to module maps. No existence or fullness is inferred merely from the definition of a module sheaf.

For step 2 I read `def-weil-pbc-constructible-abelian-sheaf` for exactly the cover and finite abelian group trivializations used. I read all three clauses of `prop-weil-pbc-inverse-image-modules-exact`: (1) identifies the pulled-back constant coefficient ring, (2) identifies the underlying abelian inverse image, and (3) states the functorial properties. The proof applies (1),(2) twice, to the immersion and to each etale cover member, and uses the killed-sheaf statement (1) for annihilation after pullback. Both maps are scheme morphisms, and R=Z/n is commutative, with no noetherian or flatness hypothesis on the schemes. I corrected the draft's casual identification of restriction with sectionwise restriction: the final step cites the inverse-image comparison separately on the etale map, as required by the abelian definition's convention. The restricted module sheaf and the abelian trivialization therefore have precisely the same underlying object up to the indicated canonical isomorphisms.

For step 3 I read `def-weil-algebraic-closure`, whose statement expressly gives existence for every field, and `def-weil-geometric-point`, which identifies a geometric point with a point and a residue-field embedding into an algebraically closed field. These give the geometric point only on a nonempty cover member. I read `lem-weil-pbc-constant-sheaf-geometric-stalk`, whose conclusion is specifically an isomorphism of abelian groups from the constant value to the geometric stalk. I also read `def-weil-pbc-geometric-stalks`, which defines the stalk colimit. The calculation n[s]=[ns]=0 is written out; no unstated exactness or inverse-image stalk theorem is needed. The stalk in this step is taken on U itself, so no unproved identification with a point of Z is used. Empty cover members are discarded, preserving joint surjectivity; on an empty stratum the empty family is a cover.

For step 4 I read `lem-weil-pbc-zmod-module-structure-killed-by-n` (1), giving exactly the module action on the local group now known to be killed by n. I read `lem-weil-pbc-constant-module-sheaf-underlying`: its statement is a canonical underlying abelian isomorphism for the constant sheaf of R-modules for any scheme, commutative R and R-module M, so it applies on U with R=Z/n. It is not merely a definition of a constant sheaf. Finally the sheaf full-linearity statement (3), already read for step 1, applies to H and the constant module sheaf and also to the inverse of their abelian isomorphism. The local finite groups remain finite sets under the new scalar action; no uniform size, connectedness or chosen global constant value is assumed.

For step 5 I read the complete statements of both constructibility definitions. They ask for the identical constructible locally closed strata with the same immersed schemes. The only new requirement on each stratum is an etale cover with finite module values, which step 4 has just constructed. Thus choosing an arbitrary original witnessing stratification proves the every-stratification clause, without refining or replacing that partition. This last step is marked elementary because it only inserts the constructed witnesses into the two definitions; earlier steps using actual comparison theorems are not marked elementary.

I checked the edge cases: n=1 makes every nonempty local group zero and uses the zero coefficient ring, which none of the cited results excludes; the zero sheaf, empty scheme, empty strata and empty cover members work as above. No assumption of qcqs, finite type, connectedness, reducedness, curve dimension, invertibility of n or nonzero coefficients is used. The concrete case A=Z/4 with n=4 gives its usual module and n=2 does not meet the killed-by-n hypothesis. An empty trivializing piece may originally carry A=Z/2 when n=1; that is why one cannot deduce nA=0 there, and why the proof discards such pieces.

I checked delivery-errors B--E against the final files: no new unsplit proof sketches or clauses relabeled as new lemmas; all non-elementary facts have nodes whose statements say what is used; no lemma's proof is substituted for its statement; no tag serves in place of a node; the sole off-unit mathematical comparison is declared under split_report.tool_uses, along with the generic constant-stalk and algebraic-closure existence tools. The item statement remains byte-for-byte unchanged. All proof steps are below 1000 characters, so none reaches the long-step threshold. Citation excerpts are verified verbatim, and the server check_dag preliminary check reports no finding introduced by the sandbox or on its nodes.

## Unfinished work

No mathematical part remains open in this split. The existing dependency nodes retain their current stage states. Server delivery preflight and push are the remaining delivery actions.
