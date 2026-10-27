# Stage-1 delivery: lem-trf-simplicial-normalized-acyclic-compatible-boundary

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-simplicial-normalized-acyclic-compatible-boundary.json`: existing statement, split; no Mathlib match. Four proof steps use the existing horn filler and the existing simplex face identity.
- `citations.json`: four verbatim statement quotations, one for every cited node in every step.
- `report.md`: this report. `searches.jsonl` is the unmodified output log maintained by msearch.py.

New nodes: 0. New Mathlib leaves: 0. The residual calculation and the use of the hypothesis about kernels and images are elementary steps, so neither warrants a new node.

## Attachments

None. Searched the live `lean/WeilConjectures/` for the exact blueprint id and for compatible boundaries, normalized acyclicity, and horn filling, including its AlgebraicTopology directory. No declaration states this item. The existing horn-filling node has a Sheaf Lean statement, but that only prescribes all faces except one and is not an attachment for this item.

## WANTED

None. All mathematical source material needed here is available in `literature/stacks-project/simplicial.tex`.

## Corrections and scope

The item was unsplit and no sandbox node or report existed when this work began; only launcher brief markers were present. No delivery process had been launched. I retained the statement, the inherited searches and blueprint ancestry, and added the proof and fresh searches. There is no released repair note for this item. No statement dispute was found.

Stacks 08P1 uses a normalization retaining the last face; this item already explicitly uses positive-face kernels and differential d_0. Accordingly I omit face 0 in the horn step. This is a change of indexing in the source argument, with the corresponding identities written in the proof; it changes no hypothesis or conclusion. The n=1 case is written separately because face maps out of G_0 do not exist. The original acyclicity assumption includes degree zero and is essential for arbitrary pairs of vertices to be boundaries.

I read GOAL.md, the role and stage-1 contract, SETUP.md's three levels and tool-lemma rule, the chapter and unit records, and the current `literature/blueprint/latest/blueprint/sec-trace-formula/sk-i-curve-zero/lem-trf-local-term-locality.md` and its proof. This is a generic simplicial input in the inherited cotangent-resolution branch; it changes no chapter or unit route. The unit's key node is not this item, so no unit binding fields are edited.

## Searches and reuse

I searched the whole DAG for tags 08NZ and 08P1 and the compatible-boundary, horn-filling and normalized-acyclicity notions. The existing `lem-trf-simplicial-abelian-horn-filling` supplies the strict smaller input: its statement has no acyclicity hypothesis and leaves one face unconstrained. `lem-weil-pbc-simplex-face-face-identity` supplies the relation for the order injections. `def-weil-pbc-simplicial-object` defines the contravariant functor, face maps and natural transformations. Blueprint searches with `tools/blueprint_refs.py` for simplicial boundary, normalized and acyclic simplicial did not produce a blueprint statement of this item; the ancestor command confirms `lem-trf-local-term-locality`.

Five fresh searches were run through the required msearch.py command: LeanFinder with the complete statement, Loogle with SimplicialObject and HasLiftingProperty, grep for boundary/horn/acyclic in MooreComplex.lean, LeanSearch with the vanishing-homology formulation, and a second LeanFinder query describing correction of the missing face. The actual output records are appended to mathlib_searches and retained in searches.jsonl. All services answered; none is recorded unavailable. I read the returned declaration types and the local MooreComplex.lean:64-115, DoldKan/Normalized.lean:80-145 and SimplicialSet/KanComplex.lean:35-70. Moore-complex constructions and projection identities do not provide the assertion. SSet.KanComplex.hornFilling assumes KanComplex and fills a horn, rather than all faces under this item's hypothesis. The second formulation also returned horn colimit constructions, which construct maps out of horns, not extensions to the simplex. Thus this is not a one-line specialization of a found Mathlib theorem.

## Not duplicates

No new nodes are proposed, so there are no new/existing same-tag pairs to distinguish. The item is not replaced by a restatement under a fresh id. The existing surjective-quasi-isomorphism boundary-lifting parent depends on this item and is not used in its proof; no circular use of that stronger result occurs.

## Review by Q126

I read the actual proofs of Stacks 08NZ (lemma-simplicial-group-kan, lines 5755-5803) and 08P1 (lemma-qis-simplicial-abelian-groups, lines 5837-5883) and checked their tags in the tags table. The only non-elementary input is the existing horn-filling theorem. No new node needs a source review.

Step 1 cites the statement of `lem-trf-simplicial-abelian-horn-filling`, which explicitly quantifies over n>=1, every missing index k, compatible prescribed faces and a filler of those faces. For k=0 the prescribed indices are exactly 1,...,n. Every compatibility equation it requires is among the item's hypotheses; at n=1 it requires none. It provides u with precisely the asserted positive faces, without an assertion about face 0. This reads the node's statement, not its proof.

Step 2 cites the statements of `def-weil-pbc-simplicial-object` and `lem-weil-pbc-simplex-face-face-identity`. The former is a contravariant functor on the ordered simplex category, and the latter is the equality of the two face-injection composites. Applying the functor reverses composites and gives d_j d_0 = d_0 d_{j+1}. I checked the full range 0<=j<=n-1, including the last value: the boundary equation for (0,j+1), together with d_{j+1}u=a_{j+1}, makes d_j r zero. Thus ALL faces of r vanish, including the last positive face and face zero; merely checking j<=n-2 would be insufficient. The statement's definitions then put r in the normalized group and in the differential kernel. The proof is a displayed substitution, so this step is elementary despite citing a Mathlib face-identity leaf. Both maps out of G_{n-1} exist since this step assumes n>=2.

Step 3 uses no node: at n=1 membership in N(G)_0 and vanishing of partial_0 are explicit definitions in the item's own statement. There is no fictitious d_i:G_0->G_{-1}. This checks the low-degree case instead of silently inheriting the n>=2 calculation.

Step 4 uses the item's assumption with m=n-1, which is nonnegative. Kernel=image means literally that r has a preimage w in N(G)_n; no homology comparison or exactness theorem is being invoked. Positive faces of w vanish by the displayed definition in the statement, and the cited simplicial-object definition in Ab makes every face additive. The two computations d_0(u+w)=a_0 and d_i(u+w)=a_i cover every face. This is elementary and retains the plus sign required by r=a_0-d_0u. There are no hidden choices of a primitive from an unproved existence theorem: this is an ordinary proof using a given surjectivity-on-cycles hypothesis.

I tested n=1 directly: any horn filler for a_1 is corrected by w in ker d_1 with d_0w=a_0-d_0u, which is supplied by exactness at G_0. For n=2 the two residual equations are d_0r=d_0a_1-d_0d_1u=0 and d_1r=d_0a_2-d_0d_2u=0, so both normalization and cycle conditions hold. For the zero simplicial group the construction returns zero. A nonzero constant simplicial abelian group fails acyclicity at degree zero, as it should: not all pairs of distinct vertices are boundaries. This confirms why the degree-zero assumption must not be omitted.

Against delivery-errors B--E: the statement is self-contained and unchanged; there are no new statement-only nodes to audit; all cited notions have existing definitions or are displayed in the item; source tags and labels were checked; all fresh search entries have actual logged calls; no new Mathlib leaf or unproved comparison is asserted; every proof citation was opened and checked against the statement; citations.json quotes are verbatim; proof_deps is the union of uses; no ancestor or child is cited circularly; no clause is moved wholesale into a new node; and all hypotheses, signs and degree bounds are checked above. Every step is below 2000 characters. No non-elementary comparison is hidden in a long step. No forbidden SGA source is used. All writes are confined to the assigned sandbox and no Lean/build tools were run.

## Continuation check by Q126

This session resumed the completed sandbox rather than starting the split again. As required, its first delivery action was the dry run, which exited successfully with `OK (not pushed)` at 376da672f75. Comparing the sandbox item with the current read clone shows changes only to proof, proof_deps, proof_origin, mathlib_searches, status and split_report; the statement, statement dependencies, source, creation record and blueprint fields are retained. No released repair note exists.

I reread the four proof steps, every cited node's complete statement, the current chapter and unit, the latest ancestor blueprint, and the source proofs of 08NZ and 08P1. For the face identity in Step 2, put the face-identity node's degree parameter equal to n-1 and its indices equal to 0 and j+1. Its contravariant image is exactly d_j d_0 = d_0 d_{j+1}, including j=n-1. At n=1 no such identity is used. The correction w exists by the item's own kernel=image hypothesis at degree n-1 and changes only face zero. These checks confirm the previous review and require no mathematical repair. All four citation quotes remain verbatim substrings of the current cited statements, and the proof steps have respectively 354, 473, 229 and 419 characters.

I retained and read all five records in searches.jsonl without rerunning them. I inspected their relevant local Moore-complex, Dold–Kan and Kan-complex declarations: the returned objects and projection comparisons do not give boundary filling, and hornFilling requires a Kan hypothesis and prescribes fewer faces. A fresh read-only search of the project Lean source for the exact item id and its notions found no attachment. No new node was created and no compiler, Lake or build tool was run. The continued review found no B--E fault to repair; the final dry run and push follow this report update.

## Unfinished work

No mathematical subclaim is left unresolved in this split. The resumed session's initial server preflight passed; the updated report is submitted to the final dry run before direct delivery.
