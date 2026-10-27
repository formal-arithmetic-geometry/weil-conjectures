# Stage-1 report: lem-sfb-complete-dvr-cocharacter-cartan

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-complete-dvr-cocharacter-cartan.json: item, split into four proof steps; no statement change.
- dag/nodes/sec-six-functors-basics/lem-sfb-reductive-nodal-equivariant-torsor-extension.json: statement, unsplit, no Mathlib match. Extends arbitrary equivariant reductive torsors over the punctured nodal test scheme; does not assert a Cartan decomposition.
- dag/nodes/sec-six-functors-basics/lem-sfb-contracting-line-equivariant-torsor-rigidity.json: statement, unsplit, no Mathlib match. Fullness at the origin on the scaling affine line, for arbitrary smooth affine groups and possibly nontrivial fibre torsors.
- dag/nodes/sec-six-functors-basics/lem-sfb-complete-dvr-cocharacter-lifting.json: statement, unsplit, no Mathlib match. Lifts a special-fibre homomorphism for a smooth affine group; asserts no factorization of a rational point.
- dag/nodes/sec-six-functors-basics/lem-sfb-nodal-equivariant-torsor-rigidity.json: statement, unsplit, no Mathlib match. Fullness of restriction at the nodal origin for arbitrary smooth affine groups, not an existence theorem for extensions of torsors on the puncture.
- citations.json: one entry for every step/node pair, quoting the cited statement verbatim.

## Attachments

None. Searched lean/WeilConjectures both for the exact blueprint tag and for cocharacter, reductive group and Cartan decomposition. Cartan--Eilenberg and Lie algebra results are not this assertion. No Lean was written and no compiler or build tool was invoked.

## WANTED

WANTED: Alper, Halpern-Leistner and Heinloth, Cartan--Iwahori--Matsumoto decompositions for reductive groups, https://sites.math.washington.edu/~jarod/papers/iwahori.pdf, entire eight-page paper, especially Section 2 Claim 2, Lemmas 3.3 and 3.6 and Theorem 1.3; for the item and all four new nodes. The PDF is not archived at the inherited literature/alper-halpern-leistner-heinloth-cartan-iwahori-matsumoto.pdf path. I read the author-hosted PDF directly. Following the worker brief for missing local literature, proof_origin.by remains agent. No literature or launcher file was written.

## What needed repair

The item had only a statement and no proof. The stronger arbitrary-residue-field assertion is correct: Theorem 1.3, unlike Theorem 1.1, removes the algebraically closed residue-field hypothesis. I did not specialize to split groups or perfect fields, and did not use the non-complete-DVR theorem. No STATEMENT-DISPUTED correction was needed.

The proof must not assume that a torsor over the residue field is trivial. The contracting-line comparison proves that the particular fibre torsor has a rational point by comparing its value at 1 with its value at 0. I explicitly separated this input from nodal fullness and from cocharacter lifting. Fullness does not mean uniqueness, so both comparison nodes explicitly avoid a uniqueness claim. The final transition and the side on which the integral multipliers occur are written out.

The inherited blueprint.from.node is null. I followed created.item to the end: the chain ends at lem-sfb-admissible-direct-image, created for a module rather than for a DAG node. The required tools/blueprint_refs.py ancestor command returns None. I retained this ancestor result and extended the inherited via list for new nodes. All from.place fields identify the relevant supporting subclaim and the existing det-thm-sf-ctf-stability-direct-images proof (3) route. I read that proof and the unit and chapter in literature/blueprint/latest. This is a supporting prerequisite, not the unit key node, so no unit realization fields were edited.

## Searches and reuse

All new-node Mathlib searches were made with the prescribed msearch.py under Q25 and this item, logged in searches.jsonl; their complete outputs are retained in the sandbox. Each new node has two differently phrased LeanFinder searches, Loogle, a grep in AlgebraicGeometry, and LeanSearch. All services returned responses. No failed service is recorded as absence. The item itself also has two semantic phrasings and all required search kinds in this session, in addition to its inherited searches.

I read all hits. Loogle Torsor gives torsors of abstract groups on types, and equivariant gives monoid algebra, finite-group projection and equivariant maps. Semantic hits concern topological vector/fibre bundles, elementary arithmetic double cosets, valuation uniformizers, fully faithful forgetful functors, or ring maps. None states the new nodes. The strongest plausible lifting hit was Algebra.FormallySmooth.exists_mkₐ_comp_eq_of_isAdicComplete. A follow-up recorded grep located it at Mathlib/RingTheory/Smooth/AdicCompletion.lean:94; I read lines 80--102 and IsAdicComplete.liftAlgHom at RingTheory/AdicCompletion/RingHom.lean:108. These lift maps from a formally smooth algebra into an adically complete ring. They do not construct the smooth Hom scheme of cocharacters, nor prove the Hopf compatibility of a lift, so are supporting candidates rather than one-line matches to the cocharacter-lifting node.

Before creating the nodes I searched the whole DAG's statement text for cocharacters, their lifting, S-completeness, equivariant torsors, punctured surfaces and the named paper. I also ran blueprint_refs.py searches for Cartan, equivariant torsor, one-parameter, cocharacter, torsor, cocharacter lifting, nodal and gluing schemes. There is no blueprint node for these four facts. The torsor and gluing results that do exist have different statements; the general scheme-gluing node is reused in step 1. Searches of project Lean have no group-scheme matches.

## Not duplicates

- lem-sfb-complete-dvr-cocharacter-lifting vs lem-sfb-complete-dvr-torus-cocharacter-conjugacy: the latter conjugates an already defined integral cocharacter into a specified torus; it does not lift a residue-field cocharacter.
- lem-sfb-reductive-nodal-equivariant-torsor-extension vs lem-sfb-split-reductive-dvr-cartan-decomposition: the latter factors rational points in a split-torus setting; the new lemma extends arbitrary equivariant torsors across a codimension-two origin and does not assert Cartan factorization.
- lem-sfb-contracting-line-equivariant-torsor-rigidity vs lem-sfb-nodal-equivariant-torsor-rigidity: the first is over a field on a one-dimensional contracting affine line; the second is over a complete DVR on the two-dimensional nodal test surface and requires degreewise algebraization over that DVR.
- lem-sfb-reductive-nodal-equivariant-torsor-extension vs lem-sfb-nodal-equivariant-torsor-rigidity: extension produces an object from the puncture using reductivity; fullness extends a chosen isomorphism between existing objects from the closed fixed point and needs only smoothness.
- Both rigidity nodes vs lem-sfb-affine-group-torsor-stackification and lem-sfb-action-groupoid-torsor-comparison: the existing nodes describe action-groupoid stackification and equivariant torsor presentations over fields; neither gives restriction fullness on a contracting line or the complete-DVR nodal surface.
- All four new nodes vs lem-sfb-complete-dvr-cocharacter-cartan: none is a factorization theorem or a clause of that factorization. The assembly constructs and glues P_g, proves its closed fibre trivial using the branch, extracts the action homomorphism, lifts it, compares the extended torsors, and computes the transition and the two integral constants.

## Tool use

lem-galois-glue is used as a generic scheme-gluing tool from another unit. Its complete statement gives the compatible charts and uniqueness needed to glue the actions and their identities as well as the underlying scheme. No node of the current unit supplies general Zariski scheme gluing. This use is declared in split_report.tool_uses. The field-only def-sc-group-scheme is used only for its diagrams; all new statements explicitly repeat those diagrams' interpretation over Spec A. The arbitrary-base torsor clause of def-sfb-split-solvable-right-torsors is explicitly independent of its preceding split-solvable-field terminology.

## Review by Q25

I read the full eight-page author-hosted Alper--Halpern-Leistner--Heinloth paper. For the item I checked Theorem 1.3, Definition 3.4 and both paragraphs of Lemma 3.6. For the extension node I read Section 2 Claim 2 and Theorem 1.3 (1) implies (2), where the latter supplies the general-base version without imposing an algebraically closed residue field. For the contracting-line node I read the first converse paragraph of Lemma 3.6, including the comparison with the constant pullback of the fibre torsor. For cocharacter lifting I read the next paragraph's lifting subclaim; I have cited the paper itself and have not cited or used any prohibited seminar source. For nodal fullness I read Lemma 3.3 and its proof, as well as the degreewise calculation of Section 2 Claim 3. The quoted statements are isolated as future statement-only tasks, not repeated as inline arguments of the item.

Step 1 uses lem-galois-glue exactly for effective gluing of the schemes over a two-open Zariski cover with inverse transition maps and cocycle identities. Its statement explicitly supplies the compatible local identifications and uniqueness. I opened its DAG node and current blueprint text. Step 1 also uses the arbitrary-base represented-torsor definition in def-sfb-split-solvable-right-torsors; I opened that node and verified that no split-solvable hypothesis attaches to that clause. The transition is left multiplication so commutes with the right H-action. Equivariance is automatic because the two chart actions leave the group coordinate fixed. The construction is locally the trivial torsor, with compatible identities.

Step 2 uses the exact conclusion of the new reductive-extension statement: a torsor on X and a specified isomorphism over U. Its group hypotheses are all hypotheses of the item. It then uses the new contracting-line statement with P the branch restriction and Q the constant pullback of T. Neither is assumed trivial at 0. Both have the given commuting actions; their special-fibre isomorphism is the identity on T. The branch t=0 has coordinate s of weight +1, and s=1 lies in the original D(s) chart, so the comparison at 1 proves T is trivial over k. This is why the argument works over imperfect or non-algebraically-closed fields.

Step 3 uses the cocharacter-lifting node exactly after constructing a morphism lambda_0 and checking the homomorphism equation on every test scheme. Completeness, smoothness, affineness and finite type are supplied. The model P_lambda is an actual trivial torsor with its explicit diagonal action, not a chosen unspecified existence object. Its closed fibre identifies equivariantly with T by the chosen point. The nodal-fullness statement applies to these two existing torsors and this specified isomorphism at o; it has exactly the required complete-DVR and smooth-affine hypotheses and explicitly gives a lift of the chosen isomorphism.

Step 4 cites no non-elementary result. I checked directly both chart coordinates q_s=lambda(s)^(-1)h and q_t=lambda(t)h. Commutation within the image of the one-parameter group yields q_t=lambda(pi)q_s. An equivariant chart map has left multiplier f, and invariance under the free scaling action forces f to be pulled back from f(1) over A. The overlap identity is c_t g=lambda(pi)c_s, which gives the required two-sided formula without reversing lambda or the integral factors. This is a two-chart computation and does not hide a comparison theorem.

For edge cases I checked H=1, H=G_m with g=pi^d times a unit (d negative and zero included), equal fibre torsors with the identity isomorphism, nontrivial fibre torsors in the two fullness statements, and arbitrary residue characteristic. Fullness is not faithful in general (positive weights can produce distinct extensions), so no uniqueness is claimed. The extension lemma concerns arbitrary torsors, independently of complete-DVR factorization, so it is a smaller geometric input rather than a renamed item. The new nodes have only statements, all notions have direct definitions or statement dependencies, and each quoted statement was reopened when citations.json was written. No proof step exceeds 2000 characters. No target or existing definition was changed.

## Unfinished work

No unfinished part of this one-level split. The four new statement-only nodes remain unsplit as required; proving or further splitting them is future work. The local archival copy is WANTED. Delivery validation results are recorded below after the mandatory dry run.

## Validation

The mandatory deliver.py --no-push invocation exited successfully: OK (not pushed), commit a41a5ac51f4, preflight passed. The server-side review_split probe also passed. The final push uses the same sandbox split and reruns delivery validation.
