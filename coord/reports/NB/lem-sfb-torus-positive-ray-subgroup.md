# Stage-1 report: lem-sfb-torus-positive-ray-subgroup

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-torus-positive-ray-subgroup.json: statement, split in eight steps; no Mathlib match for the item.
- dag/nodes/sec-six-functors-basics/lem-sfb-pid-submodule-smith-bases.json: statement, Mathlib leaf; Submodule.exists_smith_normal_form_of_le, Mathlib/LinearAlgebra/FreeModule/PID.lean:492--497. Arbitrary-rank inclusion N <= O, including zero submodules.
- citations.json: one verbatim statement quote per cited node per proof step.

## Attachments

None. Searches of lean/WeilConjectures for the blueprint tag, positive rays, cocharacters, torus weights and unipotent groups found no project declaration giving the item. GroupScheme/Lie.lean concerns group-scheme Lie algebra constructions, not integration of ray weights. An abstract Lie-module theorem and an analytic torus theorem cannot attach this item.

## WANTED

None. The mathematical literature used is present locally.

## Findings and route

The statement and stmt_deps are unchanged. No STATEMENT-DISPUTED issue was found. Read Milne Algebraic Groups, Proposition 16.64 and its preceding construction, printed pp.348--349, as well as Theorem 12.9 and Theorem 12.12, pp.233--235, and Theorem 13.41/Corollary 13.42, pp.269--270. Proposition 16.64(b)'s short generated-subgroup argument does not itself justify an equality of tangent spaces in positive characteristic. The delivered proof avoids using that unproved inference: construct U_K inside K by the same fixed-torus/cocharacter procedure and apply Corollary 13.42 to U_K -> K. Clause (a) uses the same criterion on U_K -> U_eta. This retains the source's construction and both comparison conclusions. Unipotence comes directly from the existing cocharacter theorem, so a separate application or new copy of Proposition 16.62 is unnecessary.

The latest blueprint was read at literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md and sk-thm-sf-ctf-stability-direct-images.proof.md. Its direct-image compactification route (3) is the ancestor purpose of the supporting alteration/moduli/PGL/group-structure chain already in the node. Neither the chapter nor the unit was changed. The existing from.node=null is the ancestor tool's actual answer, not a missing guessed blueprint id. The exact from.place and via chain were retained and extended for the new leaf.

DAG searches used positive ray, character line, primitive character, character coordinates, Smith normal form, cocharacter, fixed subgroups, torus centralizers and relevant Milne places. Whole-blueprint searches used tools/blueprint_refs.py search for torus, positive ray, centralizer, weight, cocharacter, character, primitive character, character coordinates and Smith normal form. No imported blueprint node states the new arbitrary-rank PID statement or the item. The existing DVR and full-rank PID leaves were read; neither can be specialized to a rank-one submodule of a higher-rank free Z-module. The new leaf is the genuinely more general Mathlib statement needed here. Exploratory torus-coordinate searches were also run and logged; their results concern arithmetic characters or analytic tori, not split torus group schemes. The proof does not create a torus-coordinate lemma, because its coordinate conclusion follows immediately from Smith bases and existing antiduality.

## Not duplicates

lem-sfb-pid-submodule-smith-bases vs lem-sc-dvr-saturation-line-smith-normal-form: the existing leaf assumes a discrete valuation ring; the new leaf applies to Z, which is not local and hence is not a DVR.

lem-sfb-pid-submodule-smith-bases vs lem-sfb-full-rank-pid-smith-bases: the existing leaf assumes equal ranks; the new leaf allows arbitrary N <= O and is used for a rank-one submodule of a rank-r lattice, with r possibly larger than one.

lem-sfb-pid-submodule-smith-bases vs lem-sfb-dvr-matrix-smith-powers: the existing node requires a DVR and states a rectangular matrix diagonalization by powers of its uniformizer; the new leaf states submodule bases over an arbitrary PID.

lem-sfb-pid-submodule-smith-bases vs lem-sfb-continuous-integral-matrix-local-smith: the existing node concerns locally constant module type of continuous p-adic matrix families; there is no topological family in the new leaf.

## Review by NB

I read the actual statement of each cited node, rather than treating its title or proof as an interface. Step 1 uses lem-sfb-multiplicative-character-antiduality for characters, their lattice and the resulting isomorphism of split group schemes, and the new Mathlib leaf for adapted bases of Z eta inside X. In the pinned source at PID.lean:492--497, the theorem has arbitrary N <= O, finite ambient basis, domain and PID hypotheses and exactly the two bases and scalar formula stated in the new node. Z satisfies these hypotheses. The one-vector basis of Z eta is eta up to sign, so the choice eta=d epsilon_1 with d>0 is justified, rather than assumed. The displayed restriction and positivity tests are integer coordinate equations. The case r=0 has no nonzero eta and is vacuous; r=1 gives the trivial torus T.

Step 2 uses only lem-sfb-gm-representation-weight-basis, whose statement gives the group-character decomposition in every characteristic. The successive decomposition argument is written with its base and refinement step, and explains why commuting factors preserve previous weight spaces. This applies equally to Lie(K), since K is S-stable. The coordinate comparison, not differentials of characters, proves the intersection formula.

Step 3 writes out the semidirect product and its inverse. Its smoothness uses precisely the smooth torus projection stated in lem-trf-split-lattice-torus-projection and composition stated in lem-trf-smooth-composition. Its connectedness uses precisely the component bijection in lem-weil-pbc-geometrically-connected-product-components, after checking geometric connectedness of the split torus by its Laurent coordinate domain after every field extension. These are generic tools from other units, declared in split_report.tool_uses with their reasons. No proof route above this supporting node was replaced. All groups remain affine of finite type, and the same checks apply to K.

Step 4 uses lem-sfb-torus-centralizer-smooth-connected, which allows any torus and requires no reductivity or maximality. T is an internal torus in the smooth connected semidirect product. Over algebraically closed F the geometric-connectedness hypothesis holds. I checked the commuting equation on arbitrary A and A'/A; its dual-number version gives the tangent invariant subspace explicitly. No reductive-centralizer node is substituted here. For K the construction is the centralizer inside K semidirect S, not an intersection asserted smooth without proof.

Step 5 applies lem-sfb-cocharacter-limit-smooth-structure only to the smooth connected internal centralizers C and C_K. Its statement supplies smoothness, connectedness, closedness, unipotence and the positive tangent formula. The projection argument proves the contracting subgroup actually lies inside H, and inside K respectively. Commuting torus actions show S-stability directly on all test algebras. Functoriality of extensions proves U_K <= U_eta; it is not inferred from tangent containment.

Steps 6 and 7 use lem-sfb-positive-weight-equivariant-inverse, whose statement I read in full. It asserts an isomorphism for smooth connected affine finite-type schemes, an equivariant map fixing the chosen point, isomorphic differential and strictly positive source tangent weights; it explicitly permits zero tangent space. All hypotheses follow from steps 2--5 and the displayed tangent equalities. In step 6 its target is U_eta; in step 7 its target is K. Thus the two applications prove the two required subgroup inclusions without any assertion that infinitesimal tangent containment alone determines arbitrary subgroups. Step 8 is elementary application of the two implications.

For small cases, I checked H=1 and an absent ray (all resulting tangent spaces zero), a trivial S-action (again V_eta=0), H=G_a with weight p in characteristic p, and H=G_a^2 with weights eta and p eta. Character p is nonzero even though its differential is zero; the construction includes it correctly. A disconnected finite subgroup and alpha_p are excluded from K by the connected/smooth hypotheses, as required; the proof never uses them as smooth comparison groups. Negative multiples are removed by the positive cocharacter condition, not by an absolute-value convention. For the new Smith leaf I checked N=0, O=0, N=O, and N=2Z inside Z^2. These are all included in the actual Mathlib theorem.

Against delivery-errors B--E: the only new node is a complete self-contained statement with empty proof/dependencies of proof and an exact, line-checked Mathlib match. It introduces its ring, module, submodules and bases, and uses the existing basis definition. There is no new clause-copy of the item, no new elementary-fact node and no new unsupported torus construction. Every recorded search is an actual msearch.py query and results are retained verbatim in search files; available unrelated hits are not reported as unavailable. Every citation in every step has its verbatim statement in citations.json. I checked existing dependency closures for cycles back to the item; none of the reused lemmas depends on it. Each step is under 2000 characters. No SGA source, Lean edits, compiler, build, repository write, launcher edit or manually run git command was used.

## What remains unfinished

No part of this one-level split is unfinished. General lemmas reused as dependencies retain their own independently reviewed or queued statuses; they are not being reproved in this delivery.
