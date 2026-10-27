# Stage-1 worker report

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-projective-automorphism-affine-presentation.json`: split statement, unchanged mathematical statement; nine explicit proof steps. Existing generic DAG results suffice. Zero new nodes and zero new Mathlib leaves.
- `citations.json`: one entry for every step/node pair, quoting the cited statement verbatim.
- `searches.jsonl`: actual Q36 search-command log. The item's earlier Q31 searches remain in its record; Q36 adds six searches without fabricating or repeating the earlier results.

## Attachments

None. Searches in `lean/WeilConjectures/` for the exact blueprint tag, automorphism/projective combinations, general-linear schemes and idempotent matrices found free general-linear schemes, frame independence, Lie-subalgebra projectors and finite-free projector constructions. None gives all clauses for arbitrary finite projective modules, the stated two-matrix algebra, the identity ideal and arbitrary coherent base change. In particular the free general-linear scheme is not an attachment to this item.

## WANTED

None. The proof is explicitly agent-written: Stacks 022W supplies only the finite-free motivating example, not the finite-projective extension. All generic facts used are in the local Stacks source and existing DAG nodes.

## Audit findings and changes

The statement is correct as imported; no STATEMENT-DISPUTED correction was needed. The source field already candidly identifies the direct-summand presentation as an agent extension. It previously had no proof. I supplied both directions of the matrix bijection, the actual formulas for multiplication and inverse, the computation of the identity kernel, and the generatorwise base-change and tower comparison. I added statement dependencies for polynomial rings, finite-presentation morphisms and fibre products, which are notions already in the statement. No existing metadata, Q31 citation or search was deleted.

The source 022W assumes positive free rank and does not establish varying-rank projective representability. I did not cite it as proving those extra clauses: `proof_origin.by` is `agent`, and each extra calculation is in the item. The current `literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md`, especially (3), is the higher route. This auxiliary affine-group calculation does not alter it. The ancestor command reports `blueprint.from.node = None` for this preexisting agent-created chain, so I retained that existing ancestry rather than inventing a blueprint node. Searches of the whole imported blueprint for automorphism and 022W found no equivalent statement; `same_as` remains empty.

## Mathlib search results

Q36 ran LeanFinder twice, LeanSearch, Loogle and source grep twice via the required msearch command and read every output. The first LeanFinder response gives abstract groups and Tannakian automorphisms; the second gives idempotent projections. LeanSearch gives `LinearMap.toMatrixAlgEquiv`, `algEquivMatrix'`, endomorphism rings and matrix-valued endomorphisms. I also read `LinearMap.GeneralLinearGroup.generalLinearEquiv` at `Mathlib/LinearAlgebra/GeneralLinearGroup/Basic.lean:83` and the standard-coordinate matrix equivalence at `Mathlib/LinearAlgebra/Matrix/ToLin.lean:508`. These compare existing algebraic objects; none constructs the representing affine scheme or gives the other clauses. Loogle's well-formed query returns no hits. The broad geometry grep hits projective elliptic-curve formulas; the narrower general-linear/idempotent query has no hits. The old Q31 Loogle query used an unknown identifier, so that legacy entry is not evidence of absence; the fresh successful Loogle and semantic queries supersede it as evidence. All six new search records reproduce the actual logged tool/query/result.

## Not duplicates

No new nodes. Before deciding that none was needed I searched the entire DAG by title/statement for polynomial universal properties, finite presentation, affine-spectrum duality, tensor fibre products, affine permanence and quotient closed immersions. The existing nodes supply exactly those generic facts; the split cites them rather than creating special cases. Whole-blueprint searches used `tools/blueprint_refs.py search` for automorphism and Tag 022W. The explicit matrix argument is the substance of the item, not a new node restating one of its clauses.

## Review by Q36

I read Stacks `groupoids.tex`, Tag 022W, `example-general-linear-group`, including its coordinate multiplication and its base-change paragraph. I checked the limited scope just described against every assertion in the item. For the generic inputs I read `schemes.tex`, Tag 01I4, `lemma-fibre-product-affine-schemes`, and Tag 01IG, `example-closed-immersion-affines`; `morphisms.tex`, Tag 01S7, `lemma-affine-separated`, and Tag 01TP, `definition-finite-presentation`; and `algebra.tex`, Tag 00F3, `definition-finite-type`. I opened the statement of every node appearing in `uses`; the complete verbatim statements are also in `citations.json`. There are no new statement-only nodes whose source or hypotheses remain to check.

Step 1 uses exactly the tensor-product node's universal property, generation by pure tensors and compatibility with composition. I wrote the finite-free coordinate identification and its inverse, so scalar extension of a split inclusion is not inferred from flatness. The hypothesis actually used is `pi=1`, and it gives `p_B i_B=1` over every algebra.

Step 2 takes existence and uniqueness of evaluation from `def-weil-pbc-mv-polynomial-ring`. The factor through the quotient is justified explicitly by the coset formula. This does not cite a definition node for an unstated theorem about solutions: the quotient argument itself is in the step.

Step 3 needs only the previous explicit identities. I checked both inverse products `pUi pVi` and `pVi pUi`, and checked that reconstruction gives the original matrices using both support relations. This is the core proof of the item; it has not been moved into a new clause node. Entrywise scalar extension proves its naturality.

Step 4 uses the full affine-spectrum statement, which explicitly gives the unique ring map underlying every map between spectra, and the fibre-product statement, which explicitly identifies both projections. It applies over an arbitrary affine open of the affine base, so the inverse image is affine as required by the cited definition of affine morphism. No arbitrary-scheme version of Yoneda or map-to-affine theorem is smuggled into this step: the represented functor is on commutative algebras.

Step 5 again uses the affine fibre-product formula and contravariant affine-spectrum correspondence. Polynomial evaluation gives the coordinate maps after the displayed relations have been checked. I checked the reversal `V_2 V_1` in the inverse coordinate of multiplication; using `V_1 V_2` would have been wrong. The group diagrams are verified by equalities on the generators in the corresponding tensor algebras. Thus no generic unquoted theorem transporting group objects through representability is needed.

Step 6 uses precisely the displayed definition of finitely presented algebra, the definition of a finite-presentation morphism (including quasi-separatedness), and clause (3) of `lem-weil-pbc-affine-morphism-permanence`. The whole source and target give the local affine charts. Affineness was proved in step 4, so all hypotheses of permanence are in force. I did not omit quasi-separatedness or infer finite presentation just from finite type.

Step 7 explicitly proves `D_e/J = A` before invoking the quotient-spectrum closed-immersion node. Its statement is exactly for any commutative ring and any ideal, so it applies to `D_e` and `J`. The generator count is finite even for zero rank. Both containments in the identity kernel follow from the two inverse maps on the quotient; a merely set-theoretic identity locus would not suffice.

Step 8 uses the polynomial universal property, the tensor universal property and the affine fibre-product formula. I wrote maps in both directions between the two coordinate algebras and checked them on coefficients and generators. The tensor comparison for modules also has a displayed inverse. Arbitrary base changes are allowed: there is no flatness, reducedness, domain or rank assumption. This is one generatorwise presentation computation, not an unproved general comparison lemma.

Step 9 checks tower coherence on generators and on pure tensors. The comparison for two different choices of splitting is written explicitly, with step 3 proving it is inverse to the opposite change. Its role is the canonicity implicit in naming the representing object. I checked `n=0`, `P=0` with a nonminimal splitting, the zero ring, and varying rank over `A=k x k` with projector `e=(1,0)`: every matrix equation and quotient argument remains valid. The last example would rule out an unjustified reduction to globally free modules or a single constant rank. There is no division by a determinant, localization to a fixed-rank component, or nonzero-ring assumption in the proof.

I checked B1--B10: no new node, self-contained unchanged statement, actual searches, explicit sources, retained ancestry and no false attachment. C1--C8: all non-elementary uses are cited statements, not their proofs, and off-unit generic tools are declared in `split_report.tool_uses`. D1--D5: the argument stays in the item and introduces no restatement node. E1--E7: all hypotheses are verified above; identity ideals, inverse order and scalar-extension coherence are computed rather than asserted. No step exceeds 2000 characters. No source prohibited by the route lock is used. No Lean was written or compiled, and no repository or launcher file was edited.

## Unfinished work

None in the stage-1 split. The delivery receives the maintainer's independent mathematical review after push.
