# Stage-1 report: lem-sfb-charzero-ad-nilpotence-group-criterion

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-charzero-ad-nilpotence-group-criterion.json`: unchanged statement; five-step explicit lowering-operator construction of a group-scheme central series.
- `dag/nodes/sec-six-functors-basics/lem-sfb-noetherian-lie-engel-criterion.json`: statement, Mathlib leaf. `LieAlgebra.isNilpotent_iff_forall`, Mathlib/Algebra/Lie/Engel.lean:275, with `LieModule.isNilpotent_iff`, Mathlib/Algebra/Lie/Nilpotent.lean:272, identifies nilpotence with termination of the displayed lower central series.
- `dag/nodes/sec-six-functors-basics/lem-sfb-charzero-lie-detects-factorization.json`: statement-only unsplit prerequisite; no Mathlib match. A homomorphism from a connected characteristic-zero group factors through a closed subgroup when its differential does.
- `dag/nodes/sec-six-functors-basics/lem-sfb-charzero-adjoint-differential-central-kernel.json`: statement-only unsplit prerequisite; no Mathlib match. The differential of Ad is ad, and the scheme-theoretic kernel of Ad is central in characteristic zero.
- `citations.json`: verbatim quotations for all five step/node citations.
- `searches.jsonl`: actual msearch.py results. Sandbox-only `write_split.py` assembles the JSON.

## Attachments

None for this item. Searches of the exact blueprint tag and the adjoint/nilpotence notions in `lean/WeilConjectures/` found no project declaration proving this group-scheme criterion. The existing `LieSubalgebra.exists_forall_apply_eq_zero_and_isNilpotent` in WeilConjectures/Mathlib/Algebra/Lie/Engel.lean proves an intrinsic Lie-algebra assertion, not the group criterion; its full proof was read. This delivery uses Mathlib's more direct intrinsic Engel theorem.

## WANTED

WANTED: T. A. Springer, Linear Algebraic Groups (1998), 13.3.5, cited by Milne for details of Proposition 17.80. This is inherited missing literature; no Springer proof is asserted here and no download was made. The complete proof supplied here is explicitly agent-written from Milne's stated ingredients and the verified Mathlib Engel theorem.

## What was wrong or missing

The original item was statement-only and the cited characteristic-zero exclusion in Milne 17.80 is implicit rather than a separately numbered theorem. Milne 10.33 alone only gives dimension inequalities for the centre and does not state equality of the adjoint kernel and the centre. The new adjoint prerequisite explicitly states the characteristic-zero equality actually needed.

No statement dispute, hypothesis change, conclusion change, hollow definition, or unit-route departure was found. The arbitrary-field statement is retained: it is not silently replaced by an algebraically closed-field assertion. No SGA source is used. The inherited blueprint ancestry is broken (`blueprint_refs.py ancestor` reports `from.node = None`); that existing null ancestry is preserved, with the full inherited place and via list extended for the new nodes. Whole-blueprint searches found no node giving the general factorization or adjoint-kernel assertion.

## Not duplicates

lem-sfb-noetherian-lie-engel-criterion vs lem-wf-engel-matrix: the existing statement is the common-kernel and triangular-basis theorem over Qlbar, including solvability; the new leaf is an intrinsic lower-central-series iff for a Noetherian Lie algebra over any commutative ring. It is not a specialization of the Qlbar statement.

lem-sfb-noetherian-lie-engel-criterion vs sk-lem-walg-engel: the blueprint matrix theorem concerns a Lie subalgebra of End(M) and produces a basis and common kernel; it does not state the intrinsic arbitrary-Noetherian-ring iff. The new node states exactly the generalization already in Mathlib.

lem-sfb-charzero-lie-detects-factorization vs lem-sfb-char-zero-differentiation-hom: the existing node detects equivariance of linear maps between representations, and assumes an algebraically closed field. It does not state factorization of a group homomorphism through an arbitrary closed subgroup over an arbitrary characteristic-zero field.

lem-sfb-charzero-adjoint-differential-central-kernel vs lem-sfb-char-zero-differentiation-hom: the existing statement gives Lie functoriality and differentiation of representation morphisms, not the scheme-theoretic kernel/centre equality.

lem-sfb-charzero-adjoint-differential-central-kernel vs lem-sfb-adjoint-kernel-central-quotient-unipotent: the existing node works over an algebraically closed field in all characteristics and constructs a possibly nontrivial unitriangular quotient of ker Ad by Z(G); it does not assert that this quotient is trivial in characteristic zero. The new node works over arbitrary characteristic-zero fields and asserts that equality.

lem-sfb-charzero-adjoint-differential-central-kernel vs def-sfb-adjoint-kernel-points: the existing node only defines the adjoint-kernel point functor, without asserting centrality.

lem-sfb-charzero-adjoint-differential-central-kernel vs lem-sfb-lie-normalizer-centralizer-invariants: the existing statement identifies tangent spaces of centralizers/normalizers with invariant subspaces. It does not assert ker Ad = Z(G).

lem-sfb-charzero-lie-detects-factorization vs lem-ag-cartier-reduced: the existing Cartier node only gives smoothness and reducedness for closed matrix groups over Qlbar. It does not give Lie-detected factorization over arbitrary characteristic-zero fields.

None of the three new nodes restates the item or a clause of its conclusion: Engel produces only Lie nilpotence, factorization is a generic subgroup criterion, and the kernel theorem applies to groups with arbitrary Lie algebra. The item's proof constructs the central series and computes its commutators itself.

## Review by Q141

I read Milne's Proposition 17.80 proof on printed p.378, its surrounding 17.74/17.77 discussion, 10.14-10.15 on pp.190-191, Theorem 10.23 and Remark 10.24 on pp.193-194, Proposition 10.31 on p.196, Cartier Theorem 3.23 on p.71, Engel 14.34(a) on p.290, and the descending central series/Proposition 6.38 on p.133. I also read the current blueprint Engel statement and the project's existing intrinsic Engel Lean proof. The chapter and unit records were read; this item is a remote supporting prerequisite of their alteration route, not their key statement, so no unit realization is changed.

For the Engel leaf I checked the actual declaration and both directions of `LieAlgebra.isNilpotent_iff_forall` at line 275 and the lower-central-series characterization at Nilpotent.lean:272. Its hypotheses are exactly a commutative ring, a Lie algebra, and a Noetherian underlying module. In step 1 the latter follows because the adjoint prerequisite states finite dimensionality over k. The zero-dimensional Lie algebra is permitted; any witness d=0 is increased to d=1. I did not claim that Engel alone integrates a group series.

For the factorization prerequisite I checked the precise fibre-product Lie formula in 10.14, the smoothness hypothesis on the subgroup in 10.15, and Cartier 3.23 over any characteristic-zero field. A future proof takes L=G times_H K. Its Lie space is all Lie(G), it is a finite-type affine closed subgroup of G, Cartier supplies its smoothness, and 10.15 gives L=G. This explains why no smoothness assumption on K or H is added. In positive characteristic Frobenius with K=1 is a counterexample, so characteristic zero is essential and is present in both prerequisite and application. For finite disconnected characteristic-zero G the differential would not detect the full image, explaining why connectedness is retained.

For the adjoint prerequisite I checked that 10.23 explicitly identifies dAd with ad; this is not inferred from the mere definition of a Lie algebra. For the kernel assertion one may pass to an algebraic closure: for n in ker Ad, its centralizer has full Lie algebra, is smooth by Cartier, and is G by 10.15. Thus every geometric point of ker Ad is central; both ker Ad and the scheme centre are smooth/reduced by Cartier, giving their scheme equality, which descends faithfully to k. This is a plan for the unsplit prerequisite, not a claim that 10.33 already states it. The centre's meaning was checked in the existing centre/base-change node. The kernel theorem includes nonreduced test algebras because it states an equality of subgroup schemes, not only equality on geometric points. Examples G=Gm, Ga and GL2 respectively give entire-group kernels for the first two and the scalar centre for GL2; there is no reductivity assumption.

Step-by-step citation audit: step 1 uses only the new Engel statement for termination of C^r, and the adjoint statement for finite dimensionality, bracket and dAd=ad; those assertions occur in the cited statements. Step 2 constructs J and 1+J^i directly: composition lowers the filtration twice, d factors kill V, and the explicit inverse polynomial makes the affine linear translates closed subgroup schemes. No external unipotence or triangularization theorem is used in this step. Step 3 uses the adjoint statement for the differential and the factorization statement exactly with H=GL(V), K=1+J, and source G. All its smoothness, connectedness, affineness, finite-type and characteristic hypotheses hold. Step 4 writes the matrix commutator identity and checks its ideal membership rather than asserting a compatibility without proof. Step 5 pulls back these explicit polynomial subgroup equations and uses the adjoint statement's all-algebras centrality for the final inclusion. This final citation does not use the stronger conclusion of the item or the proof of another node. The proof dependency list is exactly the union of these uses, and citations.json quotes actual substrings for each.

I checked the indexing: G_0 is the pullback of U_1 and equals G; G_(d-1) is the pullback of U_d=1 and equals ker Ad; the appended G_d=1 is reached because that kernel is central. For d=1, the first stage already equals the kernel, so the conclusion is commutativity. For V=0 the endomorphism scheme has one element and its automorphism group is the trivial group; the same construction and kernel lemma apply. The Heisenberg Lie algebra gives a two-step lowering filtration and the matrix power calculation still terminates. Over an arbitrary nonreduced k-algebra, finite inverse polynomials and the identity (st-ts)s^-1 t^-1 remain valid; no density of A-points is used.

I corrected the potential temptation to use an algebraically closed-field differentiation node over k, or to apply a Lie-centre equality to a group kernel. New nodes carry statements only, and the proposed supporting proofs above remain in this report. Every new node has real logged semantic/Loogle/source searches, and candidates were read. New node names, Milne places, adjoint-kernel notions, Noetherian Engel concepts and relevant blueprint keywords were searched across the DAG/blueprint; the differences from nearby existing nodes are stated above. The first delivery dry run required an explicit definition citation and the numeric Mathlib match line for the Engel leaf. I added the field/finite-dimensional specialization with its actual field and Lie definition nodes, and mathlib_match.line=275, after re-reading that declaration. All five proof steps are below 2000 characters; the two explicitly elementary steps are direct polynomial constructions/calculations, and no long step hides a named comparison theorem.

## What could not be finished

No part of the one-level split remains unwritten. The two statement-only prerequisites deliberately remain unsplit for later stage-1 work. No Lean was written and no compiler, Lake or build tool was run. The shared repository and launcher were only read.
