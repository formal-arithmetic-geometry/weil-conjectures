# Stage-1 delivery: lem-sfb-lie-normalizer-centralizer-invariants

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-lie-normalizer-centralizer-invariants.json — item split into five steps; its statement and statement dependencies are unchanged; no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-affine-group-dual-number-calculus.json — one new statement-only, unsplit node; no Mathlib match.
- citations.json — verbatim statement quotations for each of the four steps citing the new dependency.

## Attachments

None. Searched the project WeilConjectures/ tree for the exact item tag and centralizer/normalizer/Lie notions. The source has infinitesimal-point and tangent-space infrastructure, but no declaration supplies these two full-group-functor invariant identities. The characteristic-zero matrix-group adjoint definitions do not cover this item.

## WANTED

None. Read the existing Milne PDF directly using pdftotext, especially 10.6, 10.11, 10.14, 10.18–10.21 and Proposition 10.34, printed pp.188–193 and 197–198. The normalizer proof is only referred to as similar in Milne; the explicit dual-number proof here is marked agent-written. It does not invoke the external SHS reference, SGA, a quotient-group representability theorem, or a smooth homogeneous-space theorem.

## Problems found and changes

The item was unsplit and supplied no argument. Its statement correctly distinguishes whole group invariants from Lie-algebra invariants, and explicitly assumes representability of C and N; these hypotheses have been retained. Milne's full second proof is omitted. The delivered argument fills that omission rather than making either invariant identity into a new node. Smoothness of H is retained even though the dual-number calculation does not need it. No statement dispute or weakening is needed.

The inherited blueprint.from.node is null. The required blueprint_refs.py ancestor command returned None. Its long existing place and via chain were retained, with a precise source place added for the new dependency. Whole-blueprint searches for tangent, adjoint, dual numbers, augmentation ideal and normalizer found no statement of the required scalar-extended group calculus or either invariant identity. The current literature/blueprint/latest (main-20261024) unit and direct-images proof (3) were read: this is a supporting algebraic-group input beneath the recorded alteration route, not a replacement of the unit's functor arguments. No chapter or unit file was changed.

## Not duplicates

lem-sfb-affine-group-dual-number-calculus vs lem-sfb-lie-normalizer-centralizer-invariants: the new node constructs the scalar-extended identity tangent kernel and its group law and adjoint action; it mentions neither centralizer nor normalizer nor either invariant identity. The item proves the two identities by all-algebra tests and specialization.

lem-sfb-affine-group-dual-number-calculus vs lem-ag-lie-equivalence-multiplication: the existing node says the arbitrary-base infinitesimal-point/Lie equivalence carries multiplication to addition; it does not identify that Lie module with the scalar extension of the field tangent space or assert a rational adjoint representation and its subgroup compatibility. It does not subsume the new node. Its multiplication clause is acknowledged as overlapping infrastructure, not used as evidence for the missing clauses.

lem-sfb-affine-group-dual-number-calculus vs def-wf-lie-algebra-derivation: the definition restricts to algebraically closed characteristic zero and matrix groups, and its adjoint formula is at field-valued points. The new statement treats arbitrary fields, finite-type affine group schemes, arbitrary commutative test algebras, and the scalar-extension compatibility. Applying that definition would add hypotheses absent here.

lem-sfb-affine-group-dual-number-calculus vs lem-sc-rational-point-tangent-derivation-identification: the existing node identifies a rational-point tangent vector with a local cotangent functional. It does not state the arbitrary-algebra identity kernel, its functorial group law, or its regular adjoint action.

## Review by Q18

I checked the item against Milne Proposition 10.34, reading both printed pages 197–198. The centralizer proof tests first R[delta], then specializes delta to the nilpotent element in an arbitrary D-algebra; the delivered proof reproduces those two quantified directions with distinct epsilon and delta. I also read the chapter and unit records, the current latest unit/direct-images text, SETUP's three levels, and delivery-errors B through E (including the repeated new-target sections).

For the new node I read Milne 10.6 (augmentation cotangent dual), 10.11 (addition and scalar multiplication), 10.14 (closed-subgroup tangent injection), and 10.18–10.21 (base algebra kernel and adjoint naturality). The proof material for its future split is as follows, recorded here, not in its statement: for coordinate algebra A with counit c and I=ker c, tangent points over R are maps a to c(a)+delta D(a), where D kills I^2 and is k-linear on I/I^2. Finite type makes I/I^2 finite-dimensional. Thus Hom_k(I/I^2,R) is its field dual tensor R, naturally even when R is not finitely generated. The coproduct unit identities make the product coefficient D+D'; the counit and antipode give zero and negation. Precomposition by a group homomorphism gives naturality; the surjection of augmentation cotangent spaces for a closed subgroup gives the tangent injection. Conjugation acts on the augmentation cotangent space, producing a matrix of regular functions and an inverse from inversion in J, so it is a group-scheme representation. Milne's finitely-generated-R exposition in 10.18 does not impose a limitation on the coordinate computation in 10.19. No Lie bracket is needed.

For step 1 I checked that the new node's actual statement asserts finite dimension, injectivity, adjoint linearity and naturality for subgroup inclusions. This gives H-stability. Quotient rationality is explicitly obtained from the quotient matrix block; choosing a basis of h extended to g also verifies the quotient-kernel formula after every R. This avoids silently importing a flatness theorem or exactness of invariants.

For step 2 I checked that its citation gives precisely the E bijection, its naturality, and its conjugation formula, not merely a definition of tangent space. The centralizer property used is the stated functor evaluated at D, and the algebra R[delta] is indeed a D-algebra by epsilon to delta. Conversely S[delta] to S exists because epsilon_S squared is zero. Neither K nor C is assumed smooth. Thus the statement's full test-algebra quantifiers, including nonreduced algebras, are preserved.

For step 3 I checked the cited subgroup-kernel equality, addition, inverse and conjugation formulas. Normalizing H implies E(v)hE(-v)h^{-1} belongs to H and reduces to its identity; the cited equality therefore gives exactly membership of v-Ad(h)v in h tensor R. H is a subgroup of N by its own group law, not by an unquoted normalizer theorem. Step 1's basis calculation changes this membership to quotient fixedness.

For step 4 the same cited formulas are applied with R=S before specializing delta to epsilon_S. This is essential: no false assertion that an arbitrary D-algebra is free over D is made. The resulting commutator lies in H(S), hence conjugation preserves H(S) in one direction. Replacing v by -v proves the reverse inclusion. Consequently the result is equality of subgroup functors, exactly the hypothesis defining N(D), not preservation of its field points or of its Lie subalgebra alone. This step contains the missing normalizer argument itself and does not delegate that clause to the new node.

Step 5 is elementary assembly: it restricts a surjective vector-space quotient to the inverse image of a subspace, with kernel h. It explicitly lifts each invariant class using the quotient definition and applies step 4, so it does not assume that taking group invariants is right exact. It cites no extra node and uses no unproved comparison. All four non-elementary steps cite the one general calculus statement, and citations.json copies its exact statement. No step exceeds 2000 characters.

I tested the identities for H trivial (N=G and h=0), H=G (both quotient sides zero), and K trivial (C=G). For a commutative G all conjugation is trivial and C=N=G for any allowed subgroups, as the formulas require. For a finite etale subgroup H, h=0, so the normalizer tangent formula becomes g^H, confirming that disconnected-group invariants rather than only Lie invariants are essential. For mu_p in G_m in characteristic p, the new calculus has L=k and E_R(a)=1+delta a; (1+delta a)^p=1, so the no-smoothness claim on its group input passes this nonreduced test. The zero test algebra gives singleton kernels and zero modules. No division by a characteristic or infinitesimal parameter occurs.

Mathlib searches were executed only through msearch.py and retained in searches.jsonl. I read all search hits. The closest hits were LieSubalgebra.normalizer, LieSubmodule.normalizer, GroupLieAlgebra, KaehlerDifferential maps and algebra-extension cotangent lemmas. I read the Normalizer definitions and the headers/types of GroupLieAlgebra and Lie.BaseChange: the former are abstract Lie algebra invariants or analytic manifolds and the latter extends an already supplied Lie algebra, not scheme tangent points. None is an exact or one-line match. Two semantic phrasings were run for the item and for the new dependency, along with Loogle, LeanSearch and source grep. No unavailable service is called a negative result. Every recorded new-node query has a matching actual log entry.

## Unfinished work

No stage-1 split work remains. The one new node is deliberately statement-only and unsplit, as required for a one-level split. No Lean was written and no compiler or Lake command was run. The required server dry run and delivery are the remaining mechanical validation actions.
