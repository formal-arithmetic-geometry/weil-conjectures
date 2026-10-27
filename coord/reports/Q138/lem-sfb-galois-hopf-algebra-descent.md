# Q138: lem-sfb-galois-hopf-algebra-descent

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-galois-hopf-algebra-descent.json: item, split in eight steps.
- dag/nodes/sec-six-functors-basics/lem-sfb-finite-galois-vector-space-descent.json: new statement-only input, unsplit; no Mathlib match after two semantic phrasings, Loogle, LeanSearch and source grep.
- citations.json: verbatim statement quotations covering every cited node in every step.
- searches.jsonl and search-0.txt through search-9.txt: executed-search log and full returned results. The item's earlier Q108 searches are retained unchanged.

## Attachments

None. The blueprint tag is absent from WeilConjectures. Searches for Hopf/Galois descent and semilinear invariant vectors find only matrix-cocycle descent and related finite-dimensional statements, not arbitrary Hopf-algebra descent. Field.galois_invariant_vectors_span covers a locally constant matrix action over a separable closure, not the item's arbitrary L-algebra.

## WANTED

None. Milne's Algebraic Groups PDF and Stacks descent.tex are available locally.

## Statement clarification

STATEMENT-DISPUTED: the imported phrase “commuting with S and epsilon” leaves the target action of epsilon unspecified; read literally as epsilon sigma = epsilon it is false even for B=L. For L=C, k=R, sigma complex conjugation, and epsilon=id, epsilon(sigma(i))=-i differs from epsilon(i)=i. The intended compatibility is epsilon(sigma(b))=sigma(epsilon(b)). I have replaced the phrase by this explicit equation, together with the explicit antipode and comultiplication equations, as required by Milne A.64's compatible semilinear Hopf action. This repairs the ambiguity without changing the intended descent theorem. I also specified “Hopf L-algebra” in the local definition and cited the existing finite-type-algebra definition for the final clause. No target statement is edited.

## Route and sources

Read the chapter and unit records, SETUP's three levels, and the current latest blueprint's sk-thm-sf-ctf-stability/_section.md and sk-thm-sf-ctf-stability-direct-images.proof.md. This is an auxiliary algebraic prerequisite along the already recorded character-antiduality chain; it does not replace a unit-level argument. The current blueprint changes the direct-image discussion, but does not state this auxiliary Hopf descent result. blueprint_refs.py ancestor reports from.node=None, which is preserved, with the full existing provenance via chain and exact place. All new provenance is the item's chain with the item prepended. Searches of the entire imported blueprint for Galois descent, semilinear, vector space, invariant basis and 0CDR produced no equivalent statement.

Read Milne Appendix A.64 on printed pp.580–581, including the arbitrary-vector-space Morita argument and its following Hopf consequence. Also read Proposition 3.36 on printed p.77 for the invariants quasi-inverse, and A.65–A.66 to check what they actually say. A.66 is about separated finite-type schemes; it is not used as an unjustified theorem about arbitrary Hopf morphisms. Instead morphisms are descended directly using A.64. The new node cites Milne A.64 and 3.36, with Stacks Tag 0CDR, descent.tex lemma-galois-descent (and the preceding tensor-square/cocycle discussion), as the equivalent sheaf formulation. Its only mathematical content is vector-space descent: no Hopf, algebra, tensor-invariants compatibility or finite-generation clause has been moved into it.

## Not duplicates

lem-sfb-finite-galois-vector-space-descent vs lem-sfb-galois-stable-subspace-descent: the existing statement descends a stable subspace of a supplied canonical scalar extension; the new one treats an arbitrary semilinear L-vector space and gives natural scalar recovery and the Hom bijection.
lem-sfb-finite-galois-vector-space-descent vs lem-sfb-galois-closed-subscheme-descent: the existing statement concerns closed subschemes of an already given finite-type scheme; the new input is arbitrary vector spaces, without finite-dimensionality or a prior form.
lem-sfb-finite-galois-vector-space-descent vs lem-sfb-galois-descent-affine-subgroups: the existing statement is about subgroup ideals and their inclusion/normality; it does not construct a form of an arbitrary semilinear vector space.
lem-sfb-finite-galois-vector-space-descent vs lem-sc-galois-invariant-vectors-span: the existing result concerns finite-dimensional matrix cocycles over a separable closure and only their spanning assertion; this node gives descent for all vector spaces over a finite Galois extension, including maps and the canonical unit/counit.
lem-sfb-finite-galois-vector-space-descent vs lem-sc-galois-matrix-hilbert90: the existing statement constructs an invariant invertible matrix for a locally constant cocycle over a separable closure, not the arbitrary-vector-space equivalence and natural recovery maps here.
lem-sfb-finite-galois-vector-space-descent vs lem-sfb-galois-hopf-algebra-descent: the new node has no multiplication or Hopf structure and no finiteness-of-algebra clause; the item's steps construct and verify all of these, rather than applying a renamed copy of the item.

## Review by Q138

I read delivery-errors B through E in full and checked each new statement and each proof step against the open source and cited statements. Only the vector-space result is a new unsplit node; it has a self-contained statement, explicit finite normal separable hypotheses, inline semilinearity, all notion dependencies, empty proof and proof_deps, and actual search results. It is not an elementary tensor calculation and not a clause asserting Hopf descent. The existing tensor and algebra leaves are reused. Every proof citation was opened and its exact statement quoted in citations.json. No citation relies on a cited proof instead of its statement.

Step 1 uses the new node's theta isomorphism and unit at k, and the tensor algebra leaf's multiplication formula; thus it proves rather than assumes that the recovered linear map preserves multiplication and identifies the fixed scalar field. Step 2 uses precisely the existing base-change-tensor-distrib isomorphism and its naturality, together with theta and eta from vector descent and the tensor multiplication formula. I wrote out rho for two and three factors and its equivariance, so I did not assume a general commutation of invariants with tensor products. Both factors in base change are k-vector spaces and k to L is a commutative ring map, exactly its hypotheses.

Step 3 restricts epsilon and S and uses chi_2 to construct Delta; equivariance is part of the item's assumptions. It gives the scalar-extension formulas on lambda tensor a. Step 4 applies faithfulness from the new node's actual Hom bijection to maps into A, k, and the triple tensor. It checks each of coassociativity, two counit identities, and two inverse identities, with the formulas supplied by affine-group-coordinate-hopf used only to specify these identities, already required by the item's definition; it does not invoke any converse affine-group construction. Base-change-tensor-distrib gives the needed naturality. Step 5 constructs scalar extension by the explicit operation formulas, checks the canonical action and epsilon's target action, and identifies eta as a Hopf map; it uses the same three leaves and vector-space descent, not a generic category-transfer theorem.

Step 6 uses the Hom bijection and natural tensor comparison to descend Hopf maps. I checked the comultiplication square by applying the injective chi'_2, while epsilon and S are restrictions. Step 7 writes both triangle composites on generators; this is elementary after the already supplied natural isomorphisms, and module-base-change states functoriality. Step 8 uses the finite-type definition's actual polynomial-generation clause and vector descent's faithfulness, not an unproved flatness or finite-type descent assertion. I corrected a possible pitfall here by taking A/A_0 as a vector-space quotient; A_0 is a subalgebra and is generally not an ideal. This argument handles the reverse finite-generation implication without claiming B is finite-dimensional or dividing by the group order.

Small cases checked: L=k gives identity maps; V=0 and arbitrary infinite-dimensional V are permitted by A.64; the tensor comparison on pure tensors is balanced over L; B=L descends to k and forces the corrected epsilon action; scalar extensions of polynomial Hopf algebras may be infinite-dimensional, which the new input allows. Characteristic dividing the Galois group order causes no issue because the split uses no averaging by its inverse. Empty generator sets (B=L) give A=k. All individual proof steps are under 1000 characters, hence none crosses the 2000-character long-step threshold or conceals a long separate argument. No SGA source is used. The proof is honestly marked agent-written because the source states the Hopf consequence without its detailed verification.

## Unfinished work

The new vector-space descent node is intentionally statement-only and remains for a later stage-1 split. No part of the item's Hopf assembly is deferred into a new copy of its own conclusion. No Lean was written and no compiler, Lake, or build was run.
