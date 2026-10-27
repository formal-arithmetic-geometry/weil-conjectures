# Stage-1 delivery: lem-sfb-torus-normalizer-components

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-torus-normalizer-components.json: existing statement node, now split in six steps; no Mathlib match for the whole item.
- citations.json: literal full-statement quotations for every dependency cited in every step.

No new nodes or Mathlib leaves. Search outputs and their append-only command log are retained in the sandbox. All work was written in the sandbox; no Lean, compiler, Lake, repository edits or direct git commands were used.

## Attachments

None. Searched lean/WeilConjectures for the blueprint tag and torus/normalizer notions, then read the broader normalizer/centralizer hits. They concern abstract subgroups, matrix centralizer equations, or unrelated fixed-point arguments, and do not state this group-scheme theorem. The completed-proof attachment condition is not met.

## WANTED

None. The needed source is present as literature/milne-algebraic-groups_iAG2017.pdf.

## Corrections and route

The statement is correct and unchanged. Its references to def-weil-field and def-weil-algebraic-closure were missing from stmt_deps; both are now listed. The earlier node had no proof. The inherited blueprint ancestor is null, as confirmed by blueprint_refs.py ancestor; I retained its precise inherited auxiliary place and via chain and confirmed same_as is empty by whole-blueprint searches for normalizer, normaliser, multiplicative type, fixed subscheme and stabilizer. I read the chapter/unit records and the current latest unit text. This supports the inherited rank-one-reflection/Borel-pair prerequisite for the alteration/direct-image branch; it does not replace a chapter or unit argument. This auxiliary is not the unit's key statement, so no unit record is changed.

## Mathlib searches

Retained the item's prior recorded searches and ran the four required command kinds afresh, plus a second semantic phrasing. Read all five output files. LeanFinder and LeanSearch return abstract-group normalizers and their conjugation kernels, Lie normalizers, root-pairing Weyl groups or Galois topology. Loogle returns compiler normalizers and abstract subgroup normalizers. The source grep returns root-system Weyl-group files. None represents the torus normalizer functor, proves its smoothness or identifies scheme-theoretic identity components. The new 2026-10-24 entries use the exact queries and actual printed results. No new node needs searches.

## Not duplicates

No new node is created. In particular, I reused lem-sfb-constant-source-closed-factorization-locus, lem-sfb-diagonalizable-hom-family-rigidity, lem-sfb-group-neutral-component-translates and lem-sfb-torus-centralizer-smooth-connected rather than creating a transporter, rigidity, component or centralizer lemma. I checked their statements and recursively followed their statement/proof dependency edges: none depends on this item.

## Review by Q80

I read Milne, Proposition 1.79 and Proposition 1.83 (printed pp.30--32), the rigidity argument of Theorem 12.36 and Corollary 12.40 (pp.243--244), Corollaries 13.10 and 13.11 (p.257), and the finite-component translation statements around Proposition 1.34 and Corollary 1.35. Corollary 13.11 helps confirm the geometric-point interpretation, but the proof retains the universal algebra-valued functor throughout. Corollary 13.10 is used only through the existing centralizer statement; normalizer smoothness is proved after component equality, so it is not assumed in the rigidity step. No SGA source is used.

In step 1, I opened the full statement of the constant-source factorization node: its parameter locus represents factorization for every test scheme, with a separated finite-type constant source and target. Here S and G are affine finite type, hence separated by the cited affine-source-separated node. The closed subscheme is exactly S inside G and the family is conjugation. The closed-immersion definition gives the quotient-ring test, so testing the universal point proves the all-algebra condition actually represents scheme factorization. The fibre-product definition and closed-immersion base-change node give the intersection with the inverse locus; I added the explicit ideal sum I + inv*(I) to justify closedness without hiding a composition theorem. The two opposite inclusions give equality, not just setwise preservation on F-points.

In step 2, the closed-subgroup definition says exactly that a represented closed subfunctor whose points form subgroups is a closed subgroup scheme. The displayed multiplication calculation and the imposed inverse condition supply this. The closed-immersion statement identifies the affine coordinate algebra as a quotient, and images of generators prove finite type directly. I opened lem-sfb-torus-centralizer-smooth-connected: it covers any torus in a smooth geometrically connected affine finite-type group, without reductivity or maximality. Since F is already algebraically closed, the connectedness hypothesis on G is exactly its geometric connectedness here. Its conclusion supplies smoothness and closed representability of C. Its stronger centralizer-connectedness assertion is not needed. Centralizing implies normalizing on every extension algebra by the definitions.

In step 3, I opened the neutral-component/translation statement and checked that it explicitly has no smoothness or reducedness hypothesis. It gives open-and-closed subgroup structures and connectedness for both N and C. The closed-immersion criterion then supplies affine finite type for N's component. I opened the diagonalizable-family rigidity statement, which likewise explicitly allows a nonreduced parameter scheme: take X=N^circ, base point the identity, and D1=D2=S. The Laurent monomial calculation identifies the split torus Hopf algebra with F[Z^r] and verifies the exact diagonalizable hypothesis, including r=0. The represented normalizer condition restricts conjugation as a morphism to S; the explicit product identity verifies homomorphisms in the S variable. Rigidity then says this morphism equals its value at the identity, including on nilpotent test algebras. I deliberately used this version rather than the smooth-connected-action lemma, because N's smoothness has not yet been established.

In step 4, the neutral-component statement supplies the actual open scheme structures. Continuous images of connected spaces containing the identity lie in its connected component. The cited open-factorization statement therefore gives both maps, not just an equality of underlying sets. Their composites are identities after the subgroup embeddings, so this is equality as subgroup schemes. This is a direct component argument, marked elementary, with its two generic inputs explicitly cited.

In step 5, I read the complete smooth-restriction node: clause (a) restricts the smooth structure morphism of C to its identity component, while clause (c) transports smoothness across the translation isomorphisms supplied by the component node. The smooth-local-on-source node states exactly that smoothness on an open cover implies smoothness of the source morphism. The components are an open cover, and every required translation is over F. These are already Mathlib leaves, so no new local-smoothness fact is introduced.

In step 6, I checked the all-algebra conjugation calculation showing normality of C in N; this just uses the earlier functor definitions and group multiplication. The component node supplies finitely many components, F-rational representatives and actual translation isomorphisms. Pulling back an F-point under the isomorphism puts n_D^{-1}n in N^circ(F), hence in C(F). Thus the finite list surjects onto the quotient cosets. This counts cosets directly, and does not require a representable quotient or a mistaken identification of arbitrary subgroup quotients with components.

For B--E, there are no unsplit new nodes with proofs, undefined new notions, duplicate auxiliary clauses, or unsupported new Mathlib matches. Every non-elementary input is a cited statement whose complete verbatim quotation is in citations.json, and proof_deps is exactly the union of uses. All six steps are under 2000 characters; I checked them for a hidden independent lemma and found none beyond the cited factorization, rigidity, component and smoothness results. The two elementary steps explicitly carry their component/normality/coset arguments. I checked S=1 (N=C=G), G a torus (again N=C=G), and the diagonal torus in SL2 (nontrivial finite normalizer quotient, also in characteristic two). Universal test algebras include F[epsilon]/(epsilon^2); no reduction or inference from F-points is used for the subgroup-scheme equalities. No additional hypothesis has been inserted and no conclusion weakened.

## Unfinished work

None for this one-level stage-1 split. It uses existing DAG prerequisites; their subsequent formalization remains with their own items.

## Preflight repair

The first dry run rejected the phrase "the item's" in step 1 as a self-containment issue. I replaced it with the explicit normalizer notation N_G(S) defined in the statement; the mathematics and dependencies are unchanged.
