## Files written

- `dag/nodes/sec-purity-real-sheaves/lem-a1-affine-groupoid-basis-descent.json`: statement; split into six proof steps. Not a Mathlib leaf: searches found tensor-basis and unrelated affine-basis results, but no groupoid basis-descent theorem.
- `citations.json`: all 11 step-to-node citations, with verbatim statement quotations.

No new nodes and no new Mathlib leaves. Existing leaves reused: `lem-weil-pbc-fibre-product-affine-spectra`, `lem-weil-pbc-free-module-base-change-free`, `lem-weil-pbc-algebra-tensor-pushout-universal-property`; definitions `def-weil-affine-spectrum`, `def-weil-pbc-free-module`, and `def-weil-pbc-module-tensor-product`. Added the existing free-module definition to statement dependencies for the basis notion. The statement is unchanged.

## Attachments

None. Searched the entire read-only `WeilConjectures/` tree for the item id, the blueprint tag, `groupoid`, `Groupoid`, `03C8`, and `groupoids-lemma-basis`. No project declaration stating the item was found. The upstream master is not being used as evidence of a completed proof. No Lean file was written or compiled.

## Literature

Read `literature/stacks-project/groupoids.tex`, `lemma-basis` (Tag 03C8), its entire statement and proof, and `lemma-diagram` and `lemma-diagram-pull` for the composition orientation. Read `proposition-finite-flat-equivalence` (Tag 03BM), especially its final paragraph invoking the basis lemma. Checked the tag-label mapping in `tags/tags`. The item is exactly the finite nonempty basis case of 03C8, with the canonical ring isomorphism specified. A groupoid on all test schemes is the groupoid-scheme hypothesis used there; it can be viewed over Spec(Z), so omitting a separately named base scheme adds no restriction or missing compatibility.

Also read Schemes `lemma-fibre-product-affine-schemes` (01I4), including its tensor-product universal-property proof. Read the pinned Mathlib declarations `Module.Basis.baseChange` and `baseChange_apply` at `LinearAlgebra/TensorProduct/Basis.lean:64,73`, `pullbackSpecIso` and both projection identities at `AlgebraicGeometry/Pullbacks.lean:726` onward, and `Algebra.TensorProduct.productMap` and `productMap_apply_tmul` at `RingTheory/TensorProduct/Maps.lean:810,816`. These are the declarations of the existing leaves, not newly created nodes.

WANTED: none.

## Corrections and blueprint route

The unsplit item had an empty proof. Its source statement is correct; no statement dispute, hypothesis change or source correction is needed. The proof now expands the second diagram of 03C8 into basis coefficients. The source uses equalizers to conclude that its right vertical map is an isomorphism; here coefficient comparison proves invariance directly and the identity section recovers the expansion in A. No faithfully flat equalizer theorem is invoked without a node, and no clause has been moved into a new lemma.

Read the chapter and unit records (`sec-purity-real-sheaves`, `sk-p-real-rankin`) and the current `main-20261015` ancestor text `lem-a1-affine-hc0.md` and its proof. The historical ancestry is a supporting chain through the separated-etale-space and finite-flat affine-relation quotient lemmas. This item serves the 03C8 invocation in the final paragraph of 03BM in that chain. It is not the unit key node and no unit realization record is changed. Preserved the item's inherited precise `blueprint.from.place`, `via`, and other metadata; filled `same_as` with the search result, an empty list. Read-only `blueprint_refs.py ancestor` confirmed the ancestor. Searches of the entire blueprint for `groupoid basis`, `03C8`, `groupoid`, `base change basis`, and `tensor product basis`, together with DAG tag/concept/name searches, found no blueprint node stating this item and confirmed the existing generic tensor-basis leaf. The latter avoids an unnecessary child node. All non-definition proof dependencies outside the unit are existing Mathlib leaves; no route exception is requested.

## Mathlib searches

Retained all four searches recorded on the imported item, after reading their results. Also ran the required `msearch.py NZ lem-a1-affine-groupoid-basis-descent` commands for LeanFinder, LeanSearch, Loogle and grep, with a second LeanFinder phrasing using “Hopf algebroid invariant subring” and “equalizer” instead of affine geometric language. Exact queries and complete command output are in the item, the raw `search-item-*.txt` files, and `searches.jsonl`. All services answered successfully. Initial semantic hits confused the algebraic basis with affine-space/topological bases; the second phrasing produced formally unramified tensor calculations, Hopf-algebra tensor structure and a linear-disjointness basis. None has the groupoid/equalizer hypothesis or the two conclusions here. Grep for `groupoid.*basis|basis.*groupoid|HopfAlgebroid` found no declaration. Loogle's invariant-basis-number results concern equality of free-module ranks, not descent of invariant coefficients. No search was fabricated or recorded as an absence after a service failure.

## Review by NZ

I checked B–E with the source and the cited node statements open. No new node is introduced, so there is no statement-only child to check and no duplicate or relabelling of a clause. The original hypotheses suffice; in particular the proof never assumes the groupoid is an equivalence relation, the schemes are nonempty, or any ring is reduced or Noetherian. Inverses and associativity are part of the hypothesis but the calculation needs only identity, source and target compatibility. No SGA source is used.

Step 1 uses `def-weil-affine-spectrum` for contravariant functoriality and the correspondence of affine maps and ring maps. The identity-arrow hypothesis evaluated on U gives epsilon sigma = epsilon tau = identity, and hence both maps are injective. Closure of C under ring operations is checked directly; no invariant-ring theorem is cited implicitly. This is elementary.

Step 2 uses `lem-weil-pbc-fibre-product-affine-spectra` for both the coordinate ring of P and the precise two projection maps. This is not inferred from the bare definition of fibre product. The affine-spectrum statement gives the contravariant composition law, and the module tensor-product definition supplies balancing. Applied to the first factor through sigma and the second through tau, balancing says p0 sigma = p1 tau. The pointwise composition hypothesis, evaluated on P and its two projections, gives Delta sigma = p1 sigma and Delta tau = p0 tau. Those equations follow from the assumed groupoid laws, not from an uncited assertion that a composition square is cartesian.

Step 3 uses exactly the right-tensor clause of `lem-weil-pbc-free-module-base-change-free`: the original module is the FIRST B via sigma; the scalar extension is the SECOND B via tau. Therefore the basis in D consists of tau(x_j) tensor 1, with coefficients in the second B acting through p1. The `def-weil-pbc-free-module` statement says this is existence and uniqueness of coefficients, including a coefficient ring with zero divisors. No field or faithful-flatness assumption is needed.

Step 4 uses that coefficient uniqueness and the equations just established, and cites the basis definition. I checked the two expansions term by term. Delta sends sigma(a_j) to p1 sigma(a_j), whereas p0 sends it to p1 tau(a_j); both send tau(x_j) to the same y_j. Equality in D therefore yields equality of the coefficients IN B, not merely equality after a potentially noninjective map into D. This is a finite-sum calculation from the preceding steps, so it is marked elementary. Invariance of each coefficient is proved here rather than asserted in a child node.

Step 5 uses the definition of a basis. Applying epsilon to step 4 proves spanning over C. For independence, applying tau to a C-linear relation replaces tau(c_j) by sigma(c_j), and the original assumed basis gives c_j = 0 as a coefficient in A. No division, reducedness or nonempty spectrum is used. This is also elementary.

Step 6 uses all three clauses of `lem-weil-pbc-algebra-tensor-pushout-universal-property` for the tensor ring and specified product map. Its hypotheses hold because C is a commutative subring and sigma and tau restrict to the same C-algebra structure on B. The existing base-change-basis leaf gives 1 tensor x_j as an A-basis, with the first A as coefficients. This map sends each basis vector to tau(x_j). I wrote out surjectivity and zero-kernel using the two coordinate expansions, so there is no hidden comparison isomorphism lemma or assumption that an A-module isomorphism was automatically a ring map: it is already a ring map by the cited universal property. Bijectivity consequently gives the ring isomorphism asserted.

Small cases checked: A = 0 forces B = C = 0, and all coefficients, maps and tensor products in the proof are zero; a finite positive-index basis is still legitimate over the zero ring. For rank one, the identity groupoid with a unit x1 recovers its basis over A. For the pair groupoid of A = k x k over k, take the two idempotents as x1,x2; C is diagonal k, and the tensor factors have exactly the orientation of steps 2–4. For the nonreduced pair groupoid of A = k[epsilon]/(epsilon^2) over k, the basis 1,epsilon yields C = k and the same coefficient comparison; nilpotents do not invalidate independence. The proof imposes no extra hypothesis excluding these cases.

Every cited node is quoted verbatim for every step in `citations.json`; I checked the quoted statements against the actual use, not just the citation names. No step exceeds 2000 characters. The central invariant-coefficient comparison is written as two displayed finite-sum formulas, and all non-elementary input is among the existing cited leaves. There was no prior delivery or return to repair; the correction was to supply the missing proof and make tensor-side choices explicit.

## Unfinished work

None in the one-level split. The existing dependencies remain their own nodes. The server dry run passed and saved its durable success receipt for commit 8978bbe8ac. The final packaging checks are rerun on this report before pushing.
