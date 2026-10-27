# Worker report: lem-trf-cartesian-subspace-scalar-tower

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-cartesian-subspace-scalar-tower.json`: existing statement node, now split into six steps; no Mathlib match. Statement and statement dependencies retained verbatim. Existing proof metadata and earlier search entries retained, with the actual new searches appended.
- `citations.json`: verbatim statement quotes for both uses of `lem-trf-cartesian-subspace`, in steps 1 and 6.
- `searches.jsonl`: actual msearch.py results for the item, including two semantic phrasings, Loogle and source grep. No new nodes; no new Mathlib leaves.

## Attachments

None. Searched the whole read-only `lean/WeilConjectures/` for the item tag and cartesian norm/subspace/field and orthogonal-basis terminology, including an explicit `--no-ignore` search. No completed declaration stating both clauses was found. The item has no recorded Lean declaration to inspect or attach.

## Literature wanted

WANTED: Bosch–Guentzer–Remmert, Non-Archimedean Analysis, Proposition 2.4.1/5 and Lemma 2.4.3/4 as cited in the item, and the subspace permanence statement cited by `lem-trf-cartesian-subspace` as Proposition 2.3.3/4, for lem-trf-cartesian-subspace-scalar-tower. The purported archival path `literature/bosch-guentzer-remmert-nonarchimedean-analysis.pdf` is absent locally. The Arizona primary-scan URL in the item was tried with the online viewer, which refused the 14 MB content. I did not download a document or claim to read these pages. The proof is accordingly marked `proof_origin.by = agent`, not a reconstruction of unread BGR text.

## What was wrong or missing

The item was unsplit and had no proof. Its first clause is already the statement of the existing node `lem-trf-cartesian-subspace` (which even permits a trivial absolute value). I cite it rather than duplicate it. The second clause needs an actual finite coefficient construction: neither a purely algebraic restriction-of-scalars basis nor real/complex Gram–Schmidt supplies the required max-norm identity. There is no statement dispute, no added hypothesis, and no change to either the unit or the chapter.

The current `literature/blueprint/latest/` ancestor `lem-trf-local-term-locality` and its proof were read, together with the unit and chapter records. Its present route is the contracting-correspondence argument. This item belongs to the historical analytic branch already recorded in its `blueprint.from`; the split only supplies that lower-level input, without treating analytic arguments as a replacement for the current unit proof. All-blueprint searches for `orthogonal basis`, `cartesian norm`, and `ultrametric` found no equivalent imported blueprint node. The broader cartesian search contains scheme and categorical cartesian statements, not this valued-vector-space theorem.

## Not duplicates

lem-trf-cartesian-subspace-scalar-tower vs lem-trf-cartesian-subspace: the existing node gives precisely the subspace clause (1), with weaker hypotheses; it is reused in steps 1 and 6. The item also asserts scalar-tower permanence, proved here by the finite coefficient spaces and the explicit product-family identity. No second subspace node is created.

## Review by NH

I read delivery-errors B–E and checked the six actual proof steps against the statement of every cited node. The only proof dependency is `lem-trf-cartesian-subspace`, whose full statement I opened. It requires a definite ultrametric scalar-homogeneous norm, symmetry, a finite orthogonal ambient basis, and a linear subspace. It assumes neither completeness nor spherical completeness. In step 1 the ambient basis is exactly the hypothesis of clause (1); the one extra written condition, symmetry, follows from homogeneity at -1 and |-1|=1. The node then gives every part of clause (1). In step 6 the ambient space is the explicitly constructed V_0, its basis is established in steps 4–5, its norm is the restriction of the original norm, and K-homogeneity uses the isometric inclusion K into F. Step 3 proves U is an actual K-subspace of V_0. Thus the dependency says exactly what both applications take from it, without using anything inside its proof. Both citations have verbatim quotes in citations.json. It is in the same unit and is not downstream from this item.

Step 2 uses the finite-dimensionality of U to take a finite K-basis. Its F-span M is finite-dimensional because the same finite list spans it; finite deletion of dependent vectors supplies a basis. Only then is the assumed cartesian property of finite-dimensional F-subspaces of W applied, to get e_i. Step 3 uses only finitely many coefficients of those chosen u_j in that basis. Each A_i is a finite-dimensional K-subspace of F, so the stated hypothesis on F/K applies exactly to A_i. Expanding each c_ij in its supplied orthogonal basis proves U is contained in V_0. No extension degree assumption is used.

Step 4 writes the entire norm computation: regrouping finite sums by i, applying F-orthogonality, applying coefficient-space K-orthogonality, moving the fixed nonnegative factor N(e_i) through a finite maximum, and using N(a e_i)=|a|_F N(e_i). The equality of the K and F absolute values on d_iℓ is justified by the isometric-extension hypothesis. Step 5 obtains independence directly from that identity, positivity of the norms of nonzero basis vectors, and definiteness of the absolute value; spanning is the definition of V_0. These are explicit elementary steps, not uncited existence or comparison lemmas. No tensor-product identification, completeness theorem, or assertion that a possibly infinite F/K has a finite K-basis is hidden in them.

For B, there are no new statement nodes to leave unsplit or search; every notion the item needs is inline or in the retained field definition. The source shortage is declared above and no unread source is labelled document-origin. The original Mathlib searches are retained and every appended entry is the exact tool/query and result from msearch.py. I read the returned candidate statements in Mathlib: GramSchmidtOrtho requires RCLike and InnerProductSpace; Basis.restrictScalars at LinearAlgebra/Basis/Submodule.lean:169 is an algebraic basis of a K-span; Basis.norm_isNonarchimedean at Analysis/Normed/Unbundled/FiniteExtension.lean:90 refers to a constructed basis norm. None asserts either clause for the given ultrametric norm. Both semantic phrasings failed to find a matching theorem. For C, the only two cited uses have matching statements and exact quotations; proof_deps is their union, and there is no back edge. For D, the item's scalar-tower argument is written in the item and is not moved into a new node or a copy of a clause. For E, every use of finite-dimensionality and isometry is accounted for above.

I checked W=0 and U=0 (the empty basis), zero A_i (empty coefficient blocks), K=F (the same construction still applies), and coefficient spaces of different dimensions and basis-vector norms. Empty maxima equal zero throughout, each nonempty basis vector has positive norm, and products of a positive norm with a zero coefficient vanish exactly as step 5 uses. None of the steps exceeds 2000 characters; the six proof texts total 2455 characters and contain no omitted standard sub-lemma. No new node was needed after the duplicate search.

## Unfinished work

No mathematical part of this item's one-level split remains unfinished. The existing subspace dependency remains its own DAG item; this delivery does not split or edit it. Local archival BGR pages remain WANTED as above. Required remote dry run and direct delivery follow this report.
