# Stage-1 report: lem-sfb-acyclic-hypercover-pullback-normalization

Group Q16, 2026-10-22. Direct delivery; no other worker was started.

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-acyclic-hypercover-pullback-normalization.json`: statement node, now split into eight steps; statement unchanged; not in Mathlib after two semantic phrasings, Loogle, grep and LeanSearch.
- `citations.json`: one verbatim statement quotation for each step/node pair (21 pairs).
- `report.md`: this report. No new DAG nodes and no Mathlib leaves.

The search command maintains `searches.jsonl`. `write_split.py` is sandbox-only preparation code, not a delivery node. All files were written only in the assigned sandbox.

## Attachments

None. Searched the current `lean/WeilConjectures/` by the exact blueprint tag, by acyclic-hypercover terminology, and by hypercover/derived-comparison terminology. No declaration states all the item's clauses. The project has one-hypercover constructions and specialized finite-coefficient derived adjunctions, which do not give this full augmented simplicial comparison for arbitrary ring sheaves. No sorry declaration was treated as a finished proof.

## WANTED

None. The required sources are present locally; no literature was downloaded.

## Corrections and scope

The imported node had no proof. Its statement is retained in full: arbitrary schemes and commutative ring sheaves, exact inverse image through the specified ring isomorphism, possibly nonaffine weakly contractible terms, arbitrary maps of augmented simplicial objects over h, arbitrary bounded-below injective resolutions, comparisons in the derived category of abelian groups, and coefficient/refinement/composition compatibility. No extra cartesian, qcqs, finite-coefficient, nonempty or affine hypothesis has been introduced.

The proof does not cite an affine-only evaluation theorem, an etale-only injective-row theorem, or the mere existence of a natural derived isomorphism as evidence for its normalization. Instead it proves evaluation exactness from the generic module and sheaf-epimorphism statements, uses the existing general ringed-site matching theorem, and calculates the two comparison squares explicitly.

The chapter and unit records were read. This node is a general homological tool below the open-direct-image/root-tower branch of the inherited unit; no geometric unit step is replaced. The item's inherited blueprint ancestor is null: `tools/blueprint_refs.py ancestor` explicitly printed None. Its concrete inherited `from.place` is retained. Whole-blueprint searches for hypercover, weakly contractible and adjunction were made; the first finds `det-pe-hypercover-complex`, which asserts a natural derived-object comparison, but not the augmentation normalization and cross-site derived-unit identification here. Thus it is not the same statement, and `same_as` remains empty. Off-unit generic tools are declared in `split_report.tool_uses`, not in the maintainer-owned top-level field.

## Not duplicates

No new nodes were created, so there are no new/existing pairs sharing a source tag. Existing general statements were reused throughout. In particular, no separate node was created for exact evaluation, row/column total comparison, resolution independence, or any clause of the item.

## Review by Q16

I read the actual injective-resolution proof of Stacks proetale.tex Tag 09A2, lemma-compute-cohomology. Its two spectral-sequence directions are respectively the column and row arguments in steps 4 and 3; the remaining work is the explicit normalization that the source does not state. I also read sites-cohomology.tex Tag 0946 (lemma-w-contractible), hypercovering.tex Tags 01GE (lemma-acyclic-hypercover-sheaves) and 01GW (lemma-injective-trivial-cech), derived.tex Tag 09T5 (lemma-derived-adjoint-functors), and sites-cohomology.tex Tag 0D6E (lemma-derived-pushforward-composition). The latter two source proofs refer to the partial-derived Hom formula and uniqueness of adjoints; the delivery uses existing DAG statements giving their normalized representative formulas. No SGA source is used. There are no new nodes requiring independent source checks.

For step 1, I opened both total/augmentation definition nodes. They specify the signed differential, actual restriction augmentation, and termwise coefficient maps used here. The commutations in the step are the explicit simplicial and chain-map identities; no acyclicity is claimed there. All diagonal sums used later are finite under the chosen lower bound.

For step 2, I opened all five cited statements. The module-colimits forgetful theorem explicitly gives exactness and sectionwise kernels and assumes sheafification; the pro-etale site statement supplies a small-site presentation where sheafification exists. The two general-site epimorphism statements bridge module epimorphisms to set-sheaf epimorphisms, to which the actual projectivity definition of weak contractibility applies. This avoids imposing the affineness required by det-pe-wc-sections-exact. The remaining cohomology calculation is the kernel/image/quotient computation for an exact additive evaluation functor, written out in the step.

For step 3, the pro-etale topos theorem explicitly supplies the covering axioms and subcanonicity required by the general ringed-hypercover injective-augmentation theorem. That theorem is for ring sheaves and locally solvable matching families, not just etale hypercovers with constant coefficients. Pulling back each matching covering verifies precisely its hypothesis, including degree zero. Its conclusion gives the actual alternating restriction row and augmentation, so the row-augmentation theorem applies with p >= 0 and a common q lower bound N in Ab. It does not require underlying abelian injectivity. The row theorem's countable coproduct assumption holds for abelian groups.

For step 4, I checked the column-comparison statement: it requires simultaneous lower bounds in both directions, which the minimum of the resolution/source bounds supplies. Step 2 gives its fixed-column quasi-isomorphism hypothesis. This proves the two specifically displayed total maps are quasi-isomorphisms, rather than just asserting the existence of an abstract comparison.

For step 5, the bounded-below injective theorem says exactly that the supplied I and J are K-injective; the small ringed-site existence theorem and the right-derived definition supply the universal derived functors and canonical resolution identifications. The K-injective Hom theorem gives the comparison unique up to homotopy, and the generic derived-map theorem identifies the resulting section map with the canonical transition. I checked the total homotopy sign: a coefficient homotopy s becomes (-1)^p s on the pth column; horizontal mixed terms cancel and vertical terms yield ds+sd. The augmentation square is strict. Hence the cancellation proves independence and coefficient naturality with the claimed normalization.

For step 6, I checked the K-injective Hom, exact-left-adjoint/right-adjoint K-injectivity, and partial-derived-adjunction statements. Exactness of h^* is an explicit hypothesis of the item. It makes h^*i a quasi-isomorphism, giving b by the Hom bijection. Transposing gives a, and the representative formula in the partial-derived theorem identifies the transpose of the identity with h_*j after the ordinary unit. The equation ai homotopic to h_*j eta proves that a represents the actual derived unit. It is not an arbitrary adjunction structure on the same underlying functors.

For step 7, I checked the ringed-topoi derived-pushforward composition theorem against the global-sections morphism to the point with ring Z. Its normalization permits identity resolution of h_*J, since step 6 makes this complex K-injective; the comparison is therefore the equality of actual section complexes. This avoids applying an exact-left-adjoint composition theorem to module global sections, whose left adjoint need not be exact over Z. The derived-map computation theorem then identifies Gamma(a) with derived sections of the unit. On each summand I verified G T_U(i) = T_V(j)c_g up to the explicit total homotopy, and G alpha_I = alpha_J Gamma(a) strictly. Cancelling yields the stated formula and direction of the comparison.

For step 8, the refinement maps act by ordinary section restrictions, which commute with both augmentation and resolution maps. I wrote both equalities before cancellation. Coefficient naturality is componentwise and uses step 5. Composition uses the canonical inverse-image composition identification and the equality of successive section restrictions; the already proved map identification transfers that equality to the actual derived-unit maps. This requires no additional acyclicity or cartesian condition.

I checked small cases: zero coefficient sheaf and the zero ring give zero complexes and preserve every equality; the empty base causes no nonempty hypothesis; identity morphisms/refinements give identity section maps; a constant identity hypercover of a weakly contractible base has the usual alternating identity complex with H^0 equal to the sections and positive cohomology zero; arbitrary negative lower bounds cause finite diagonals after taking their minimum. A map from a two-point disjoint union to a point with constant nonzero coefficients induces a diagonal map in degree-zero cohomology, generally not an isomorphism, consistent with the explicit absence of a quasi-isomorphism claim for c_g.

I checked delivery-errors B through E against the files: no new-node form defects, no bare-tag substitute for a non-elementary cited fact, no definition cited for an unstated theorem, no affine/etale/commutative coefficient mismatch, no relabelled clause as a helper lemma, and no unstated transport argument. All eight steps are shorter than 2000 characters. Verbatim quotes were taken directly from every cited node's statement into citations.json; none was fabricated from its proof.

## Unfinished work

No mathematical part of this one-level split remains open. Its cited existing lemmas retain their own DAG statuses; this delivery makes no claim to complete Lean proofs. Required server dry run and push results are recorded by the delivery tool.
