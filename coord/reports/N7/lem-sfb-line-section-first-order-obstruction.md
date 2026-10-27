# Stage-1 delivery: lem-sfb-line-section-first-order-obstruction

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-line-section-first-order-obstruction.json`: statement, split; retains its statement and inherited metadata; eight proof steps, with existing generic dependencies only. Five actual fresh search queries are appended to the inherited searches.
- `citations.json`: one statement quotation for each of the 14 step/node citation pairs.
- `report.md`: this report. `searches.jsonl` was written by the authorized msearch command.

New nodes: 0. New Mathlib leaves: 0.

## Attachments

None. Searched the full `lean/WeilConjectures/` tree for the exact blueprint tag, Serre-duality names, and section-obstruction terminology. Curve/TracePairing and Curve/RiemannRoch supply duality tools; PrincipalThickeningObstruction supplies a different ideal-section obstruction sequence. None states the line-deformation obstruction together with its Serre multiplication and arbitrary two-term-model formulas. The item therefore is not an attachment.

## WANTED

None. The proof is marked agent-written: 0C6R supplies the deformation context, not the section or complex-model calculation verbatim.

## Problems found and changes

The item had no proof. No statement error was established, and its statement is unchanged. The meaning of the transition convention is now explicit: e_j=t_ij e_i, and a_ij s_j is the expression in the j-frame. The source calculation at Stacks 0B8S uses the opposite sign from the existing module boundary/Cech-compatibility node; I follow the latter, spelling out lift j minus lift i. The final convention sentence means that the comparison convention for v changes too; reversing the boundary alone would not preserve the displayed formula.

The smaller statement `thm-sc-serre-duality-curve` gives the canonical isomorphisms but does not explicitly state the naturality formula used here. The proof consequently cites `det-thm-picard-duality`, whose statement does give it. Similarly the projection formula's objectwise isomorphisms alone do not justify the connecting-map comparison: `lem-weil-pbc-ringed-projection-mate-exact` states that its canonical counit mate gives a morphism of triangles, including that square. These are C4 distinctions, not alternative proof routes.

The ancestor command returns None for the inherited created.item chain. The item already had blueprint.from.node=null and a detailed place/via list. I retained that metadata and checked the current `literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md`, especially (3), together with its chapter/unit records. This is the existing Picard/theta prerequisite within that inherited direct-image route. No chapter or unit was edited. Searches of the entire imported blueprint for Serre duality, section obstruction, and first order found no statement of this item; Serre duality is an existing generic tool.

## Not duplicates

No new nodes were created. The existing local-lift boundary, Cech naturality, natural Serre-duality, projection, affine derived equivalence, K-flatness, and split-complex boundary nodes cover the needed generic lemmas. The transition multiplication and lift-independence calculations remain steps, rather than new nodes restating clauses of the item.

## Review by N7

I read Stacks more-morphisms.tex 0C6R (lemma-picard-group-first-order-thickening), including its map f to 1+f. I read curves.tex 0BS2 (lemma-duality-dim-1), especially functoriality (5) and differentials (6), and 0BS4 (remark-rework-duality-locally-free), and the latest blueprint det-thm-picard-duality's naturality statement. For the model calculation I read perfect.tex 08EU (lemma-cohomology-base-change, which is the quasi-coherent projection formula despite its label) and 06Z0 (lemma-affine-compare-bounded), homology.tex 011J and 011K (lemma-ses-termwise-split-cochain and lemma-ses-termwise-split-long-cochain), derived.tex 0152 (lemma-derived-canonical-delta-functor), and sites-cohomology.tex 06YU (definition-derived-tor and preceding construction) and 0B56 (equation-projection-formula-map). I also read homology.tex 015Z and the bounded-flat/K-flat statement at sites-cohomology.tex 06YQ (lemma-bounded-flat-K-flat), and more-algebra.tex 064K (lemma-derived-tor-quasi-isomorphism). No SGA source is used.

Step 1 uses exactly the statement of lem-sp-right-adjoint-preserves-injectives: extension to the split rank-two algebra is exact, so restriction preserves injectives. This gives an identification using the same injective resolutions, and hence also identifies the boundaries on C and C_A. The common topology, the split algebra, and the epsilon kernel sequence are checked on affine opens explicitly. This avoids silently identifying module categories with different structure rings.

Step 2 is the local transition calculation: the difference of the chosen lifts is epsilon times t_ij a_ij s_j in the i-frame. The cocycle equation and its image under multiplication by s are written out. It needs no black-box lemma.

Step 3 uses lem-sc-boundary-cech-compatibility's actual local-lift statement, with its stated sign, on the exact O_C-module sequence of step 1. It then uses lem-sc-cech-h1-map-natural's actual cochain-level naturality to identify the result with H^1(m_s)(v). Neither node is being asked to assert affine acyclicity or that an arbitrary cover computes all cohomology.

Step 4 uses the naturality equation in det-thm-picard-duality for the specific map O_C to L and degree 1. O_C and L are finite locally free, C is smooth proper and connected of pure dimension 1, and k is algebraically closed, so the hypotheses apply. The dual map is checked in a local frame to be multiplication by s. This supplies the pairing formula without an uncited cup-product identification.

Step 5 uses the canonical short-exact-sequence triangle of lem-weil-pbc-complex-ses-triangle on the A-modules k, A, k. Derived tensor exactness is part of lem-weil-pbc-ringed-projection-mate-exact. On every affine trivializing open, R tensor_k A is A-free, so the coefficient tensor has no higher Tor and its maps are exactly epsilon and reduction; their gluing gives the line-extension triangle. This uses flatness of the actual deformation, not a claim that k is A-flat (it is not).

Step 6 uses lem-pc-projection-formula only under its stated qcqs and quasi-coherent hypotheses: f is projective and L_A is invertible, while all three coefficient objects are quasi-coherent. The separate exact-mate node explicitly supplies the connecting square for the same counit-mate maps, with its normalization at the coefficient unit. The affine-equivalence node applies to Spec A and explicitly is triangulated. Finally def-sc-module-cohomology-boundary defines the boundary by this derived triangle, so this is the required boundary, rather than a dimension comparison or an arbitrary isomorphism of groups.

Step 7 uses lem-pc-module-bounded-flat-kflat for the bounded finite free model. After restriction of scalars to k, its coefficient sequence is degreewise split, so lem-weil-pbc-complex-ses-connecting-formula applies literally. Its projection of d_A of a lift is division by epsilon. The exact tensor node preserves the cone connecting arrow, so this formula is the boundary identified in step 6. The end groups are ker d_0 and coker d_0 since the model is in degrees 0 and 1.

Step 8 checks the difference of two lifts directly: division by epsilon changes the representative by d_0 of the reduction of their difference. Model independence is functoriality of the derived tensor triangles from the already cited exact tensor node, under the cohomology identifications induced by the specified model equivalence. I also checked the simultaneous sign convention as described above.

I tested the argument on a constant deformation (a=0), s=0, t=0, negative-degree bundles with H^0=0, large-degree bundles with H^1=0, and P^1 with H^1(O)=0. On a genus-one curve with L=O, s=1, it gives partial_v(1)=v, fixing the nonzero sign test. For a model with one-dimensional terms and differential epsilon b, it gives exactly x maps to bx; changing the lift adds a d_0-boundary. Adding an acyclic free summand changes neither cohomology nor this map. Characteristic 2 causes no division by 2 and the same formulas work. No vanishing or finite-free model existence beyond the statement's conditional hypothesis was used.

Every cited node's statement was opened and read; citations.json quotes it verbatim. I checked B through E: no new unsearched nodes, no clause moved wholesale to another node, no non-elementary uncited comparison, no dropped hypotheses, and no tags used to stand in for a dependency. Each proof step is below 2000 characters. The generic off-unit tools are listed in split_report.tool_uses for maintainer review, without setting the maintainer's top-level tool_uses field.

## Unfinished work

None in the mathematical split. The required server checks and delivery are run after this report is written; their final outcome is reported by the delivery tool.
