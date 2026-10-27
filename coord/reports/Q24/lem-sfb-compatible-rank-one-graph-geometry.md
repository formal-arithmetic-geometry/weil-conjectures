# Stage-1 delivery: lem-sfb-compatible-rank-one-graph-geometry

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-compatible-rank-one-graph-geometry.json`: statement retained verbatim; nine proof steps, status split.
- `dag/nodes/sec-six-functors-basics/lem-sfb-simple-root-generation-mixed-commutation.json`: statement; not in Mathlib; unsplit. Generation by torus and signed simple root groups, Borel choice for a base, and mixed-sign commutation for distinct simple roots.
- `dag/nodes/sec-six-functors-basics/lem-sfb-subdirect-product-reductivity.json`: statement; not in Mathlib; unsplit. A smooth connected closed subdirect product of reductive groups is reductive, without conditions on the projection kernels.
- `dag/nodes/sec-six-functors-basics/lem-sfb-torus-simple-root-isomorphism-criterion.json`: statement; not in Mathlib; unsplit. A general surjective reductive map with an isomorphism on maximal tori and equivariant isomorphic lifts of signed simple root groups is an isomorphism.
- `citations.json`: one entry for each proof-step citation, quoting the cited statement verbatim in full so that all clauses used are visible.
- `searches.jsonl`: actual msearch records, read before entering verdicts. `milne.txt` and `write_split.py` are sandbox-only reading/writing aids, outside the delivered node tree.

## Attachments

None. I searched `lean/WeilConjectures/` for the exact blueprint id and for reductive groups, RootDatum, and rank-one terminology. The rank-one hits concern sheaf ranks, not rank-one reductive subgroup graphs. There is no project declaration stating this item, or any of the three new geometric inputs, to attach. No Lean was written or compiled.

## WANTED

None. All proof sources used are in the local Milne book. These are algebraic-group results, cited by the book's assertion numbers and printed pages; no Stacks result or SGA source is used as a substitute.

## What changed and what was wrong

The item's imported statement is unchanged, including all coroots, the finite-cokernel condition and the empty-base clause. It had no proof. The full root-datum isogeny-realization theorem that created this item is not used, preventing a circular proof.

The only ancestor returned by `tools/blueprint_refs.py ancestor` is None for this inherited chain; the original null from.node and the existing via list are retained, and every new node prepends this item to via. The exact Milne input and its position in the direct-images/alterations/representation-theory chain are stated in from.place and split_report.blueprint. I read the latest blueprint, including its chapter, ctf-stability unit and direct-images proof (3); I did not change a chapter, unit, or route. There is no repair note for the item.

## Source error

Milne's displayed step in 23.22 literally writes the entire rank-one group as its triangular big cell. That equality is false: in SL_2 the product of lower-unitriangular, diagonal and upper-unitriangular matrices has invertible upper-left entry, whereas the Weyl matrix with entries (0,-1;1,0) has upper-left entry zero. The dense-open statement is true. Step 5 states exactly that statement, and step 6 first proves the desired inclusion on this dense open subset, then takes its closure with the remaining factors fixed. Thus the proof follows the intended 23.22 induction without using the false equality. This is an error in the source's displayed proof, not a dispute with the item's statement. No extra hypothesis or weaker conclusion was substituted.

I use the restricted mixed-simple-root assertion in 23.21, not a general claim that commutators of arbitrary root groups have only one weight. For distinct simple alpha and beta, no positive integral combination m alpha - n beta is a root, since its simple-root coefficients have both signs. This is precisely the commuting case required here, in every characteristic.

## What remains

All three new nodes are deliberately statement-only, with no proof or proof dependencies, as required for a one-level split. Their later splits must prove the indicated general algebraic-group facts. There are no unresolved claims within the assembly of this item apart from those explicitly cited inputs. No Mathlib leaf was found.

## Searches and candidate checks

I searched the entire DAG by id, root-subgroup/simple-root concepts, subdirect products, and Milne places 21.21, 21.62, 23.20 and 23.24, inspecting statements and sources rather than merely reports. Whole-blueprint searches used rank-one, simple root, subdirect product, root subgroups, simple root groups and compatible rank. They found no equivalent blueprint statement. The simple-root hits were unrelated boundary nodes. I read the existing root-parametrization, rank-one, root-generation, Bruhat-cell, root-product, centralizer, character-anti-equivalence and group-image statements and reused their actual conclusions.

Each new node and the item have a new LeanFinder search and a second phrasing, a Loogle search, a Mathlib grep and LeanSearch, all run through the required msearch command and recorded exactly. All services answered in this run. The logs are included verbatim in the corresponding search results. The relevant returned source was opened: MonoidHom.graph is the abstract-group construction in Algebra/Group/Graph.lean:158; GeckConstruction.lie_e_f_ne at RootSystem/GeckConstruction/Relations.lean:265 is a characteristic-zero matrix Lie-bracket assertion; HasTrivialRadical at Algebra/Lie/Semisimple/Defs.lean:59 concerns Lie algebras. RootPairing.Equiv concerns abstract root pairings, and RootSystem/Hom.lean:45-47 lists isogenies as TODO. None supplies the geometric statement or a one-line specialization. Goursat and abstract group quotient equivalences do not control a nonreduced group-scheme kernel.

## Not duplicates

lem-sfb-simple-root-generation-mixed-commutation vs lem-sfb-semisimple-root-subgroups-generate: the existing statement generates a semisimple group from ALL root groups; it supplies neither generation from only signed SIMPLE root groups for an arbitrary reductive group, Borel choice for a prescribed base, nor mixed-simple-root commutation.

lem-sfb-simple-root-generation-mixed-commutation vs lem-sfb-reductive-rank-one-reflections: the latter supplies each rank-one group and its reflection, not simple-root generation of the whole reductive group or commutation of different signed simple-root groups.

lem-sfb-subdirect-product-reductivity vs lem-sfb-semisimple-isogeny-invariance: the existing statement assumes a finite kernel and semisimple target; the new statement allows arbitrary projection kernels and reductive targets in a closed subdirect product. Neither statement is a specialization of the other.

lem-sfb-torus-simple-root-isomorphism-criterion vs lem-sfb-isogeny-root-power-laws: the latter assumes a finite scheme-theoretic kernel; the criterion must first rule out a positive-dimensional kernel and then the infinitesimal kernel using its torus and simple-root lifts.

lem-sfb-torus-simple-root-isomorphism-criterion vs lem-sfb-central-isogeny-borel-root-compatibility: the existing statement assumes centrality and finite kernel; the criterion assumes neither and concludes an isomorphism using the root-group lifts.

lem-sfb-torus-simple-root-isomorphism-criterion vs lem-sfb-root-datum-isogeny-realization: the existing statement constructs a map from an isogeny of root data and depends on this item. The new criterion concerns an already given surjective homomorphism and does not construct it or invoke the isogeny existence theorem.

All three new nodes vs lem-sfb-compatible-rank-one-graph-geometry: none mentions compatible graph families or concludes the item's package of generated subgroup, maximal torus and full root datum. The first gives generic root-group structure, the second a subdirect-product criterion, and the third an isomorphism criterion for an existing map between already reductive groups with already maximal tori. The actual triangular-density and centralizer argument remains in steps 4-7 of this item.

## Review by Q24

I read the item against Milne, printed pp.490-492, from construction 23.17 through 23.24 and the paragraph completing 23.18. I also read Section 2h (2.46-2.48, pp.54-55), 21.23, 21.41, 21.62, the normal-subgroup theorem 21.51, the big-cell theorem 21.84, and the root and coroot formulas in 23.5. The three new statements follow respectively 21.41/21.62/23.21, 23.20, and the general argument of 23.24 plus the completion of 23.18. They introduce all their objects and spell out the hypotheses; no auxiliary proof is hidden inside their statements.

Step 1 uses the generation node's explicit empty-base clause and the root-datum conventions of reductive-borel-pair-structure. Its graph calculation is a surjective coordinate map, not an appeal to a missing closed-graph theorem. The remaining torus identification is elementary.

Step 2 uses rank-one-reflections for the smooth connected reductive domains, affine-pointed-map-generated-subgroup for the actual word-kernel construction and reducedness, smooth-geometrically-reduced for the input, and locally-algebraic-group-identity-component for the open-and-closed component and its smooth reduction. These cited statements really contain all four claims. The finite disjoint union is affine and finite type, and its image is inversion-stable even on disconnected test algebras, since inversion preserves each idempotent piece. Each connected generator lands in the identity component, and reducedness kills its nilradical. Minimality then identifies the entire generated subgroup with that smooth component; this avoids an unrecorded appeal to a reduced-group smoothness theorem.

Step 3 uses algebraic-group-homomorphism-factorization for CLOSED scheme-theoretic images and faithful flatness, multiplicative-character-antiduality for the character equivalence and its closed-immersion criterion, the new simple-generation statement for both factors, and the new subdirect-product theorem for reductivity. I checked that the image of h is a closed subgroup of a split torus, hence is of multiplicative type as defined in the cited statement. The surjection on characters of that image inclusion is injective because its composite is h*. Thus h is faithfully flat. The image of the second projection contains every signed simple root group because b is bijective and each f_alpha maps the signed root groups onto them. Smooth connectedness of L is established BEFORE the subdirect criterion is applied. The finite-cokernel assumption is retained; injectivity alone suffices in this particular image argument.

Step 4 repeats the already cited generated-subgroup construction for the signed graph groups, uses root-product coordinates for containment in the positive and negative radicals, and uses the parametrization statement's all-algebras action formula to check normalization. The mixed-commutation node applies in both factors because both Delta_i are bases and b is injective. The rank-one-reflections statement explicitly says its rank-one root set is {alpha,-alpha}; applying the new generation statement to that reductive group proves that S and its two graph root groups generate H_alpha. This is why the smaller graph generators still generate L. No claim that positive SIMPLE groups alone generate an entire unipotent radical is used, which could fail in small characteristic.

Step 5 uses bruhat-longest-cell-charts for its scheme-theoretic open immersion, its representative of the longest element and opposite Borel intersection, reductive-borel-pair-structure for the semidirect Borel decomposition, rank-one-reflections for the two rank-one roots, and borel-root-product-coordinates for the rank-one radicals. Translation converts the longest cell to U^- T U^+; restriction to the three closed subgroup factors makes C locally closed. Thus the proof does not falsely infer openness merely from constructibility of an arbitrary morphism image. The dense rank-one graph cell contains the full graph torus S, not a one-dimensional torus substituted for it.

Step 6 is the explicit word induction of 23.22. Its only extra inputs are mixed commutation and the word-kernel description. I checked n=0, distinct first roots, and the equal-root case; the latter is established on a DENSE rank-one cell and then closed, with the other factors fixed. Both left V,S and right U stability follow directly from the definition of C and normalization. The final use of the generated subgroup is density of all words, which follows from the displayed intersection of word-map kernels in the cited statement. No representability theorem for a stabilizer is assumed. Locally closed plus dense gives open. This is one routine induction, not a separate standard comparison lemma; all nine steps are shorter than 2000 characters.

Step 7 uses torus-centralizer-smooth-connected for ANY torus in a smooth connected group and reductive-torus-self-centralizer in BOTH ambient factors. Their hypotheses hold: L was proved smooth connected, the ambient T_i are maximal, and h was proved faithfully flat, so centralization of its image descends to all T_0 points after faithfully flat extensions. The two ambient big cells have unique coordinates over EVERY algebra; thus J intersection C is exactly S as a subgroup scheme, not only on field points. S is both closed and open in the connected J, proving equality and maximality.

Step 8 uses exactly the new isomorphism criterion and the all-algebras root-action formula already verified in step 4. I checked all criterion hypotheses individually: surjective map, reductive source and target, maximal split tori, torus isomorphism, and the two signed equivariant graph lifts for every simple target root. This prevents the gap in replacing an infinitesimal kernel argument by a bijection on rational points.

Step 9 uses isogeny-root-power-laws for BOTH the isomorphism and its inverse. Their finite kernels are trivial, so that node's hypotheses hold. Composing its root-group polynomial formulas forces the positive exponents to multiply to 1; its coroot formula then identifies the actual cocharacters as well as roots. Integer root coefficients and first-projection uniqueness identify the base and the displayed signed graph subgroups. This is elementary assembly of the cited formulas, with no appeal to the parent's existence theorem.

For edge cases I checked a nontrivial torus (empty Delta), the trivial group, SL_2 with the identity rank-one graph, and in characteristic p the graph of Frobenius on SL_2 (the first projection remains an isomorphism although the second has infinitesimal kernel). I checked the root-group criterion against Frobenius on G_a and the very-special isogeny warning of Milne 23.30: a torus isomorphism alone is insufficient; the criterion additionally requires isomorphic simple-root lifts. Subdirect-product reductivity includes the full product and a Frobenius graph, and does not incorrectly require smooth or reduced projection kernels. No use is made of root DIFFERENTIALS in positive characteristic.

I checked delivery-errors B-E against the files: new nodes are self-contained and statement-only; citations are verbatim and their hypotheses are verified above; no new node is an elementary graph calculation, a duplicate, or the generated-graph theorem in disguise; and the induction and infinitesimal-kernel issue are explicit. The only off-unit generic input is smooth-geometrically-reduced, declared in split_report.tool_uses. No source or project file was edited, no agent started, and no compiler or local forbidden checker was run.
