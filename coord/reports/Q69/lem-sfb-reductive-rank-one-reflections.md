# Stage-1 report: lem-sfb-reductive-rank-one-reflections

Group Q69; completed 2026-10-24. Only the sandbox was written. No Lean code, compiler, Lake, build, repository git command, or agent delegation was used.

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-reductive-rank-one-reflections.json`: item, split into ten steps; statement unchanged; no Mathlib match.
- `dag/nodes/sec-six-functors-basics/lem-sfb-reductive-torus-fixed-subgroup.json`: statement-only supporting lemma; no Mathlib match. Any torus centralizer in a reductive group is reductive.
- `dag/nodes/sec-six-functors-basics/lem-sfb-reductive-semisimple-rank-formula.json`: statement-only supporting lemma; no Mathlib match. Quotient maximal torus and semisimple-rank dimension formula.
- `dag/nodes/sec-six-functors-basics/lem-sfb-split-rank-one-classification.json`: statement-only supporting lemma; no Mathlib match. Explicit matrix models of arbitrary reductive pairs of semisimple rank one, with their derived groups.
- `dag/nodes/sec-six-functors-basics/lem-sfb-torus-normalizer-components.json`: statement-only supporting lemma; no Mathlib match. Smooth normalizer and centralizer, same identity component, finite quotient.
- `citations.json`: verbatim statement excerpts for every node used by every proof step.
- `searches.jsonl` and saved search outputs: actual msearch queries and answers. Exploratory searches for a cocharacter-limit theorem and an SL2-cover theorem were retained, but neither became a node; explicit matrix models make those extra black boxes unnecessary.

## Attachments

None. Searched the project library for the exact blueprint tag and for reductive groups, coroots, rank-one groups, tori, and centralizers. There is no declaration giving the item in all characteristics. The upstream Lie-algebra reductivity results concern characteristic zero and a different notion, not group-scheme reductivity.

## Wanted

None. All mathematical sources used are in `literature/milne-algebraic-groups_iAG2017.pdf`.

## Corrections and source errors

The item and its hypotheses were retained. It had no proof. Its assertions are compatible with Milne 21.1--21.2 and 21.11(a)--(e), including positive characteristic.

The displayed statement of Milne Theorem 20.33 omits “of semisimple rank 1”; the book's errata explicitly restore it. Without this condition the claim fails already for the trivial group or a torus. The paragraph following its proof mislabels the derived groups of its three displayed products. The correct derived groups are SL2, PGL2, and SL2 respectively, as follows from perfectness (20.24), determinant, and 20.32. The new classification statement uses the corrected hypothesis and these correct derived subgroups. This is a source typo repair, not a change to the assigned item.

The current blueprint ancestor tool returns `None`: the item's existing `blueprint.from.node` is null. I preserved this convention and the inherited complete route text, prepended the item to each new node's `via`, and appended its precise supporting role. I searched the full imported blueprint using `blueprint_refs.py search` for torus, reductive, centralizer, normalizer, cocharacter, rank one, rank 1, semisimple, and central torus; no blueprint node states one of the new assertions. The unit and chapter records were read and not modified: this is a supporting item, not the unit's key node. The alteration/Steinberg/Haboush route is retained.

## Not duplicates

lem-sfb-reductive-torus-fixed-subgroup vs lem-sfb-torus-centralizer-smooth-connected: the existing node proves smoothness and connectedness for an arbitrary smooth connected ambient group; it does not prove absence of a unipotent radical when the ambient group is reductive.

lem-sfb-reductive-torus-fixed-subgroup vs lem-sfb-reductive-torus-self-centralizer: self-centralization assumes a maximal torus; the new node applies to any torus and proves reductivity of its generally larger centralizer.

lem-sfb-reductive-semisimple-rank-formula vs lem-sfb-reductive-radical-quotient: the existing node constructs the central radical and semisimple quotient, but does not assert that the image of a maximal torus is maximal or the rank dimension formula. The new statement takes an already constructed central radical as input and uses the general quotient-geometry node; it does not depend on the existing radical-quotient proof, which is cyclic relative to this item.

lem-sfb-split-rank-one-classification vs lem-sfb-reductive-root-subgroup-parametrizations: the existing node supplies root subgroups in an arbitrary reductive group; it does not classify semisimple-rank-one groups by explicit matrix models. It also lies on a potential return route through the Borel-pair structure, so it is not used as a substitute for the argument being proved.

lem-sfb-split-rank-one-classification vs lem-sfb-reductive-rank-one-reflections: the new node assumes semisimple rank one and supplies explicit group isomorphisms, not root-centralizer reduction, root-space dimensions, reflection identities, or coroot equivariance. The item's steps derive those assertions by lattice and matrix calculations; none is simply transferred into a new node.

lem-sfb-torus-normalizer-components vs lem-sfb-torus-centralizer-smooth-connected: the existing statement has no normalizer, component comparison, or finiteness conclusion.

lem-sfb-torus-normalizer-components vs lem-sfb-connected-action-torus-rigidity: rigidity only says a connected group acts trivially on a torus; it does not construct the smooth normalizer or identify the normalizer's components. Those are the new node's additional geometric content.

## Review by Q69

I read the item's source, Milne 21.1--21.2 on pp.424--425 and the complete proof of 21.11(a)--(e) on pp.428--430, including its SL2 input 20.32. I read 20.33--20.34 and the SL2 review 20.37--20.40 rather than assuming an abstract root datum, since producing that root datum is the parent's purpose. The four new sources were checked separately: 17.57--17.59 for reductivity of torus centralizers; 17.20 and 19.20--19.21 for maximal quotient tori and the rank formula, together with 17.61--17.62 for the central radical; 20.24, 20.32--20.34 for the matrix classification and correct derived groups; and 12.40 plus 13.10--13.11 for normalizer geometry. The PGL2 scalar quotient was also checked in 5.49; its projective-matrix charts are expanded directly in step 5.

For step 1 I opened the character-antiduality, Gm-weight-decomposition, and reductive self-centralizer nodes. The first really gives the character equivalence, the second a finite decomposition for each coordinate Gm action, and the third equality as subgroup functors, including nonreduced algebras. Iterating the commuting coordinate decompositions gives the full torus decomposition. I wrote the dual-number identification of centralizer tangent vectors with invariant tangent vectors, so it is not an uncited Lie-theoretic black box.

For step 2 the new normalizer node gives exactly the finite quotient by the centralizer; the existing self-centralizer node supplies the needed identification of its denominator with T. The character and cocharacter actions and their pairing compatibility are calculated by composition, and the adjoint weight transport is written explicitly.

For step 3 the existing largest-subtorus node guarantees the subgroup chosen really is the largest torus in the kernel, and character antiduality gives its concrete primitive-character description. I checked this even for a nonprimitive alpha and in characteristic dividing its integer content. The reduced subtorus, not the possibly nonreduced kernel, is used. The character restriction test gives all rationally proportional roots before any reducedness conclusion is used.

For steps 4--5 I verified every source statement's hypotheses: the centralizer is a torus centralizer in a reductive group, T stays maximal in it, and the product lemma allows a maximal-dimension radical construction. The existing perfect-solvable-group theorem supplies its unipotent part with normality in the ambient H, and connected-action rigidity makes the resulting torus central. The new rank-formula node takes this explicitly constructed central radical as input and concerns precisely this quotient. S has codimension one and is central in H; hence the semisimple rank is at most one. If it is zero then T=R(H), and the existing ambient self-centralizer equality forces H=T, contradicting the nonzero alpha summand. This proves rank one instead of assuming it.

For steps 6--9 I checked the full new classification statement, not its proof: it supplies pair isomorphisms with standard diagonal tori and the specified derived subgroups. Its semisimple-rank-one assumption was established in step 5. Step 6 computes actual torus characters on tangent matrices in the three models, using gl2/scalars for PGL2; it does not identify the SL2 and PGL2 Lie algebras in characteristic two. The scalar quotient's projective charts also justify representatives of F-points. Step 7 writes the maps on matrices and kernels and checks the upper unitriangular chart. Surjectivity of SL2 to PGL2 is justified fppf locally by adjoining a square root of the inverse determinant; separability is unnecessary. Step 8 calculates the normalizer by the two torus eigenlines, with diagonal/antidiagonal alternatives. Step 9 checks the reflection formula on an integral character basis: alpha is 2 chi for SL2, chi for PGL2, and e1-e2 for GL2. The central characters contribute zero pairings. All these are explicit computations from the stated models, not new lemmas restating the item's clauses.

For step 10 I reopened character antiduality to check perfectness and separation by characters. Torsion-freeness of X and nonzero alpha prove uniqueness without dividing by 2. Conjugation carries the actual kernel subtorus and centralizer, hence the unique nonidentity local normalizer class, to the corresponding objects for n alpha; the conjugated formula and uniqueness give coroot equivariance. This spells out the transport rather than asserting it.

I tested the trivial group and a pure torus: Phi is empty, step 1 gives only Lie(T), the quotient W is trivial, and the per-root steps are vacuous. For rank-one examples I checked SL2, PGL2, GL2 and each with an additional central torus, including characteristic two where mu2 is nonreduced. The general supporting statements allow S=1 and S=T; the rank formula allows rank zero; the classification requires rank one and r=0 is allowed. No assertion uses only reduced points when it needs a subgroup scheme. No non-elementary proof step exceeds 2000 characters. New nodes contain statements only, every search recorded for them was actually run, and the blueprint/DAG/library searches found no duplicate theorem. All nodes cited by the proof have verbatim excerpts in citations.json; proof_deps is exactly their union.

## Unfinished work

No part of the assigned one-level split remains unfinished. The four new nodes are intentionally unsplit future items. No new Mathlib leaves were found.

## Validation

Server `review_split` passed before packaging. The first full dry run exposed a cycle through the existing radical-quotient proof: its centre theorem cites Borel-pair existence from a node whose root-datum clause depends on this item. I did not edit those other items. Steps 4--5 now reconstruct the needed central radical from three earlier, acyclic statements. Both new rank/classification statements introduce that radical themselves and depend only on general quotient geometry. The required dry run is repeated after this repair.
