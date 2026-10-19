# Worker report: lem-sfb-ringed-comparison-tensor-adjunction

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-ringed-comparison-tensor-adjunction.json`: statement, split into four proof steps; Mathlib verdict remains no match. No statement or statement-dependency changes.
- `citations.json`: verbatim statement extracts for every step/node citation, including the general lemma's specified-2-isomorphism clause.
- `report.md`: this report. The search command also generated `searches.jsonl` in this sandbox.

New nodes: 0. New Mathlib leaves: 0. No unit file is changed: the item is a child supporting the unit's triangle calculation, not its key statement.

## Attachments

None. The project-source searches by exact item id and by tensor/adjunction, conjugate and ringed-comparison concepts found no declaration of this item. In particular, `WeilConjectures/CategoryTheory/DerivedCategory/RightDerivedFunctor/CompConjugate.lean:46` states `CategoryTheory.Adjunction.rightDerivedFunctorCompIso'_hom_eq_conjugateEquiv` for exact additive left adjoints. It neither gives the tensor clause nor covers arbitrary ringed-topos module pullback, so it is not an attachment. The existing tensor-Hom adjunction declarations likewise do not state this item.

## WANTED

None. All source material needed for this formal deduction is present.

## What was wrong or missing

The imported statement is retained; no statement dispute was found. Its proof was empty. A DAG search for the source tags and comparison concepts found the pre-existing `lem-sfb-ringed-derived-monoidal-comparisons`, created by Q106 for `lem-sfb-ringed-projection-tensor-composition`. Its statement supplies both the single-composite monoidal equation and adjunction normalization, and the compatibility for a specified ring-compatible 2-isomorphism. Reusing it avoids introducing duplicate nodes or moving the two conclusions into new clause-nodes. It is presently unsplit; this delivery does not claim to have proved that dependency or to have closed the item's entire downward reach.

I read the current chapter and unit records and the current main-20261015 triangle statement and proof. The First identity identifies the two direct-image paths and then uses canonical projection/exchange maps. The present argument supplies precisely compatibility of those path identifications with tensor and counit; it does not replace the unit's integration, projection-formula or proper-base-change route. Searches of the whole imported blueprint using `blueprint_refs.py search` for pullback composition, monoidal, conjugate, ringed topoi and tensor compatibility found no blueprint statement giving the full present arbitrary-ringed-topos two-path claim. The item retains its nearest ancestor and precise First-identity place, with `same_as: []`.

## Mathlib searches

All six inherited query texts were rerun using the required Q62 msearch command and their actual results read; the node retains those queries and its no-match verdict. LeanFinder was tried in two phrasings. LeanSearch and Loogle returned ordinary sheaf-module pullback composition and its conjugate equation, not the stated ordinary unbounded derived ringed-topos result. I read `Mathlib/Algebra/Category/ModuleCat/Sheaf/PullbackContinuous.lean:50-85,163-181`: `SheafOfModules.pullbackComp` is an isomorphism of the underived module categories and `SheafOfModules.conjugateEquiv_pullbackComp_inv` is its underived adjunction equation. The second grep's other monoidal pullback hits concern categorical pullbacks and unrelated simplicial/arrow constructions. These are not one-line specializations to the K-flat/K-injective comparisons here. All services used returned results; none was silently treated as unavailable or as absent. No unrun search has been added.

## Not duplicates

No new nodes. In particular, the existing general comparison node is cited, not copied. Its generic one-composite/2-isomorphism assertions are assembled into the two-path identities explicitly in steps 2 and 3. The existing exact-left-adjoint normalization node is not used, because the present statement deliberately makes no such exactness assumption.

## Review by Q62

I read `literature/stacks-project/sites-cohomology.tex`, Lemma Tag 0D6D (`lemma-derived-pullback-composition`, lines 3658ff), Lemma Tag 07A4 (`lemma-pullback-tensor-product`, 3684ff), Lemma Tag 07A6 (`lemma-adjoint`, 3991ff), Lemma Tag 0D6E (`lemma-derived-pushforward-composition`, 4011ff), and the transpose construction in Remark Tag 07A7 (`remark-base-change`). The tag-to-label mapping was checked in `stacks-project/tags/tags`. The pullback proof uses K-flat complexes with flat terms and preservation of those complexes by pullback; the tensor proof uses total tensor complexes; the pushforward proof invokes adjoint uniqueness. Thus I have not identified ringed module pullback with the exact inverse-image functor of abelian sheaves. Stacks does not print this two-path equation verbatim, and the 2-isomorphism coherence is taken from the explicit statement of the existing general comparison lemma. `proof_origin.by` is accordingly `agent` for the formal deduction.

For C3/C4, I opened and read the complete statements of every node used in the steps: `lem-sfb-ringed-derived-monoidal-comparisons`, `def-weil-pbc-adjunction-conjugate`, and `def-weil-pbc-adjunction-mate`. The general lemma has the same small-site universe condition, arbitrary sheaves of commutative rings, ordinary unbounded module derived categories, canonical K-flat tensors/pullbacks, normalized K-injective comparisons and canonical derived adjunctions. Its last sentence explicitly allows nonflat ring maps and unbounded complexes. The required compatibility of the specified 2-isomorphism with structural ring maps is exactly a hypothesis of both it and the item. A dependency traversal of its statement/proof edges did not reach this item, so the new citation introduces no back edge through that lemma.

Step 1 uses the general lemma's composition comparison and its final specified-2-isomorphism clause. These give actual comparisons a_i, kappa_i, s and r, rather than arbitrary endpoint isomorphisms. The definitions theta = a_1 s a_2^{-1} and c = kappa_2 r kappa_1^{-1} expand the comparisons already specified by the item; no new coherence theorem is asserted in this step. The source ring for both composite arrows is that of Y and the target ring is that of W, so the 2-isomorphism clause is well typed even though the intermediate ringed topoi differ.

Step 2 uses the general lemma's displayed monoidal composition equation and its monoidal 2-isomorphism clause. The lemma's left side is exactly d_i a_i by the definition of d_i in the item. I wrote the four-line equality calculation. Its third line is obtained by multiplying the i=2 equation by the indicated inverse isomorphisms; it uses tensor bifunctoriality and does not hide a K-flat replacement or descent argument. This substitution step is elementary relative to the cited equations. Both K and H remain arbitrary objects of D(Y).

Step 3 uses the same general lemma's explicit adjunction normalization and its adjunction-compatible 2-isomorphism clause. I checked types: a_i:Q_i -> P_i has conjugate V_i -> S_i, hence a_i^c = kappa_i^{-1}; s:Q_2 -> Q_1 has conjugate S_1 -> S_2. The conjugate node's statement explicitly reverses composition and preserves inverses, which gives kappa_2 r kappa_1^{-1} in that order. This avoids the common error of conjugating to the inverse direct-image comparison. The adjunctions in use are exactly the composite adjunctions specified by the item and the general lemma, with no change of unit/counit.

Step 4 uses the conjugate node's identification with the identity-intervening mate and the mate node's explicit transpose characterization. Taking G and H to be identity functors, that characterization gives e_1 theta as the transpose. The formula e_2 P_2(c) is the ordinary adjunction transpose of the same c_Z. Equality of these expressions proves the displayed counit equation directly, without citing a definition as though it secretly proved an extra coherence theorem.

I checked B1-B9 and D1-D5 against the actual delivery: there are no new unsplit nodes, duplicate definitions, leaf claims, hidden new-node proof sketches or added dependencies outside the step-use union. Every non-elementary ingredient is one of the cited statements (C1), while the substitutions and transpose unpacking are written out. All four proof steps are shorter than 2000 characters. The JSON uses ordinary single TeX backslashes, and the citations are literal substrings, not paraphrases. No source outside the allowed route, including SGA, is used. No off-unit non-Mathlib tool is needed: the general lemma belongs to this same unit, and the two mate definitions are existing Mathlib leaves.

For E1-E6 I checked zero K or H, zero Z, identical paths with the identity commutation, and a nontrivial specified automorphism of a composite path. The zero cases give equal zero maps, the identity case cancels a_i against its inverse, and the automorphism case retains s and its conjugate r throughout rather than silently replacing the 2-isomorphism by an equality. As a nonflat sanity check, the setting includes module pullback along the ring map Z -> Z/2; its underived module pullback is not exact, but all comparisons used are the K-flat derived ones and no step applies exact-left-adjoint normalization. No finiteness, boundedness, flatness or constructibility assumption was introduced. Nothing was sent back to another worker: this is the author's direct-delivery review, with independent maintainer review still required.

## What remains unfinished

Nothing in the requested one-level split. The general coherence lemma remains its existing unsplit dependency; it is not a new node of this delivery. No Lean was written or compiled, and no live/shared project or launcher file was changed. The required server dry run and push are performed by deliver.py after this report is written.
