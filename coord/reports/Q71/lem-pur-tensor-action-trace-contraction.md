# Q71 stage-1 report: lem-pur-tensor-action-trace-contraction

## Files written

- `dag/nodes/sec-smooth-purity/lem-pur-tensor-action-trace-contraction.json`: statement item, now split into five explicit steps; no Mathlib match for the complete two-functor identity.
- `citations.json`: one verbatim statement excerpt for each node used by each proof step.
- `report.md`: this report. `searches.jsonl` is the search command's own record; `write_split.py` is a sandbox-only drafting helper.

No new nodes and no new Mathlib leaves. The pre-existing Mathlib leaf `lem-coef-monoidal-structural-coherence` is reused.

## Attachments

None. I searched `lean/WeilConjectures/` for the item's blueprint tag and the tensor-action / trace-contraction terminology, and checked the SixFunctors and CategoryTheory projection/trace hits. None states the displayed equality. Tensor actions on additive functors and scalar modules are different notions. The item's own existing record contains no Lean declaration or completed-proof claim.

## WANTED

None. The blueprint, the Stacks category chapter, and the relevant Mathlib source are locally available.

## Problems found and repairs

The item was an unsplit statement with no proof. Its source explicitly says the formula is an agent expansion, not a formula printed in the blueprint. I retained that distinction: `proof_origin.by` is `agent`, and each proof step identifies the expansion or the actual structural coherence source. The statement, its hypotheses, statement dependencies, source, creation information and blueprint ancestry are unchanged.

The main gap to fill was the meaning of canonical reassociation when an arbitrary coefficient functional is contracted. Step 2 now separates associator naturality in that functional from the purely structural unitor equality. It does not use the coherence theorem for arbitrary generating morphisms. Step 4 writes the naturality square with the precise coefficient arrow `a`, rather than asserting that the maps are compatible without calculation.

The initial named Loogle query `CategoryTheory.MonoidalCategory.leftUnitor_tensor` was rejected as an unknown identifier. I retained its actual outcome and followed it with the successful quoted-name search `"leftUnitor_tensor_hom"`. This was not a service outage and supplies no evidence of absence. The successful searches find the structural unitor identity only, not the full item. The original seven inherited search records are preserved; all eight searches run in this attempt are appended exactly as logged. Two distinct semantic phrasings for the complete item returned linear-algebra traces, rigid coevaluation identities, Cartesian structural formulas or unrelated factorization results, rather than this arbitrary two-functor statement.

## Unfinished work

None for this stage-1 item. There is no Lean writing or compilation in this delivery. The server-side `review_split` preliminary check passed. All five steps are below 2000 characters.

## Not duplicates

No node was created. Before considering a separate left-unitor coherence leaf I searched the whole DAG for unitors, associators and the Mathlib names, and searched all blueprint nodes using `trace contraction`, `tensor action`, `unitor`, `left unit`, `unit coherence` and `structural coherence`. I found and reused the more general `lem-coef-monoidal-structural-coherence`. The nearby `lem-sc-scheme-canonical-shift-unit-associativity` concerns a specific shift comparison on scheme-derived categories, and `lem-sf-ringed-derived-native-tensor` concerns construction of a derived tensor; neither is the arbitrary monoidal coherence theorem needed here. The existing parent `lem-pur-composite-integration-counit` requires geometric compact supports, adjunctions and an actual compositor, and depends on this item; it is not used to prove this item.

## Review by Q71

I read `GOAL.md`, the worker brief and stage-1 contract, the three levels in `SETUP.md`, both copies of delivery-errors B through E, the smooth-purity chapter/unit records, the current main-20261015 chapter and unit text, and the complete `lem-pur-projection-purity-agreement.proof.md`. The last sentence of the latter is the source location served here. I also read the current parent `lem-pur-composite-integration-counit` to check where this general contraction identity is used. The proof stays at that formal calculation; it introduces no replacement route to purity.

For the two definition citations I opened the complete statements of `def-sfb-monoidal-category` and `def-sfb-strong-monoidal-functor`. I read Stacks `categories.tex` at `definition-monoidal-category` (0FFK), `definition-functor-monoidal-categories` (0FFL), and `lemma-monoidal-coherence` (0HAY), including part (2) and the following explanation of structural coherence. I checked those tags against the local tag table. I opened the full statement of `lem-coef-monoidal-structural-coherence`: it gives equality for two structural arrows with identical formal endpoints, precisely what the unitor calculation requires. I also read Mathlib `CategoryTheory/Monoidal/Category.lean:686-688` and `CoherenceLemmas.lean:31-38`, which explicitly state the same unitor identity with the associator orientation used here. There are no new nodes whose sources remain to be checked.

Step 1 uses the two definition statements for tensor bifunctoriality, functoriality and inverse-arrow conventions. The substantive action identity is a hypothesis of the item. I checked its substitution at `(L_f,L_g,P_gK)` and reversed all factors: the functorial factor at the right after inversion is `F_f(sigma_K)`, with `sigma_K` oriented from the nested source to `L tensor P_fP_gK`. The domain and codomain are written in the step. This is direct inversion, not an additional action-compatibility lemma.

Step 2 uses the monoidal definition's explicit naturality of structural isomorphisms to move `t_f` across the associator. The separate citation to `lem-coef-monoidal-structural-coherence` compares exactly two structural paths from `(1 tensor B) tensor C` to `B tensor C`. I checked the same formal source and target, with no permutation or arbitrary generating arrow. After those two equalities, tensor bifunctoriality supplies the displayed contraction equality. This is the one non-elementary theorem invocation in the proof, and its node is cited.

Step 3 uses the monoidal definition's tensor preservation of componentwise composition, together with Steps 1 and 2 and the item's definition of `a`. I checked that `q_(f;L,C)` ends at `F_fL tensor C`, allowing `a tensor 1_C` to follow it. Nothing about a third functor, an adjunction or compatibility with a compositor is needed.

Step 4 has no external node citation: it multiplies the assumed naturality square of `PF_g` by its two component inverses. I checked the arrow is `a:F_fL -> L_g`, that the fixed argument is `K`, and that `P_gK=C`. It uses no associativity law for `g`. This is a two-line consequence of the given natural isomorphism, so it is an elementary step rather than a new lemma node.

Step 5 uses the monoidal and functor definitions for preservation of composition, applies Steps 3 and 4, and substitutes the item's definition `b=t_g F_g(a)`. I checked the source is exactly the source in the assertion and the codomain is `K`. All intermediate objects and arrows lie in the hypothesis's closed domains; in particular `a tensor 1_(P_gK)` is permitted because its objects are displayed and the domains are full and tensor-closed as stipulated. No symmetry, left-exactness, zero object or additive structure enters the proof. The off-unit definitions are declared as generic tools; the coherence node already is a Mathlib leaf.

For B1-B10 I checked that there are no new statement-only nodes or unsearched candidates to audit, the item remains self-contained, TeX has single decoded backslashes, and the Mathlib structural hit is identified at the lines actually read. For C1-C8 I checked every used node's actual statement, quoted it verbatim in `citations.json`, retained exactly the union of step uses in `proof_deps`, and avoided the circular parent citation. For D1-D5 the steps themselves carry the calculation, including the inversion and naturality squares; no new node merely renames a clause. For E1-E7 I checked all types and the closed-domain assumption, and found no false statement requiring correction.

As small-case checks, I specialized to strict monoidal identity functors and identity projection comparisons: both sides are successive application of the two given functionals. In vector spaces with one-dimensional coefficients and arbitrary scalar functionals, both sides multiply by the same product; a zero functional gives zero on both sides. I also checked the second projection comparison may be rescaled by any nonzero scalar: its inverse contributes the same inverse scalar to both sides, so no unassumed normalization or action law for `g` has entered the proof. Taking the coefficient objects or `K` to be the tensor unit preserves all arrow types and uses the same explicit unitor equality. The calculation never interchanges factors, so it applies without a braiding. I found no statement dispute and made no statement change.
