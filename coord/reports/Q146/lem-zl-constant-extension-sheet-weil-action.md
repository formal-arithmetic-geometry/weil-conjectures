## Files written

- `dag/nodes/sec-deligne-laumon-general/lem-zl-constant-extension-sheet-weil-action.json`: item, statement, split into six proof steps; no Mathlib match.
- `citations.json`: fourteen verbatim statement quotations, one for each step/cited-node pair.
- `searches.jsonl`: six searches actually run by the prescribed msearch command, with their recorded results.

No new nodes; zero new Mathlib leaves. The sandbox initially contained only dispatch markers, with no split, report, saved delivery result or running delivery process to resume.

## Attachments

None. Searches for the exact blueprint tag and for constant-extension/sheet/Frobenius/direct-image notions found no declaration under `lean/WeilConjectures/` stating all clauses. The inspected `WeilSheaf/LowerStar.lean` implements transported direct images but does not state their clopen component formula. General operation declarations and results in a different model of Weil categories are not attachments of this item.

## WANTED

None. The current blueprint source and all auxiliary DAG statements needed for this split are present.

## Corrections and scope

The statement is unchanged. The live item had an empty proof. I expanded paragraph 5 of the current `thm-zl-real-mixed-by-curves.proof.md`, specifically the sentence about permuting copies and commuting with Frobenius. I read the chapter and unit records and kept the finite constant-extension/diagonal-unit route. This item is not the unit's key theorem, so no unit record is edited.

The potentially dangerous point is permutation direction. With geometric Frobenius defined by the inverse arithmetic field automorphism on the final scalar factor, the sheet map is `pi(sigma) = arithmetic_Frobenius composed with sigma`. Its pullback at the sigma sheet reads the pi(sigma) component. I checked this on affine ring tensors explicitly. I did not replace pi by its inverse in the final action.

No clause has been offloaded to a new lemma. In particular the adjunction-mate component computation stays in Step 3, where it is three operations: diagonal unit, pullback-composition identification, and the pulled-back counit projection. Each non-elementary input is an already existing statement. All proof steps are below 2000 characters.

## Not duplicates

No new nodes are proposed. Whole-DAG searches for clopen/reindexing/Frobenius-exchange notions and whole-blueprint searches for `Frobenius sheet`, `constant extension`, `clopen`, and `exchange` found the existing tools used below, rather than another node stating this entire item. The same-unit constant-extension Weil-heart equivalence is used only for its explicitly stated geometric-sheet decomposition, not as a substitute for the desired direct-image formula. The same-unit split-sheet adjunction states the actual product adjunction and unit/counit, so it is cited rather than restated in a new node.

## Mathlib search reading

All six new searches are preserved in `searches.jsonl`. The exact Weil-sheaf query returned Witt-vector isocrystals and finite-field Frobenius maps, which do not supply constructible Weil direct-image comparisons. Loogle's `"Weil"` returned Weil divisors. The first grep returned no matches. A second semantic formulation in terms of diagonal/product adjunctions returned product/closed-monoidal mate facts. LeanSearch returned `CategoryTheory.Limits.Pi.reindex`, `Sigma.reindex` and module base-change facts. I read the local `Products.lean` reindex definitions/projection identities and `Monoidal/Closed/Functor.lean` mate formula located by the second prescribed grep. These describe abstract product reindexing or the monoidal Frobenius morphism; they do not state the canonical geometric exchange, its Weil action, and the coefficient-stage normalization of this item. All services answered successfully. Earlier search records already in the live item are retained with their original queries and results.

## Review by Q146

I read `coord/delivery-errors.md` B–E in full against the six steps, the current blueprint paragraph 5, and the actual statements of every cited DAG node. For the item source, the phrase “commute with Frobenius” is the conclusion to justify, not an external lemma. There are no new-node sources to audit. I also read the original blueprint presentation of `lem-fix-weil-operations` to identify the intended construction, but the proof does not cite its proof as a theorem: the explicit lifting equation is taken from the statement of `lem-pod-semilinear-field-operation-lifts` instead.

Step 1 uses clause (b) of `lem-zl-constant-extension-weil-heart-equivalence` only for the geometric disjoint sheets. That clause states a disjoint union of m sheets isomorphic to X with the cyclic geometric action; it has precisely the same finite fields, extension, separated finite-type model and constructible coefficient conventions. `def-weil-frobenius-detailed` supplies gamma inverse to arithmetic Frobenius and the ring-coordinate map on the last scalar factor. The written tensor equation then proves the direction of pi, rather than assuming a sign convention from the cyclic-action sentence. The labels are field embeddings, so pi is specified even if X is empty; this does not require distinguishing empty subsets by their images.

Step 2 uses the full derived statement of `lem-zl-split-sheet-adjunction`, including its specified Hom bijection, diagonal unit, projection counit, heart biproduct, and coefficient compatibility. It applies because the given finite nonempty family of projection sections satisfies h s_sigma = id. The exact Frobenius equivalence used to commute P_X with products is explicitly in the statement of `lem-pod-semilinear-field-operation-lifts`; the universal property proves preservation in one line. No exactness, constructibility, or derived-product comparison is inferred from a definition alone.

Step 3 uses the displayed unit–square–counit definition in `def-exchange-projection`, with `fix-lem-exchanges` supplying its identification with the actual exchanges at the completed/rational/common stages. The latter's square hypotheses are addressed explicitly: the Frobenius maps are scheme automorphisms, and the source k-structures are twisted so that all square arrows are k-morphisms. These schemes remain finite type. The same-unit adjunction statement gives exactly the counit projections and the componentwise transpose, so computing the transpose at sigma proves the desired projection equation. This uses statements, not the proof of a definition or a stalk formula. It requires no general base-change invertibility theorem: the displayed permutation inverse verifies invertibility in these coordinates.

Step 4 uses the actual rule `(K,theta) -> (FK,F(theta) a_K)` in the statement of `lem-pod-semilinear-field-operation-lifts`, for both pullback and direct image. Its coefficient category is the rational/common-stage pair category required by the item, not the derived category of Weil sheaves used by some upstream declarations. The prior component equation and the naturality of the split-sheet adjunction give each output component as theta composed with the pi(sigma) projection. Because equality is proved by the product universal property in the derived category, it is equality of morphisms, not just equality of their stalks.

Step 5 reads the coefficient-compatibility assertions in `lem-zl-split-sheet-adjunction`, `lem-pur-finite-clopen-derived-decomposition`, and clause (1) of `fix-lem-exchanges`. The clopen theorem includes the actual module/derived equivalences at integral, rational, and common stages and their coefficient comparisons. Here all operations are finite products or automorphism transports; these preserve the necessary bounds and the heart. Thus no general all-morphisms constructibility assertion, arbitrary higher-coefficient base-change theorem, or reduction of rational coefficients is used. A rational Weil isomorphism is handled as a morphism at a common finite coefficient field, without assuming a stable integral lattice.

Step 6 uses the diagonal-unit clause of `lem-zl-split-sheet-adjunction` and the exact morphism equation in `def-weil-weil-sheaf-complex`. Composing with each projection gives theta on both sides, proving equivariance directly. I checked m=1 (identity permutation), M=0, and X empty (the unique morphism in the zero category), and used no lissity, geometric connectedness, or semisimplicity. A nontrivial cycle of length three also confirms that the exchange reads the next component rather than the previous one; cycles of length two would not detect that mistake.

For B, there are no new unsplit statements, duplicated tags, or proposed Mathlib leaves; original metadata and statement notions are retained. For C, all fourteen step/node pairs have quotations from statements, with the portions supporting the actual use included. I checked that the potentially broader tools used in the proof do not depend on this item. For D, the central exchange and action computations are written out; no new node restates a clause and no circular invocation appears. For E, the field, scheme, coefficient, adjunction and square hypotheses above are in force and the small cases pass. No statement dispute or source error was found.

The two generic off-unit tools are declared in `split_report.tool_uses`: `lem-pod-semilinear-field-operation-lifts` gives the explicit operation-lifting formula absent from the statement of the item's existing Weil-operations citation; `lem-pur-finite-clopen-derived-decomposition` gives the coefficient-compatible derived clopen equivalence. They support the prescribed route and do not change the mixedness argument. I do not set the maintainer-owned `tool_uses` field.

## Unfinished work

None in the mathematical split. Required server validation and delivery follow this review.
