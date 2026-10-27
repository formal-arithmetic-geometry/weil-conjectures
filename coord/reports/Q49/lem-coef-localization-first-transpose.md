# Worker report: lem-coef-localization-first-transpose

## Files written

- `dag/nodes/sec-six-functors/lem-coef-localization-first-transpose.json`: statement item, split in three steps; not a Mathlib leaf as a whole. Statement and original provenance retained.
- `citations.json`: one verbatim statement quote for every step citation.
- No new nodes and no new Mathlib leaves. `searches.jsonl` retains the five searches actually run for this item, in addition to the inherited searches retained in the node.

## Attachments

None. Searches of `lean/WeilConjectures/` for the exact blueprint tag, localization transpose, counit normalization and related triangle declarations found no declaration stating the whole item. Mathlib results cover separate ingredients and do not constitute project attachments.

## WANTED

None. The needed sources are present locally.

## Findings and corrections

The item was unsplit. Its statement needs no correction: the assumed compatibility of the third isomorphism with the second arrow is exactly what rotated TR3 requires. The proof does not assume uniqueness of arbitrary TR3 completions. It proves uniqueness of the first component using fullness and the adjunction bijection. No assumption that the counit is a monomorphism is used. The full-faithfulness hypothesis on I_B supplies fullness on Hom sets; its faithfulness is stronger than this argument needs. Neither exactness nor full faithfulness of I_A is silently assumed.

The ancestor is `lem-coef-finite-closed-shriek`, proof paragraph 2. This split supplies its previously unexpanded claim that the first localization component is the image of the specified exceptional adjunct. No chapter or unit route changes. The item is not the unit key node, so no unit realization file is written.

## Not duplicates

No new nodes. The existing `lem-sf-triangle-morphism-iso` supplies the exact pre-triangulated two-out-of-three theorem; the existing `lem-weil-pbc-adjunct-counit-identity` supplies the exact adjunct equation. `lem-weil-pbc-triangle-morphism-extension` is unnecessary: its additional uniqueness hypothesis is not assumed here. The blueprint search for triangle morphism and counit normalization gave no node stating this entire abstract assertion.

## Review by Q49

I read the ancestor's blueprint proof paragraph 2 and the item's complete statement, the six-functors chapter record, and the biduality unit record. For the abstract ingredients I read Stacks derived.tex Tag 0145 (definition-triangulated-category, including the signed rotation and TR3) and Tag 014A (lemma-third-isomorphism-triangle), and categories.tex Tag 0037 (definition-adjoint and its following explicit transpose formulas). No prohibited source is used. There are no new nodes whose sources need separate checking.

For step 1 I opened `def-weil-triangulated-category` and checked that its statement actually includes exact functors preserving distinguished triangles, rotation with minus the shifted first map, and TR3. The square (1,d) commutes by the hypothesis d S_X(eta_A)=eta_B. TR3 on the rotated triangles produces h on the shifted first objects. The shift autoequivalence is full and faithful; lifting h and cancelling the two minus signs gives epsilon_B a=S_X(epsilon_A). Its other square gives the original connecting square. Thus every triangle-morphism square is accounted for, including the source functor's specified shift comparison. This is a direct use of the axioms, not a new completion lemma hidden in the proof.

For step 2 I opened `lem-sf-triangle-morphism-iso`; its statement permits pre-triangulated categories and any two invertible components. Both triangles in step 1 are distinguished, the middle map is identity, and d is invertible. I also read Mathlib CategoryTheory/Triangulated/Pretriangulated.lean:526, isIso₁_of_isIso₂₃, confirming exactly this specialization. I reused that existing leaf instead of creating a duplicate or merely citing a tag.

For step 3 I opened `lem-weil-pbc-adjunct-counit-identity` and checked its equivalence epsilon L(f)=phi iff f=R(phi) unit. The domain is P=S_Z J_A M and the target object is V=S_X M, so Q=J_B V. A candidate t composed with c inverse has source I_B P and target I_B Q; fullness therefore supplies f:P to Q. Its counit equation is exactly phi. The cited equivalence forces f to equal b, and cancellation of c proves t=I_B(b)c. This is a short calculation from the cited statement and the explicit hypothesis that I_B gives Hom-set bijections, hence is marked elementary. It does not promote a clause of the item into a new node.

I checked edge cases M=0, identity coefficient functors with c=identity, and the identity adjunction (where the counit equation forces a=identity). The argument uses no nonzero-object or boundedness hypothesis. An arbitrary triangle completion can fail uniqueness without the fully faithful adjunction, which is why the Hom lifting and transpose calculation are retained. All three proof steps are below 2000 characters. B–E checks: statements and provenance retained; every non-elementary ingredient is in an opened node statement; the cited sources have the correct tags; the proof makes the rotation signs and transpose equation explicit; no new-node duplication, relabelled clause, unproved naturality claim or cycle is introduced. Citations are verbatim extracts rather than paraphrases.

## Unfinished work

None in the requested one-level split. Stage 2 and Lean compilation are outside this task.
