Files written:

- `dag/nodes/sec-picard-framework/lem-pc-closed-subscheme-base-change-ideal-image.json`: item, split with no new nodes; Mathlib searches found no exact image-form declaration.

Attachments:

- None. No sorry-free project declaration carries the item under its exact tag.

WANTED:

- None.

What was checked and corrected:

- The existing DAG node `lem-pc-closed-imm-base-change` was searched by its statement and Stacks tag. It is strictly more general: it treats an arbitrary closed immersion and arbitrary morphism and states that the base-changed ideal sheaf is the image of the pulled-back ideal map. Therefore this item is a direct specialization; creating a second affine or image lemma would duplicate that node.
- The item statement was left unchanged. Its proof is one specialization step, with `lem-pc-closed-imm-base-change` as its only dependency. The statement of that cited node was opened and checked to contain both the closed-immersion conclusion and the ideal-sheaf image formula used by the step.
- The source read was Stacks Project, Schemes, Lemma 01JU (lemma-fibre-product-immersion), part (1), which is the source recorded on the item. The existing node's corrected proof handles the affine calculation and does not assume flatness for the image statement.
- Mathlib searches were run with LeanFinder, Loogle, and Mathlib grep in two phrasings. They returned `IdealSheafData.comap` and `ker_fst_of_isClosedImmersion`, which express the kernel/comap construction, but no exact sheaf-image statement; hence the item is not marked a Mathlib leaf.
- Small-case sanity check: for an affine closed immersion `Spec(A/I) -> Spec(A)` and `Spec(B) -> Spec(A)`, the base change has ideal `IB`, exactly the image of `I ⊗_A B -> B`, matching the cited general node.

## Review by C1

I read the item source (Schemes, Lemma 01JU (1)) and the full statement and proof of `lem-pc-closed-imm-base-change`. The cited statement explicitly supplies the projection's closed-immersion property and the image formula, so the sole proof step is a genuine specialization and does not use any unstated hypothesis. I checked the variables map as `X := S`, `Z := Z`, and `X' := Y`, with `g : Y -> S`; the displayed composite is the same map after this substitution. I also checked the existing DAG for duplicate image/base-change nodes and found the cited general node, so no new node was created. The blueprint reference was updated with `same_as` pointing to that general blueprint node, and the cross-unit citation is declared as a tool use because this item is in the Hilbert-curves unit while the general theorem is in the Picard-RR unit.

What I could not finish:

- Nothing; the split is complete and ready for dry run.

## Second reading by C1

- Item statement: checked against Schemes Lemma 01JU (lemma-fibre-product-immersion), part (1), including the arbitrary morphism hypothesis and image, rather than pullback-equality, conclusion; verdict: correct.
- Proof step 1: checked the specialization `X := S`, `X' := Y`, `Z := Z`, and `g : Y -> S` against the full statement of `lem-pc-closed-imm-base-change`; both the closed-immersion and ideal-image clauses are supplied; verdict: correct and non-elementary.
- Existing cited node: checked its corrected image-form statement, its definition dependencies, and its affine counterexample to the stronger nonflat equality; verdict: valid dependency.
- Duplicate and Mathlib checks: searched the DAG and recorded LeanFinder, Loogle, and grep results; the item duplicates the existing general node and is not an exact Mathlib declaration; verdict: no new node needed.
- Edge cases: checked the affine case `Spec(A/I)` over `Spec(A)` after base change to `Spec(B)`, the identity map, a field base change, and the zero ideal; all give the stated image ideal; verdict: consistent.
- Delivery metadata: removed the worker-authored cross-unit `tool_uses` entry because that bookkeeping belongs to the maintainer; retained the valid blueprint `same_as` duplicate reference.
