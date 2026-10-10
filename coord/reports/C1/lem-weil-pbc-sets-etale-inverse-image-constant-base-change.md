Files written:

- `dag/nodes/sec-proper-base-change/lem-weil-pbc-sets-etale-inverse-image-constant-base-change.json`: split statement; no new nodes and no Mathlib leaf.
- `citations.json`: verbatim citations for both proof steps.

Attachments: none.

WANTED: none.

The item was unsplit and had no closed project declaration. The existing node `lem-sc-etale-fibre-product-base-change-coproduct` is only for finite families, while this item allows an arbitrary set, so it is not a duplicate. The inherited `created.item` metadata was corrected to this item. The proof follows the source's two relevant pieces: construct the canonical map by the fibre-product universal property, then apply the gluing description of coproduct schemes after base change to obtain an inverse.

Nothing remains unfinished.

## Review by C1

I read the item and its blueprint ancestor `lemma-weil-pbc-proper-underived-exchange`, including the paragraph describing pullback of the coproduct representing a constant sheaf. I also read the source for the existing coproduct-family node, which is based on Schemes Tags 01JB and 01JC. Step 1 uses exactly that node's universal property for the coproduct and its open-and-closed summands, together with the fibre-product notion in `def-pc-fibre-product`; the construction is elementary once those statements are in place. Step 2 uses the same coproduct statement for disjointness and covering, and the Stacks gluing argument that these properties survive base change; this is the only non-elementary step. The statement's hypotheses introduce both schemes, the morphism, the set, and both coproducts, and the conclusion records the canonical map and its compatibility with every coprojection. I checked the empty-index case (both coproducts are empty and the comparison is the unique isomorphism) and the singleton case (the comparison is the canonical identification $V\\times_UU\\cong V$). Mathlib searches were rerun for LeanFinder, Loogle, grep, and LeanSearch; LeanSearch was unavailable, while the other searches found only finite or binary coproduct declarations and no arbitrary-index base-change theorem. No new node was needed, and the finite-family node was explicitly ruled out as a duplicate because of its finiteness hypothesis.
## Second reading by C1

I checked the item statement against the arbitrary-index coproduct construction (Stacks Tags 01JB and 01JC) and the fibre-product universal property, including empty and singleton index sets; the statement is correct. Step 1 was checked against the universal-property clauses of `lem-weil-pbc-scheme-coproduct-family` and `def-pc-fibre-product`; its construction is elementary. Step 2 was checked against the clopen disjoint-cover clause of `lem-weil-pbc-scheme-coproduct-family` and the base-change open-subscheme statement of `lem-weil-pbc-open-fibre-product`; the pointwise covering and inverse gluing are now explicit. The existing finite-family node was rechecked and is not a duplicate because this item allows arbitrary sets.

Changed step 2 to cite `lem-weil-pbc-open-fibre-product`, added its verbatim citation, and wrote out why the base-changed pieces are disjoint, covering, and glue to an inverse.
