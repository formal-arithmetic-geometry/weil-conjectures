# Delivery report

Item: `lem-weil-pbc-geometrically-regular-descent`

The target is split according to Algebra, Lemma Tag 07NH. For an arbitrary finite purely inseparable extension `k'/k`, the new public node `lem-weil-pbc-faithfully-flat-base-change` gives faithful flatness of `A tensor_k k' -> B tensor_k k'`. The definition of geometric regularity gives regularity of the target, and `lem-weil-pbc-regular-ring-faithfully-flat-descent` gives regularity of the source. Quantifying over all such extensions is precisely `def-weil-pbc-g-ring`.

The new child is statement-only and cites `def-weil-pbc-faithfully-flat-ring-map`; its source records Tags 00HI, 00FI, and 00HQ. The target proof cites Tags 07NH and 07NG through its source and cited nodes. No Lean declarations are added.

## Review by G1

I reviewed the split against the Stacks 07NH proof and checked the direction of every map. The base-change map is from `A tensor_k k'` to `B tensor_k k'`, exactly the tensor base change of the original faithfully flat map, and the new child records why flatness and spectrum surjectivity combine to faithful flatness. The target ring is regular by the stated geometric-regularity definition, so the existing 07NG descent node applies without an unmentioned Noetherian hypothesis. The final universal quantifier is the definition of geometric regularity, not a stronger finite-extension claim. The child is public, unsplit, statement-only, has all three required Mathlib searches, and its `created.item` matches this delivery. The item has one non-elementary step, a proof origin, a split report, and proof dependencies exactly equal to its cited uses.
