Files written:

- `dag/nodes/sec-picard-framework/lem-sc-p1-rhom-hom-derived-connecting.json`: statement, no new node, split proof.
- `citations.json`: verbatim citations for every proof-step dependency.

Attachments: none.

WANTED: none.

The item was unsplit with an empty proof. I checked the target statement against the Serre-duality blueprint step and the cited Derived Categories tags 05TE, 05RS, 06XR, and 070I. No exact sorry-free project declaration carries the blueprint tag or the full statement, so this is a split rather than an attachment. Existing nodes already cover K-injective localization, the derived-functor bridge, and long exact sequences, so I created no duplicate child node.

## Review by M1

I read `lem-sc-p1-rhom-hom-derived-connecting.json`, the unit `sk-thm-picard-duality`, the chapter record, and the source material for Tags 05TE, 05RS, 06XR, and 070I. Step 1 uses the bridge definition to identify `Rv(X)` with the Hom complex, the abstract derived-category localization, and the K-injective localization bijection; these statements explicitly provide the cocycle/homotopy-class calculation. Step 2 uses the same K-injective statement and bridge clause that the resolution choice does not matter; the bounded-below hypotheses are those in the item. Step 3 uses the bridge and derived-category cone description, the existing long exact cohomology node, and the homological-functor long exact-triangle node; these give the cone boundary and identify the connecting map with postcomposition by `w[n]`. I verified that every cited node says the fact used in its step and recorded verbatim quotes in `citations.json`. I tested the formula in degree `n=0` (a map `M -> ker(d^0)` gives the corresponding derived morphism) and for the zero triangle (both connecting maps are zero). The only repair to the imported item was filling its empty proof and proof dependencies; its statement, hypotheses, source, and blueprint reference were unchanged.

## Second reading by M1

- Item statement: checked against Stacks Tags 05TE, 05RS, 06XR, and 070I and the `thm-sc-p1-duality` blueprint Step 2; verdict: hypotheses and connecting-map formula agree, including bounded-below objects.
- Step 1: checked the K-injective bridge, derived-category localization, and `lem-weil-pbc-kinjective-hom-derived`; verdict: the cocycle/chain-map and homotopy/localization argument is supplied by the cited statements.
- Step 2: checked the K-injective comparison statement and the bridge's resolution-independence clause; verdict: lift uniqueness up to homotopy supplies independence and naturality.
- Step 3: checked the cone description, derived cohomology long exact sequence, and homological-functor long exact sequence; verdict: the cone boundary and postcomposition by `w[n]` are the same representative, and the cited long-exact statements identify the connecting maps.
- New nodes: none; B1-B7 and duplicate/Mathlib-leaf checks are vacuous. Existing `lem-sc-p1-ext-resolution-derived-connecting` is only a short-exact-sequence specialization and depends on this item, so it cannot replace it.
- Edge cases: checked the zero triangle, degree `n=0`, and the zero object; all give the asserted zero or kernel-map formulas.

Changes: corrected stale `created.item` metadata and added this second-reading audit. No mathematical statement or proof step changed.
