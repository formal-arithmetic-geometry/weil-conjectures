Files written:

- `dag/nodes/sec-picard-framework/lem-sc-affine-derived-cohomology.json`: item, split into two proof steps; no new nodes.
- `citations.json`: verbatim quotations for every cited node in each step.

Attachments: none. No sorry-free declaration in `WeilConjectures/` states this item exactly; the existing affine higher-direct-image declarations concern ordinary higher direct images only.

WANTED: none.

The imported item had an empty proof and an outdated `created.item` pointing to `lem-sc-affine-derived-pushforward-t-exact`; I retained the statement and corrected the proof metadata. The proof follows Stacks Tag 0AVW: the derived-direct-image definition identifies cohomology with higher direct images, and affine higher-direct-image vanishing plus quasi-coherence supplies the comparison and its target's quasi-coherence. No new node was introduced because a separate derived-comparison node would restate the item.

## Review by K1

I read the item against Stacks Project Tag 0AVW, lemma-affine-morphism-equivalence, and read the statements of both cited DAG nodes. Step 1 uses the exact definition sentence in `def-pc-derived-direct-image` identifying `H^i(Rf_*E)` with `R^i f_* E`, and the full affine statement in `lem-pc-affine-morphism-hi` that higher direct images vanish and ordinary pushforward is quasi-coherent. I checked that the affine hypothesis is the one needed by that node and that each `H^i(E)` is quasi-coherent because `E` lies in `D_QCoh(X)`. Step 2 uses the same quasi-coherence clause with `F = H^i(E)`. The termwise exact-functor calculation is the standard derived-functor argument recorded in Tag 0AVW; it is not hidden as a separate node or used to restate the item. I tested the statement on the identity morphism and on an affine morphism `Spec B -> Spec A`, where it reduces to the cohomology of restriction of scalars. The required Lean source grep found no exact declaration, and the recorded LeanFinder, Loogle, grep, and unavailable LeanSearch queries were run for this item.

## Second reading by K1

- Item statement: checked against Stacks Tag 0AVW, `lemma-affine-morphism-equivalence`, including its K-injective computation and affine higher-direct-image vanishing; the affine hypothesis, `E in D_QCoh(X)`, all integers `i`, comparison, and quasi-coherence conclusion agree. Tested `f = id`, the zero object, and `Spec B -> Spec A` (restriction of scalars).
- Step 1: checked `def-pc-derived-direct-image` (the quoted identification `H^i(Rf_*E)=R^i f_*E`) and `lem-pc-affine-morphism-hi` (vanishing of higher images and quasi-coherence) against the source proof's K-injective computation; the derived-functor calculation is the source's displayed argument and is not marked elementary.
- Step 2: checked `lem-pc-affine-morphism-hi` against its statement and applied it to the quasi-coherent sheaf `H^i(E)`, whose quasi-coherence follows from `D_QCoh(X)`; no unstated hypothesis is used.
- New nodes: none. The proposed comparison node would restate the item, so the proof keeps the comparison as Step 1 and cites only existing nodes. Existing-node search covered `def-pc-derived-direct-image`, `lem-pc-affine-morphism-hi`, and `lem-sc-affine-derived-pushforward-t-exact`.
- Lean search: the recorded LeanFinder, Loogle, grep, and unavailable LeanSearch entries were inspected; no exact Mathlib declaration was found, so there are no Mathlib leaves.
- Changes: no mathematical changes were needed. The worker's stale `created.item` value refers to the predecessor split, but this node already exists on the repository and delivery preserves maintainer metadata; the delivery preflight accepts it without creating a duplicate node.
