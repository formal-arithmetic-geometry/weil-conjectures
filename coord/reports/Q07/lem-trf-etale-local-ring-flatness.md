# Worker report

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-etale-local-ring-flatness.json`: item, split, statement unchanged; no exact Mathlib match. Four proof steps, no new nodes, no new Mathlib leaves.
- `citations.json`: one entry for every step/node citation, quoting the cited statement verbatim.

The sandbox also retains the genuine Mathlib search log and preparation scripts. The two provisional helper-node files were removed: the final proof needs neither of them.

## Attachments

None. Searches in the project's `WeilConjectures/` source for the blueprint tag, item id and the etale/stalk/module-flatness notions found no project declaration proving the entire item without sorry. The existing general relative-flat-extension node is reused as a dependency, not claimed as an attachment for this item.

## WANTED

None.

## What was checked and changed

I read Stacks `literature/stacks-project/flat.tex`, Tags 05BA and 05B9. The item is exactly the local-ring equivalence of 05BA: an etale morphism, a point and its image, an arbitrary module over the source stalk, and restriction along the specified stalk map. No statement repair is needed. The imported proof was empty.

The final proof uses the open-diagonal/base-change argument of 05B9 directly at stalks. An existing node, `lem-pc-pullback-stalk-relative-flat-extension`, already gives base change for arbitrary modules over stalks, so the auxiliary quasi-coherent sheaf construction of the printed 05BA proof can be omitted. This is the same diagonal argument underlying that proof, with no change to the unit's etale-neighbourhood route. I declared this off-unit generic tool in `split_report.tool_uses`. Its statement is stronger than the instance needed here, with no sheaf or finiteness hypotheses. Traversing its statement and proof dependencies does not reach this item, so its use is noncircular.

I searched the DAG and blueprint for the source tags and the notions before proposing helpers, and then read the relevant existing fibre-product, open-immersion, stalk, relative-flat-extension and flatness-transitivity nodes. Both provisional helpers were unnecessary: the final split cites existing nodes throughout and introduces no node restating or generalizing the item. The original blueprint ancestry and statement dependencies are retained.

The recorded Mathlib searches include two semantic phrasings and Loogle/grep/LeanSearch. The most relevant algebraic candidate is `Algebra.FormallyUnramified.flat_of_restrictScalars`, in `Mathlib/RingTheory/Unramified/Finite.lean:275`; I read the declaration and its surrounding assumptions. It requires a formally unramified essentially finite type algebra, and only supplies the upward implication. The scheme-stalk comparison needed to instantiate those assumptions and the reverse implication are additional results, so the item is not its one-line specialization. Scheme `Flat`/stalk-map APIs describe flatness of the ring map, not this equivalence for every module. The genuine search records, including exploration for the removed helpers, remain in `searches.jsonl`; the item's inherited search record is preserved.

An earlier draft incorrectly applied the sheaf-level comparison to the local-spectrum source instead of using the identity source map on an affine neighbourhood. The final direct stalk proof eliminates that construction entirely. It also eliminates the proposed 05B9 helper, whose statement would have deferred essentially the same comparison rather than exposing its argument.

## What could not be finished

Nothing remains for this stage-1 item. No Lean was written and no compiler, Lake, build, local DAG checker or local preflight was run.

## Not duplicates

No new nodes remain in the delivery. The existing relative-flat-extension lemma and transitivity lemma are cited directly.

## Review by Q07

I compared every hypothesis and both conclusions against Tags 05BA and 05B9 in `flat.tex`. I also read the full statements of every node cited by every step. The item is faithful to 05BA, and the proof exposes both non-elementary inputs instead of citing the source as a black box.

Step 1 uses `def-pc-fibre-product` for the projections and the diagonal equations. `def-weil-etale-morphism` explicitly includes unramifiedness; `def-weil-unramified-morphism` explicitly says its diagonal is an open immersion. `def-weil-open-immersion` identifies the structure sheaf with its restriction to the open image, so the induced map on germs is an isomorphism. `def-weil-locally-ringed-space-morphism` supplies composition of the structure maps. Applying that composition to each projection composed with the diagonal gives d a_i = id; inverting d gives both a_i = d^{-1}. No separatedness, affine chart, residue-field identification, or equality of off-diagonal points is being assumed. These are direct uses of definitions and inverse identities, not uncited geometric theorems.

Step 2 cites `lem-pc-pullback-stalk-relative-flat-extension`. Its statement says exactly that C tensor_A M is flat over the other base stalk, for an arbitrary A-module flat over the original base stalk. Here both scheme maps are e, and the fibre-product point is delta(t), so both projection points are t and the original base point is s. Thus every scheme, point, ring and scalar-action hypothesis matches. The node does not require quasi-coherence, finite generation, or flatness of a scheme morphism. I checked its dependency closure to exclude a circular use.

Step 3 explicitly constructs the two balanced maps, checks linearity for the second projection rather than just the first, and proves both inverse identities. In particular a_1 = a_2 is essential for the inverse to be A-linear, and is proved in Step 1. The cited `def-weil-pbc-flat-ring-map` gives injectivity after tensoring as the flatness criterion. Tensoring the displayed isomorphisms transports that criterion, so there is no hidden flatness descent assertion. This is an elementary tensor calculation, with all formulas written out.

Step 4 uses `def-weil-etale-morphism` for flatness of e, `def-weil-flat-morphism` for flatness of A over R at t, and `lem-pc-module-flat-transitive` for restriction of scalars of the flat A-module M. The transitivity statement explicitly has precisely those hypotheses and conclusion. The chosen scalar map remains e_t^sharp in both directions. Every dependency appears in `uses`, and every such citation has a verbatim statement quote in `citations.json`.

I tested the statement and construction with M = 0, e = id, M = A, and a nontrivial finite separable field extension. For e = id the tensor maps reduce to A tensor_A M = M. For a field extension, the product-stalk ring at the diagonal is the diagonal factor; the proof never identifies the entire tensor product with A. Arbitrary infinite modules are allowed by the cited relative-flat-extension statement and all the explicit formulas. With no point t there is no instance, as expected. No counterexample or missing hypothesis was found.

I reviewed delivery-errors B through E against the final files: the statement is unchanged, the split is an argument rather than an equivalent helper node, all non-elementary inputs are existing cited statements with matching hypotheses, there are no duplicate or elementary new nodes, and the scalar identifications are explicit. The four steps have 762, 576, 743 and 417 characters; none hides a lemma in a long step. No SGA source is used. This review is Q07's signature under the final split; the maintainer's independent review remains the delivery review.
