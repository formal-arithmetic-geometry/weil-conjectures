## What changed

Proved `AlgebraicGeometry.finite_etale_etale_local_split` in
`Sheaf.Paper.FiniteEtaleEtaleLocalSplit`, without changing its signature or public imports.
Added proof imports `Mathlib.AlgebraicGeometry.Morphisms.FlatMono` and
`Mathlib.AlgebraicGeometry.Limits`. The original finite-unramified decomposition supplies
closed-immersion components. Mathlib proves that their maps to the base are open immersions.
Four proved private helpers handle coproduct point coverage, uniqueness of the component
index, a uniform clopen neighbourhood, and restriction of the coproduct to that neighbourhood.
The final proof transports the restricted cofan along `pullbackLeftPullbackSndIso`.
Updated the item's node proof and proof dependencies to match this construction.

Searches: LeanFinder for finite étale local splitting found only general étale/algebra
results; Loogle found `IsOpenImmersion.of_flat_of_mono`; the scripted grep search found
`nonempty_isColimit_cofanMk_of`. Direct searches of both library roots found no theorem
already proving the target. Read the Mathlib pullback ranges, coproducts, flat monomorphism,
étale and formally-unramified implementations. No relevant open change record was found.
The local Stacks TeX is absent on this machine, so checked the primary-source pages
[Stacks 04HN](https://stacks.math.columbia.edu/tag/04HN) and
[Stacks 04HJ](https://stacks.math.columbia.edu/tag/04HJ): 04HN uses 04HJ followed by open
immersions and shrinking, exactly the route retained here.

## Proved and sorry left

Proved the item's sole original sorry:
`AlgebraicGeometry.finite_etale_etale_local_split`
(node `lem-weil-pbc-finite-etale-etale-local-split`).
No sorry remains in this delivery; none was split off. All four private helpers are proved.
The proof uses the existing declaration
`AlgebraicGeometry.exists_etale_closed_immersion_decomposition_of_finite_unramified`
(node `lem-weil-pbc-finite-unramified-etale-local`, module
`Sheaf.AlgebraicGeometry.FiniteUnramifiedEtaleLocal`), which still has its existing sorry.
Thus this closes the target declaration relative to that planned dependency, rather than
claiming the target's entire axiom closure is sorry-free.

The Lean proof allows an empty initial index and an empty surviving index, as required.
The intersection over an empty index is the whole neighbourhood. Components missing the
chosen point are excluded by intersecting their complements; overlapping component images
in the base are allowed. Disjointness is required only in the original coproduct scheme.
Local and server compilation succeed without warnings. The delivery dry run passes all
checks except the intentionally pending second reading, and prints OK; nothing was pushed.
The declaration-table comparison confirms the original statement is unchanged and its
sole original sorry is removed. All Lean lines meet the 100-character limit.

## No longer needed

No existing Lean import was removed. The separate node
`lem-weil-pbc-open-fibre-product` is no longer a direct proof dependency: the proof uses
canonical iterated pullbacks and their pasting isomorphism instead of identifying an open
preimage via that node. Its Mathlib source module remains a public statement import.
No other original node is pruned. Added existing Mathlib leaves
`lem-weil-pbc-scheme-coproduct-family` and
`lem-weil-pbc-closed-immersion-base-change` to record the coproduct and base-change facts.
No new module is needed for any of the shrinking steps.

## Where the brief, the DAG or earlier work was wrong

No incorrect statement was found. The plan's shrinking must remove the images of components
not passing through the distinguished point, as its expanded steps already specify; the
Lean neighbourhood intersects each image or its complement according to that point.
The unit `sk-thm-p1` and its realized statements/steps are untouched. The item is below those
unit realizations, and still follows the 04HJ → clopen images → shrinking → coproduct route.
The remaining coproduct and shrinking glue is supplied completely by proved helpers,
without additional statement modules or new nodes.

## Second reading by S2

1. Compared the delivered Lean module with the repository version. The target theorem
signature and all existing declaration signatures are byte for byte unchanged; only the
proof and proof-only imports changed. Verdict: pass.
2. Compiled the module with `lcompile.py`; it succeeds without warnings. There are no
`sorry`s, `axiom`, `unsafe`, `opaque`, `extern`, or `implemented_by` declarations in the
delivery. The target's dependency `exists_etale_closed_immersion_decomposition_of_finite_unramified`
remains the planned open theorem, so its `sorryAx` is outside this module. Verdict: pass.
3. No statements were split off and no new nodes were added. The private helpers are
strictly intermediate reductions, not restatements of the target. Empty index and empty
surviving-index cases are permitted, and the clopen shrinking argument is valid. Searches
reported above found no existing theorem duplicating the result. Verdict: pass.
4. Read the proof downward from the target. It uses the finite-unramified decomposition,
Mathlib's flat-mono open immersion result, finite clopen shrinking, coproduct coverage and
pullback pasting. Proof-only imports are plain imports. The old open-fibre-product node is
pruned from direct proof dependencies; no other old dependency is removed, and the unit
`sk-thm-p1` route remains intact. Verdict: pass.
5. Compared the delivered node with the Lean proof: its proof steps, proof dependencies,
proof origin and chapter/unit metadata agree with the implementation. The old shrinking
and open-fibre-product route is replaced by the explicit pullback-range and coproduct
construction recorded in the node. Verdict: pass.

Changed: corrected the target docstring's step 4 to describe the implemented pullback-range
and pasting route rather than claiming use of the pruned open-fibre-product lemma. The
mathematical proof is unchanged. Added this second-reading record.

A scratch-copy `#print axioms` confirms exactly `propext`, `Classical.choice`, `Quot.sound`
and `sorryAx`; the latter is inherited from the disclosed finite-unramified dependency.
Read the unit's realized statement and every realized step: neither this item nor the
pruned dependency realizes a unit-level step.
