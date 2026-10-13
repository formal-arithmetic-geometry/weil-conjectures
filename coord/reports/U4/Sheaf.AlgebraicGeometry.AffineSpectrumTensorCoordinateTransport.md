## What changed
Repaired both transport helpers to accept canonical chain-level coherence and proved the pointwise homology equation from that coherence using naturality of exact restriction of scalars and stalk homology. Added `Sheaf.AlgebraicGeometry.AffineSpectrumTensorCoherentCoordinateData`, whose supplied coordinate theorem includes the coherence equation and is used by the final existence theorem.

## Proved and sorry left
Original hole removed: 1 of 1, `affineSpectrum_tensor_coordinate_homology_transport_pointwise`, by correcting its false universal statement and proving the corrected chain-coherence implication. This does not prove the old statement. Holes added: 1; split off: 1. This is a decomposition with net zero holes, not a completed geometric proof. The morphism helper was already proved and remains proved. The new supplied-data theorem `exists_affineSpectrum_tensor_coherent_coordinate_data` (node `lem-pc-affine-spectrum-tensor-coherent-coordinate-data`) remains a named sorry, with its construction and chain-coherence proof recorded in its docstring and node.

## No longer needed
The negation diagnostic and disputed markers were removed. Removed proof import `Sheaf.AlgebraicGeometry.AffineSpectrumTensorCoordinateData` and node `lem-pc-affine-spectrum-tensor-coordinate-data` from this route. The stronger coherent coordinate constructor replaces that insufficient data assertion. No unit route was bypassed. The pointwise node no longer uses `lem-pc-affine-spectrum-tensor-coordinate-homology` (the old circular plan); that node remains needed by the final assembly. The morphism node now uses only the pointwise node instead of its old direct proof dependencies `def-pc-scheme`, `def-pc-derived-category`, `def-pc-single-complex-base-change-stalk-condition`, `lem-pc-iso-pullback-stalk-cohomology`, and `def-pc-tensor-pullback-composition-iso`; these definitions remain available for its statement and the pointwise argument.

## Where the brief, the DAG or earlier work was wrong
The returned universal helpers were false because q and t could be simultaneously negated. The corrected supplied-data statement requires the canonical chain equality before homology. The pointwise proof now uses the chain-coherence-to-homology argument; the morphism theorem retains extensionality through the pointwise theorem.

## New nodes
`lem-pc-affine-spectrum-tensor-coherent-coordinate-data` records the supplied coordinate construction with canonical chain coherence; see `coord/changes/affine-spectrum-tensor-coordinate-coherence.md`.

## Forced adaptations
None.

## Statement corrected

Both universal helpers now use supplied coordinate data and require the canonical
chain equality before applying homology. The pointwise node's old existential
wording was replaced by the supplied-data statement. The fixed homology conclusion
is unchanged. This follows the pullback-stalk identification of Stacks Tag 0098,
with ordinary pullback composition from Tag 0096.

- `lem-pc-affine-spectrum-tensor-coordinate-homology-pointwise`: holds; the repaired constructor supplies chain coherence.
- `lem-pc-affine-spectrum-tensor-coordinate-transport`: holds; the repaired constructor supplies chain coherence.

The final `exists_affineSpectrum_tensor_coordinates` signature remains unchanged.
Its proof obtains coherent witnesses and passes the supplied chain equality to the
proved homology helper. The new constructor has no homology transport conclusion;
it is a strictly earlier geometric construction step. There is no sorry in a
definition and no arbitrary data chosen from an unproved existence theorem.

## Second reading by U4

1. Compared the complete module with the repository version and checked the declaration table. The signatures and bodies of `ordinaryIsoPullbackStalkHomologyIso` and the signature of `exists_affineSpectrum_tensor_coordinates` are unchanged. Only the two reported universal helpers acquire the chain-coherence hypothesis. These are corrections of false intermediate statements, covered by the change record, not proofs of their old statements. Searches of callers find no external invocation of either changed helper; `AffineSpectrumOrdinaryComparisonSquare` uses the unchanged final interface and unchanged homology definition. No target or existing definition changes.
2. Read both modules and the two private homology compatibility proofs. The transport module compiles locally without warnings (56.6 seconds after an initial timeout); the new constructor compiles in 12.2 seconds. The sole delivered sorry is the named `exists_affineSpectrum_tensor_coherent_coordinate_data`. No forbidden declarations, hollow definitions, or data selections from this open existence theorem occur: its witnesses are eliminated only in a theorem proof. The scratch `#print axioms` check passed: both ordinary comparison definitions and both transport helpers have exactly `propext`, `Classical.choice`, `Quot.sound`; the unchanged final existence theorem and the new open coordinate constructor additionally have `sorryAx`. The scratch compiled in 56.9 seconds; its only warnings were long appended print commands, outside delivered sources.
3. The new open theorem is a geometric chain-level construction, not the original homology conclusion under another name. Its proof in words constructs ring coordinates, the input-stalk comparison, and the balanced tensor map, then checks the pinned composition mate on pure germ tensors. Checked the actual pinned-unit specification of `exists_tensorPullbackAdjunction` and pinned-germ specification of `exists_tensorPullback_stalk_iso`: the construction does not assume arbitrary adjunction choices agree. Zero complexes, identity coordinate maps, and zero/empty stalk cases introduce no flatness or nonzero hypothesis. Independently searched with leanfinder for stalk tensor pullback composition, loogle for mapHomologicalComplexCompIso, grep for tensorStalkIso/stalkPullback, and rg across the library. Results provide component tools but no existing theorem with the affine coherent-coordinate conclusion. OpenOrdinaryTensorGermCoordinates is an open-inclusion construction, not an affine-spectrum isomorphism theorem. Closing this geometric construction is not a few-minute task. The source checks were [Stacks 0098](https://stacks.math.columbia.edu/tag/0098) and [Stacks 0096](https://stacks.math.columbia.edu/tag/0096).
4. Reviewed top-down: final existence obtains coherent coordinates, the morphism helper applies extensionality to the pointwise result, and the pointwise result uses exact-functor homology naturality. All public imports furnish symbols in public signatures or the unchanged public homology definition; the stronger coordinate module itself defines the chain comparison appearing in those signatures. The report lists the removed old dependencies, including the circular pointwise-to-morphism edge. The unit record `sk-thm-picard-semicon` is unchanged; its existing realized arrays are empty, so this delivery makes no claim to complete that bookkeeping. No unit-level step is bypassed.
5. Compared all four node records with the Lean and checked the new node's source, natural-language proof, searches, created/blueprint/chapter/unit and lean fields. The new node is the only new open theorem; the homology nodes describe supplied-data implications and the final node keeps its existential statement. The proof dependencies follow the homology reduction and coherent-data assembly. Statement-change records explain the negation obstruction. Verdict: acceptable as a documented statement repair and net-zero decomposition, conditional on the delivery preflight.

Second-reading repairs: clarified that the old false hole was corrected rather than proved; expanded Old/New signatures in the change record to verbatim source text; corrected the new node's proof-origin description; completed the dependency-pruning report. Added local irreducibility attributes for `ordinaryIsoPullbackStalkComplexIso` and `ordinaryIsoPullbackStalkHomologyIso` after the private unfolding proof to avoid repeated expansion of their comparison chains in the public transport arguments; their defining bodies and public signatures remain unchanged. No mathematical proof was rewritten.
