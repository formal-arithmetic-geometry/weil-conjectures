## What changed

The item theorem `AlgebraicGeometry.pushforward_support_closed_subset` now combines a
closed support interface with the existing closed-ambient-support vanishing lemma. Properness
makes the image of the supplied closed support closed, and the ambient-support lemma gives the
required containment. The new interface is stated in
`lean/Sheaf/AlgebraicGeometry/ProperPushforwardSupportClosed.lean` and imported by the item.

## Proved and sorry left

Closed the one original hole: `AlgebraicGeometry.pushforward_support_closed_subset`.
The closedness interface `AlgebraicGeometry.exists_pushforward_support_closed` is also proved.
Holes added: none. No `sorry` declarations remain in either delivered module; this is one original hole closed, with no unfinished statements split off.

## No longer needed

Removed from the item: proof-only imports
`Sheaf.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian`,
`Sheaf.AlgebraicGeometry.FiniteTypeModuleSupportClosed`, and
`WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.FiniteFreeComplex`.
Their results remain used inside the new closedness module, so none of these modules is globally
pruned. The item now uses `lem-weil-pbc-proper-pushforward-support-closed`,
`new-closed-support-pushforward-support`, and `def-weil-proper-morphism`.
The old direct dependencies `pqf-lem-coherent-ft-locnoeth`, `pqf-def-coherent`,
`lem-pc-coherent-hi`, `lem-pc-sections-higher-direct-image-quasi-coherent`, and
`lem-weil-pbc-finite-type-module-support-closed` are used through the closedness interface.
`lem-weil-pbc-sheaf-sections-determined-by-germs` and `def-weil-pbc-module-stalk` are used
through the existing closed-ambient-support lemma. No old dependency becomes globally unnecessary.

## Where the brief, the DAG or earlier work was wrong

The DAG's closedness step requires transporting coherence of the zeroth higher direct image
through `rightDerivedZeroIsoSelf`; this delivery implements that transport explicitly, including
the finite-presentation construction from coherent generators, and then proves the containment
and image argument completely.

## New nodes

`lem-weil-pbc-proper-pushforward-support-closed` records the closedness substep and its source;
its theorem is proved in the delivered module.

## Second reading by D3

1. Compared both delivered modules with the repository. The existing target signature is byte-for-byte unchanged; the added proper-support interface is recorded by its new node. Restored the original theorem docstring and removed three proof-only imports from the target module; the diff contains no accidental edits.
2. Compiled both modules with `lcompile.py --all`; both compile cleanly. The target has no `sorry`, and the new interface has no `sorry`, hollow definition, axiom, unsafe declaration, or other forbidden construct. Both public proofs use only the permitted foundational axioms (verified on scratch copies).
3. Checked the split-off theorem and node. `exists_pushforward_support_closed` is a strict closedness substatement of the item, has a source and complete proof docstring, and is not duplicated by the upstream/library search results. The item proof uses the existing closed-ambient-support theorem for containment.
4. The proof follows the unit route: proper pushforward closedness, then closed ambient support containment, then the image closedness argument. The removed imports were not used after the interface split; no additional pruning was found.
5. Checked the DAG records against the Lean declarations. The proper-support node names the new theorem and its actual dependencies; the item node names the target theorem and the proper-support and closed-ambient-support declarations used by the proof. The unit remains `sk-thm-p1`; its `realized` nodes are untouched. Expanded the new node’s dependencies to record the coherent-generator construction and quasi-coherence of higher direct images, and replaced its unverified search summaries by searches actually run with `msearch.py`.

Changed: removed the target's unused proof-only imports of coherent finite-type locality, finite-type support, and finite-free-complex modules, restored the target’s original docstring, corrected the new node’s dependencies and verbatim Lean statement, recorded fresh searches, and documented this second reading.
