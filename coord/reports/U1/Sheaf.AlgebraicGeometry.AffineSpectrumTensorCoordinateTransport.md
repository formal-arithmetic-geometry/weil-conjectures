## What changed

Replaced the proof of `AlgebraicGeometry.SingleComplexBaseChange.exists_affineSpectrum_tensor_coordinates`
with the planned assembly from `exists_affineSpectrum_tensor_coordinate_data` and
`affineSpectrum_tensor_coordinate_homology_transport`. The existing ordinary stalk homology
isomorphism definition and the two intermediate declarations are unchanged.

## Proved and sorry left

The target `exists_affineSpectrum_tensor_coordinates` is proved by extracting the coordinate
data and applying the homology transport theorem. The pointwise helper `affineSpectrum_tensor_coordinate_homology_transport_pointwise` remains sorry (node
`lem-pc-affine-spectrum-tensor-coordinate-homology-pointwise`). The two imported intermediate declarations
remain sorry: `exists_affineSpectrum_tensor_coordinate_data` (node
`lem-pc-affine-spectrum-tensor-coordinate-data`) and
`affineSpectrum_tensor_coordinate_homology_transport` (node
`lem-pc-affine-spectrum-tensor-coordinate-homology`). No new sorry was added.

## No longer needed

None. The data and homology declarations are both used by the proof, and the imports
`IsoPullbackStalkCohomology`, `TensorPullbackCompositionIso`, and
`AffineSpectrumTensorCoordinateData` remain needed by the module declarations.

## Where the brief, the DAG or earlier work was wrong

The earlier attempt stopped after searching for a direct construction. The DAG already splits
the construction into the two imported declarations, so the parent theorem can be closed by
assembling those declarations even while their proofs remain open.

## New nodes

`lem-pc-affine-spectrum-tensor-coordinate-homology-pointwise` records the pointwise homology equation used to close the morphism equality.

## Earlier second reading (a previous round; superseded)

Pending independent reading of the pointwise decomposition and its node.

## Second reading by U1

1. Compared the delivered module with the repository version. Existing declaration
signatures and definitions are unchanged; the only additions are the named pointwise
helper and the proofs of the homology transport and assembly theorems.

2. Compiled all sandbox modules with `lcompile.py`. The file compiles cleanly. The only
remaining `sorry` is the explicitly named pointwise helper; no forbidden declarations or
hollow definitions occur. The proved declarations use only the allowed imported theorem
axioms (the helper remains open as documented).

3. Checked the new pointwise statement and node. It is the elementwise form of the
homology morphism equality, is strictly simpler than the parent equality, has a source,
natural-language proof plan, and is needed by extensionality. It does not duplicate the
parent target. The node's Lean declaration and statement match the module.

4. Checked pruning and imports. Both coordinate-data and homology transport declarations
are used by the assembly proof; the public imports support declarations in this module,
and the data module is proof-only. No proof dependency can be removed, and the unit route
is preserved through the two planned sublemmas.

5. Checked DAG agreement. The parent node records both sublemma dependencies and the new
pointwise node records its homology dependency. The unit and chapter metadata are
unchanged, and the pointwise node is marked split with the required source and proof
fields.

Changed: added this second-reading record; no code or DAG repairs were needed.
