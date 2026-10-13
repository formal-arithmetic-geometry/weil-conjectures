## What changed

Split the affine coordinate transport proof into two named intermediate theorems. The new
`AffineSpectrumTensorCoordinateData` module states the ring, complex, tensor, and pure
tensor coordinate data. The item module contains the homology transport sublemma and
assembles both sublemmas into `exists_affineSpectrum_tensor_coordinates`. The item imports
the data module privately for the proof.

## Proved and sorry left

`ordinaryIsoPullbackStalkHomologyIso` remains a definition with no sorry. The target theorem
`exists_affineSpectrum_tensor_coordinates` is proved by combining the two intermediate
statements. The new declarations `exists_affineSpectrum_tensor_coordinate_data` and
`affineSpectrum_tensor_coordinate_homology_transport` retain sorry proofs, with nodes
`lem-pc-affine-spectrum-tensor-coordinate-data` and
`lem-pc-affine-spectrum-tensor-coordinate-homology` respectively.

## No longer needed

No imports or planned proof dependencies were removed; the decomposition uses the stated
ordinary stalk cohomology and tensor pullback composition dependencies.

## Where the brief, the DAG or earlier work was wrong

The original node's proof plan requires substantial affine stalk and homology transport
arguments. These are represented as two strict intermediate statements so the target can
be assembled and compiled while those arguments are proved independently.

## New nodes

`lem-pc-affine-spectrum-tensor-coordinate-data` records the strict coordinate-data
subtheorem in `AffineSpectrumTensorCoordinateData.lean`.

`lem-pc-affine-spectrum-tensor-coordinate-homology` records the homology equation for
supplied coordinate data in the item module.

## Second reading by U4

1. I compared the delivered item module with the repository version. The existing
   declarations, including `ordinaryIsoPullbackStalkHomologyIso` and the target
   theorem, retain their signatures byte for byte; the only interface addition is the
   separately imported data theorem and the homology transport theorem.
2. Both delivered Lean modules compile with `lcompile.py --all`. The two intermediate
   theorems are the only remaining named `sorry`s; there is no `sorry` in a definition,
   and no axiom, unsafe, opaque, extern, or implemented-by declaration was added.
3. The data theorem is a strict prefix of the target existential (it omits the final
   homology equation), while the transport theorem assumes exactly that data and proves
   only the final equation. Thus the split statements are true in the intended affine
   stalk and tensor setting and are strictly smaller than the target.
4. The target proof uses both intermediate declarations exactly as stated, and the
   ordinary pullback isomorphism and tensor composition imports remain in the route.
   The new data module is imported privately because it is needed only by the proof.
5. The DAG records the target proof as the assembly of the data and homology steps and
   records both split declarations with their source and Lean declarations. I found no
   statement or unit-route change.

I changed this report and corrected the two split-node proof records so their dependency
lists describe the underlying scheme, derived-category, stalk, and tensor-composition
inputs rather than referring circularly back to the target node. No Lean proof text was
changed in this second reading.
