## What changed

Replaced the whole-proof sorry in
`AlgebraicGeometry.affineSpectrumCoordinates_stalkCondition` with a proof from
termwise representative transport, pointwise additive-arrow conjugacy, and the
existing fixed-square coordinate-invariance theorem. The statement and both
original public imports are unchanged. Added proof-only imports of
`Sheaf.AlgebraicGeometry.AffineSpectrumCoordinateRepresentatives`,
`Sheaf.AlgebraicGeometry.AffineSpectrumStalkConjugacy`, and
`Sheaf.AlgebraicGeometry.StalkComparisonCoordinateInvariance`.

The representative theorem has only X, Xprime and gprime; it constructs coordinates
with exactly the two termwise-pulled-back complexes. It contains no square or
stalk condition. The conjugacy theorem assumes such representatives and concerns
one point and one degree; it gives an isomorphism of additive comparison arrows
without assuming either arrow invertible. The original theorem combines these
strict parts by preservation/reflection of isomorphisms, then passes to arbitrary
coordinates and all points. No object is defined by choosing an arbitrary witness.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.affineSpectrumCoordinates_stalkCondition`
(node `lem-pc-affine-spectrum-stalk-condition`). No sorry remains in that module.

Added two whole-proof holes, each in its own module:

- `AlgebraicGeometry.SingleComplexBaseChange.exists_affineSpectrum_coordinate_representatives`
  (node `lem-pc-affine-spectrum-coordinate-representatives`).
- `AlgebraicGeometry.SingleComplexBaseChange.nonempty_affineSpectrum_stalkComparison_arrow_iso`
  (node `lem-pc-affine-spectrum-stalk-conjugacy`).

This is a decomposition: one upper hole closed and two lower holes added, not an
axiom-free proof of the transport theorem. All three delivery modules compiled together in import order with lcompile.py.
The final logical combination was also compiled independently in `scratch/lean/Bridge.lean`, using arbitrary spectrum
coefficient objects and a pointwise arrow-conjugacy hypothesis. The inverse point
identity also compiled independently in `scratch/lean/Points.lean`.

## No longer needed

None. Both original public imports remain necessary for the theorem's statement.
All original mathematical dependencies remain needed through the new transport
statements or the coordinate-invariance theorem. The original node now names its
immediate proof dependencies instead of duplicating their transitive dependencies;
this does not claim those transitive nodes or modules are pruned.

The old immediate `proof_deps` removed from the target node are
`def-pc-scheme`, `def-pc-affine-spectrum-derived-coordinates`,
`lem-pc-ringed-spaces-derived-pullback-composition`,
`lem-weil-pbc-module-stalk-pullback`, `def-pc-base-derived-tensor-cohomology-model`,
and `lem-weil-pbc-module-stalk-exact`. These remain statement or transitive
dependencies; no module is pruned from the import closure.

## Where the brief, the DAG or earlier work was wrong

The plan's cited declarations do not directly state transport of Coordinates across
isoSpec or naturality of the tensor comparison under the four local-ring
isomorphisms. Existing coordinate invariance treats two presentations on one fixed
square; the pullback-stalk formula by itself does not identify the base-derived
tensor model counits across different base rings. These are the two new subproblems.

The unit `sk-thm-picard-semicon` has no realized nodes at this location, and its
route is unchanged. No existing signature or definition has been changed.
Edge cases of the new statements were checked mathematically: empty source
schemes, zero complexes and rings, noninvertible coefficient morphisms, and
unbounded complexes. Neither statement assumes quasi-coherence, boundedness,
flatness of the square, or invertibility of the comparison itself.

The shared compiled library initially lacked
`Sheaf.AlgebraicGeometry.AffineSpectrumDerivedCoordinates.olean`, although the
source module is present. The first full compilation stopped at this import;
no dependency was copied or rebuilt locally to work around the cache. The next
cache publication supplied the dependency, and all three modules then compiled.

## New nodes

`lem-pc-affine-spectrum-coordinate-representatives` separates construction of
termwise pulled-back coefficient representatives (step 2 of the original plan),
in `lean/Sheaf/AlgebraicGeometry/AffineSpectrumCoordinateRepresentatives.lean`.

`lem-pc-affine-spectrum-stalk-conjugacy` separates the local-ring and derived-tensor
comparison square (steps 1 and 3 of the original plan), in
`lean/Sheaf/AlgebraicGeometry/AffineSpectrumStalkConjugacy.lean`.

Both nodes record the performed LeanFinder, Loogle and grep searches, and the
unavailable LeanSearch request as unavailable. No change record is needed:
existing declarations and public imports are unchanged.

## Second reading by G1

1. **Interface and statements.** Compared the delivered target module with the repository version. The target theorem signature is unchanged byte for byte. The two split statements are proper subproblems (representative construction and pointwise arrow conjugacy), with no added hypotheses to the target. Verdict: pass.

2. **Proof and axioms.** Inspected all three modules: the target proof is a genuine composition of the split lemmas, point-map bijectivity, coordinate invariance, and Arrow isomorphism transport. The split lemmas are whole named theorems with source/docstring text and no hollow definitions. All three modules compiled locally in import order during the delivery dry run. An independent scratch import with `#print axioms` for all three declarations compiled and showed exactly `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`; the latter is expected from the open split statements. No forbidden declarations occur; the only remaining `sorry`s are the two named split theorems.

3. **Search and split quality.** Repeated LeanFinder, Loogle, grep, and source searches for affine-spectrum representative transport, tensor-pullback equivalences, and stalk-comparison conjugacy. No existing declaration states either split result. The Stacks sources (Tags 0DJ8, 0098, and 0D5S) support the decomposition route. Verdict: pass.

4. **Pruning and dependencies.** Checked that each node's `proof_deps` is exactly the union of the proof-step uses, and that the target node records only its immediate split dependencies plus coordinate invariance. No import can be removed without losing a statement or proof dependency; no old node is falsely reported as pruned. The unit route remains unchanged. Verdict: pass.

5. **DAG agreement.** Checked the recorded Lean statements against the declarations and verified line-width and module-system requirements. New nodes contain the required source, proof, searches, `status: split`, and Lean records. Verdict: pass.

Changed during second reading: no Lean statements or proofs; added this review
section and explicitly listed the old immediate dependencies removed from the
target node, distinguishing them from import-closure pruning.
