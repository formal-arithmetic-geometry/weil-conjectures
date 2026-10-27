## What changed

Filled `AlgebraicGeometry.exists_smooth_neighborhood_of_prescribedPointJet` in
`Sheaf.AlgebraicGeometry.PrescribedPointJetSmoothNeighborhood`, preserving its signature.
Added private proved helpers detecting a sheaf differential by a point derivation and
constructing such a derivation from a nonzero cotangent class at a rational closed point.
The proof imports the existing hypersurface criterion, PointCount, the source cotangent
point-derivation construction, and the tensor multiplication API privately.

The local coefficient is outside the maximal-ideal square: otherwise multiplying by
its frame coefficient would make the prescribed jet zero. Dual separation and
`AlgHom.cotangentDerivation` provide a detecting derivative. The skyscraper module and
the universal property of relative differentials turn it into a functional on the
relative differential fibre. The existing hypersurface criterion then gives the exact
smooth open neighbourhood on the original zero scheme.

Updated the item's DAG proof to describe this implementation. No statement, definition,
public import, source-library module, consumer, or unit route changes.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.exists_smooth_neighborhood_of_prescribedPointJet`
(node `lem-zl-prescribed-point-jet-smooth-neighborhood`).
No holes added or split off. No `sorry` remains in the delivered Lean module.

Validation: the server compiled the proof in 6.5 seconds. `#print axioms` for the
public theorem reports exactly `propext`, `Classical.choice`, and `Quot.sound`.
The temporary axiom-print command was removed after this check.

## No longer needed

No original imports, nodes, or modules are pruned. Every declared mathematical dependency
remains used. The full `Sheaf.AlgebraicGeometry.ClosedPointField` module is not imported:
its globally finite-type statement would require quasi-compactness, whereas the already
proved `Scheme.Hom.finite_residueField_of_isClosed` from PointCount supplies exactly the
locally finite-type assertion needed here. This is the same closed-point field input,
without introducing an extra global hypothesis.

## Where the brief, the DAG or earlier work was wrong

No statement defect found. The planned change-of-frame calculation and full cotangent-
differential isomorphism are unnecessary: the contrapositive modulo the maximal-ideal
square and one detecting point derivation suffice. The updated DAG records this shorter
implementation. In the relative-differential step the algebraic closedness is essential;
no claim is made for a general non-rational point. Empty schemes give no z, and a zero
section cannot satisfy the nonzero-jet hypothesis.

## Second reading by J1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
