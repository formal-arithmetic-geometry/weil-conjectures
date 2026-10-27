## What changed

Filled seven existing theorem holes in Sheaf.Paper.RootTowerCoordinateFace.
The proofs establish the base ideal containment, the structural square, monotonicity,
nested squares, profinite squares, naturality, and the surjective closed immersion into
the cartesian fibre. All existing declaration signatures and definition bodies are preserved.
Private proved helpers use root equations, prime ideals, quotient spectra and pullback squares.
The retained packet compiled without warnings in 12.2 seconds (compile result
08dd1fb62bb8bc2547ab507b). Subsequent normalization experiments were reverted.

## Proved and sorry left

Closed 7 of the original 13 holes, all in
AlgebraicGeometry.ProEtale.RootCoordinateFace:
baseIdeal_le, square, ideals_mono, nested_square, profinite_square,
exchange_naturality, fibreInclusion_properties.

Six original named holes remain: exchange_adjuncts, exchange_vertical_pasting,
exchange_horizontal_pasting, exchange_cube, exchange_proetale, coordinateFace.
They retain their original statements and proof docstrings, attached to
lem-sfb-root-tower-coordinate-face. No holes were added and no statements were split off.

## No longer needed

The completed algebraic and geometric proofs use quotient spectra and pullback
universal properties directly. They do not use WContractibleAffineCover,
IndEtaleStability, AffineClosedSiteFunctorProperties, HenselianClosedLift,
CondensedHenselianLisseRigidity, WeakContractibleEquivalences, ClosedInverseImageLimits,
ProEtaleWContractibleSectionsExact or WLocalComponents.
Their direct proof imports were removed. Direct imports of RightDerivedFunctor.Comp,
CondensedAmbientExchange, InternalModuleOperationsTransport,
UnboundedSectionsLocalization and ProEtaleWeaklyEtaleLocalization were also removed
from this partial packet. Their mathematical inputs remain relevant to the six unfinished
original statements, so no DAG dependency or module is claimed pruned from the full argument.

## Where the brief, the DAG or earlier work was wrong

No statement error found. For fibreInclusion_properties, the root equations show directly
that a prime contains the selected parameters if and only if it contains all their roots.
This replaces the presentation calculation in that part of the proof.

The compile service later failed before invoking Lean with exit code 125:
stdbuf could not create a temporary directory in /tmp: No space left on device
(os error 28). This prevents further compilation and delivery verification.

## Second reading by W5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
