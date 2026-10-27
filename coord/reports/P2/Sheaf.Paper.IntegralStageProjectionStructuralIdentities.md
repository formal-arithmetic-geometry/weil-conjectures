## What changed

Restored the quarantined item module at its existing path and preserved its public
statement. Replaced its structural-identity hole by explicit finite-stage transport:
projection composition uses naturality and the recorded support/pullback compositor
squares; the pentagon uses the compositor square twice on each route; proper coincidence
uses the proper-identification coefficient square. Endpoint isomorphisms cancel, and a
proved constructible Milnor injection detects the integral equalities. The pentagon
requires no new split-off normalization hypothesis. The long path algebra is checked
in private generic category lemmas, keeping elaboration independent of the large
operation-model definitions.

Added IntegralProjectionReductionData for the actual finite-Tor lift of reduction and
specified tensor/support/direct/pullback endpoint coordinates. Its membership proof uses
integral_residue_tor. Added IntegralReductionShiftedHomFiniteQcqs, proved from the existing
private intrinsic_hom_finite theorem via a proof-only `import all`, scalar adjunction and
the integral residue-Tor criterion. Added IntegralReductionJointFaithfulness, proved from
the target's defining Roos triangle and the source Milnor theorem. Added
IntegralProjectionReductionCoordinates for the remaining primitive normalized tensor and
single-projection reduction squares. The coordinates are chosen only inside theorem
proofs; no definition chooses arbitrary data from an unproved existence theorem.

Profiling identified repeated rewrites over large operation-coordinate types. Local
irreducibility for the large tensor/projection definitions and private generic path
lemmas keep the calculation within the per-file limit; development profiling options
are removed.

All existing public imports and signatures are preserved. Only the item, new modules and
their DAG nodes change; no adopted source module is edited.

## Proved and sorry left

The original hole of
`WeilConjectures.integralStageProjection_structuralIdentities` is closed by a complete
Lean combination of finite laws, normalization squares and the Milnor injection.

New proved declarations include:

- `WeilConjectures.IntegralProjectionReduction.reduction_finiteTor`;
- `WeilConjectures.integralReduction_shiftedHom_finite_qcqs`;
- `WeilConjectures.integral_reductions_jointly_faithful`.

One new hole remains:
`WeilConjectures.integralProjection_reduction_coordinates`, node
`lem-sf-integral-projection-reduction-coordinates`. It asserts natural tensor coordinates
and reduction squares for individual projection maps. It asserts none of the composition,
pentagon or proper-coincidence conclusions. Its docstring gives the scalar associator and
adjunction-mate calculation, including the normalization of all endpoints, and names
the existing strict tensor-tower comparison and scalar projection-pasting theorem.

Thus one original hole is closed and one strictly lower hole is added: this is a
decomposition, with zero net holes closed. There are no holes in definitions and no
anonymous or private holes. Existing imported finite-stage laws retain their own nodes
and proof obligations.

## No longer needed

No original Lean import was removed: the item originally imported only
ConstructibleProjectionMates. The new proof does not need these original planned direct
DAG dependencies:

- `lem-sf-integral-compactification-system-realization`
  (`Sheaf.SixFunctors.IntegralCompactificationSystemRealization`);
- `lem-sf-projection-integral-coherence-realization`
  (`Sheaf.SixFunctors.ProjectionIntegralCoherenceRealization`);
- `lem-sf-integral-projection-refinement-square`
  (`Sheaf.Paper.IntegralProjectionRefinementSquare`).

Their entire system-route assembly, three-cell/pasting constructors and common-refinement
proper-coincidence detour are unnecessary for this item's proof. Their declarations and
files remain intact for other consumers. Integral residue Tor remains necessary through
the actual finite-Tor reduction construction and finite shifted-Hom proof. The unit's
projection-formula route is retained: finite laws, normalized reduction and integral
reconstruction, then coherence. No blueprint unit statement or realized step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The old plan forbade concluding equality from finite evaluations. This remains correct
for unrestricted derived objects, but constructible integral objects admit a proved
Milnor injection once the shifted Hom groups are finite. The finite-coefficient private
intrinsic_hom_finite theorem already has no separatedness hypothesis on the structure
morphism, although IntegralConstructibleReductionHom's wrapper adds one. Reusing the
stronger existing theorem avoids adding a new affine-cover finiteness obligation.

An arbitrary isomorphism of projection arrows, as supplied by
IntegralStageProjectionReduction, does not identify the specified tensor and adjunction
endpoints. The remaining lower statement records those exact normalized squares instead.

## New nodes

`def-sf-integral-projection-reduction-coordinates`: actual reduction lifted to finite Tor,
its pullback comparison, and composites giving tensor/projection endpoint coordinates.

`lem-sf-integral-reduction-shifted-hom-finite-qcqs`: proved finiteness of shifted Hom into
restricted reductions, by the existing qcqs finite-coefficient Hom theorem and adjunction.

`lem-sf-integral-reductions-jointly-faithful`: proved constructible Milnor injection, with
no claim about unrestricted finite evaluation.

`lem-sf-integral-projection-reduction-coordinates`: remaining normalized scalar tensor
and individual proper/open projection reduction squares, strictly below the structural
identities. No existing interface changed, so no change record or forced adaptation is
needed.

## Second reading by P2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
