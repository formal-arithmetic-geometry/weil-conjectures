## What changed

Filled four theorem proofs in `Sheaf.AlgebraicGeometry.VectorTraceGeometricDescent`.
The projection proof reuses the finite-coefficient compact-support projection theorem
and composes its component with the signed symmetries and exact-pullback comparison.
The compactification-triangle proof expands the existing tower comparison and the
specified proper/open compositor; their components agree by associativity.
Concentration reuses `vectorIntegration_cohomology_zero`. Invertibility uses the
actual glued trace normalization on a locally free frame cover, the affine top trace,
and a proved private derived version of jointly surjective inverse-image conservativity.
The empty-base proof applies that conservativity to the empty covering family, making
the target a zero object and hence its incoming Hom sets subsingletons.

All existing public signatures, definitions, attributes and public imports are unchanged.
Two private proof imports provide exchange/projection invertibility and cover conservativity.
The existing node's proof, proof dependencies and proof origin now record these arguments;
the plans for the four unfinished clauses remain in place. No other modules are adapted.

## Proved and sorry left

Closed 4 of the original 8 holes, with no holes added or split off:

- `AlgebraicGeometry.Etale.vectorTrace_projection_isIso`.
- `AlgebraicGeometry.Etale.vectorBundleIntegration_compactificationTriangle`.
- `AlgebraicGeometry.Etale.vectorBundleIntegration_concentration_and_isIso`.
- `AlgebraicGeometry.Etale.vectorBundleIntegration_empty`.

Four original holes remain, all attached to
`lem-pur-vector-trace-geometric-descent`:

- `AlgebraicGeometry.Etale.vectorBundleIntegration_baseChange`.
- `AlgebraicGeometry.Etale.vectorBundleIntegration_directSum`.
- `AlgebraicGeometry.Etale.vectorBundleIntegration_swap`.
- `AlgebraicGeometry.Etale.vectorBundleIntegration_zero`.

The retained statements and their complete proof plans are unchanged. Base change needs
comparison of the pulled-back frames with the generator-defined geometric square and
pasting of exchanges. Direct sums additionally need the ordered affine counit calculation
and descent of that calculation. Swap needs the block permutation comparison with the
affine linear action. Rank zero needs the empty-tower normalization compared to its
specified identity exchange. None of these equations follows from mere invertibility.

No private helper contains a hole. Existing dependency theorems are used with their
present proof status; this is not a claim that the targets' whole axiom closure is closed.

## No longer needed

Removed these unused direct private proof imports:

- `Sheaf.AlgebraicGeometry.CompactProjectionExchange`.
- `Sheaf.Paper.DegreeZeroDerivedMapGluing`.
- `Sheaf.AlgebraicGeometry.RelativeSpecBaseChange`.
- `Sheaf.AlgebraicGeometry.AffineSpaceTopTrace`.
- `Sheaf.AlgebraicGeometry.AffineSpaceLinearTraceInvariance`.
- `Sheaf.AlgebraicGeometry.QuasiCoherentSymmetricAlgebraCore`.
- `WeilConjectures.AlgebraicGeometry.AffineMorphismRelativeSpec`.
- `WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact`.
- `Mathlib.CategoryTheory.Adjunction.Basic`.
- `Mathlib.AlgebraicGeometry.Noetherian`.

Facts used from affine top trace, exact inverse image, adjunctions and Noetherian schemes
are already available through retained public imports. The completed concentration and
invertibility clause uses existing concentration and conservativity instead of another
application of degree-zero map gluing. The triangle clause follows directly from the tower
comparison, without the multiplication equation. No entire dependency module is claimed
pruned: the retained unfinished clauses still require the original geometric/descent
plan, so their DAG dependencies remain. No source-library declaration is removed.

## Where the brief, the DAG or earlier work was wrong

No statement error or definition repair was found. The planned proof of invertibility
can be shortened using existing cohomology concentration and cover conservativity.
The compactification-triangle clause can be proved directly from the existing tower
comparison, independently of the more substantial direct-sum equation.

The first direct expansion of the proper/open projection proof exceeded the compile
limit because instance search unfolded the large derived constructions. Reusing
`isIso_projectionMap_of_finite` and exposing only the four outer factors avoids this. Profiling also exposed expensive
unification against the glued integration construction. The proof now passes the
morphism explicitly to cover conservativity and locally keeps the glued integration
and gluing data irreducible, unfolding them only for their normalization theorem.

## Second reading by B4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
