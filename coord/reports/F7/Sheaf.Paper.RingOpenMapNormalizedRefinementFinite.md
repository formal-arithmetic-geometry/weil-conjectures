## What changed

Proved `WeilConjectures.ConstructibleExceptionalCoefficients.exists_normalized_refinement_iso_finite`
in the assigned module. The proof writes the positive exponent as m+1, extracts bounds from
finite homology support, and uses `finiteRing_constructibleDerived_origin` to retain an actual
bounded-below etale antecedent for the original input. It packages that witness as
`FrobeniusExchange.CompactOrigin`, supplies the constant-ring coefficient composition equality,
and projects the normalized isomorphism from `finite_ring_refinement_coordinates_canonical`.
The latter already states the required normalization together with an additional coordinate
identity. Its source-import graph and DAG dependencies do not return to this item.

Added three private proof imports: `Sheaf.Paper.FiniteRingRefinementCoordinatesCore`,
`Sheaf.Paper.FiniteRingConstructibleDerivedOrigin`, and
`Sheaf.AlgebraicGeometry.ProEtaleConstantRingPullbackComparison`.
Updated the assigned node's proof, proof dependencies, and proof origin to match this route.
The public statement and existing public imports are unchanged. No other existing module changes.

## Proved and sorry left

Closed 1 of 1 original holes:
`WeilConjectures.ConstructibleExceptionalCoefficients.exists_normalized_refinement_iso_finite`
(`lem-sf-ring-open-map-normalized-refinement-finite`).

Added 0 holes; split off 0 statements. The delivered module has 0 remaining holes.
The proof uses the existing stated theorem
`WeilConjectures.ConstructibleExceptionalCoefficients.finite_ring_refinement_coordinates_canonical`,
which remains sorry in its existing module; this delivery does not claim to prove that dependency.

The final single-file compile passed without warnings in 9.2 seconds. The delivery tool
records its additional compilation and axiom probe. The argument requires no nonempty
scheme, nonzero object, or nonempty homology support; finite-set boundedness handles the zero
input, and the existing normalized finite comparison covers identity refinements and empty opens.

## No longer needed

No existing import or module is removed or withdrawn. No new intermediate theorem is needed.
The assembly-data and open-restriction nodes remain statement dependencies, while the proof now
uses the already stated finite-coordinate comparison and finite constructible origin theorem.
A separate proof here of proper base change, boundary vanishing, open-closed conservativity,
or comparison normalization is unnecessary: these are the construction behind the existing
canonical finite-coordinate theorem, whose additional coordinate equation is unused here.
No unit statement or unit proof step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The previous single-step plan did not mention the already available stronger theorem
`finite_ring_refinement_coordinates_canonical`. Its normalized isomorphism clause applies once
the input's bounded-below etale-origin witness is constructed. This avoids splitting this
obligation again. The geometric construction does not need a new use of the characteristic inequality.
The proof explicitly eliminates the equal-characteristic case using `hl`; every binder and
the complete target statement are preserved.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.RingOpenMapNormalizedRefinementFinite": "e85219e9f6dc575a5d9440f99ceddb959b85cff1"}, "results": {}, "time": "2026-10-28T05:11:13+0800", "transitive": 0, "version": 1}
```

## Second reading by F7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
