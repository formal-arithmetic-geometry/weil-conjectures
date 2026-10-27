## What changed

Proved `actualCoefficients_coherent` and `identityCoefficients_coherent` in
`Sheaf.AlgebraicGeometry.RingedRestrictionExchangeOpenDescent`. Proved private
helpers compare canonical inverse-image compositors through their adjunction
conjugates, transport equal composite maps, and establish the two compositor unit
laws. The actual-square equation then follows by cancellation of isomorphisms;
the identity-square equation follows by naturality and the unit laws.

Added the proof-only import
`WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates`. Updated proof steps 1
and 9 and proof_origin of `lem-sf-ringed-restriction-exchange-open-descent`.
All existing public signatures and definitions are preserved.

Validation: the assigned module compiled cleanly through lcompile.py in 52.5 seconds,
within the 60-second limit.

## Proved and sorry left

Closed two of nine original holes: `actualCoefficients_coherent` and
`identityCoefficients_coherent`. Added zero holes and split off zero statements.

The seven remaining original holes, all in namespace
`AlgebraicGeometry.Scheme.RingedRestrictionExchange` and all attached to
`lem-sf-ringed-restriction-exchange-open-descent`, are:

- `degreeZero_normalization`
- `open_comparison`
- `open_sectionwise`
- `openCube_exists`
- `open_restriction`
- `open_descent`
- `identity_normalization`

Existing proved declarations are preserved. This is a partial proof delivery,
with no statement repair or decomposition.

## No longer needed

No imports, modules or nodes are withdrawn. The coefficient proofs use the
existing canonical compositors and identity comparisons; they require no new
intermediate statements or additional mathematical assumptions. All recorded
proof dependencies remain needed by the module's other proofs or remaining steps.

## Where the brief, the DAG or earlier work was wrong

No false statement or tool defect was found. The coefficient proof plan is
implemented using an explicitly chosen equal composite scheme map; this makes
the dependent transports in the HEq goals explicit. It works for arbitrary maps
and ring sheaves, including empty schemes and zero rings, with no case exclusion.

A generic degree-zero reduction from the existing cochain-unit equation was
written and compiled abstractly. Its direct specialization to the concrete
ringed functors encountered a kernel timeout, so that experiment is not part of
this delivery and the original degree-zero hole is retained.

## Second reading by W2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
