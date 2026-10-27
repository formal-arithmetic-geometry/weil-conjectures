## What changed

Proved the original system_scalar_projection_identification by a genuine decomposition
into three strict subarguments. The main Lean proof constructs an inverse from fixed basis
coordinates, proves derived scalar restriction conservative using the homology criterion,
proves the upper scalar/refinement square by injectivity of the scalar adjunction Hom
bijection, and transports all four refinement coherence laws by cancellation.

The existing 44 data declarations are moved verbatim to SystemScalarProjectionData and
publicly reexported by the original item. This permits the strict subargument modules to
refer to the definitions without an import cycle. No definition body, existing signature,
target statement, or coefficient universe changes. The source-library tree is untouched.
The factorization resolves an import cycle. Profiling showed failed comparisons expanding
the p-adic valuation implementation; local irreducibility hints on the coefficient
integers and absolute value avoid that unfolding without changing their public attributes.
Completed geometric and comparison words also receive local irreducibility hints.
Unused automatic SizeOf and constructor-index helper generation is disabled for
these proof-data records. The final data module compiled in 43.2 seconds, and the
main proof compiled in 20.5 seconds.
Change record: coord/changes/V8-system-scalar-projection-data.md.

## Proved and sorry left

One original hole is closed:
WeilConjectures.SystemScalarProjection.system_scalar_projection_identification
(lem-coef-system-scalar-projection-identification).

Three strictly smaller holes are added, each with a full proof in words and a matching node:

- WeilConjectures.SystemScalarProjection.normalized_scalar_tensor_constituents
  (lem-coef-system-scalar-tensor-constituents).
- WeilConjectures.SystemScalarProjection.scalar_basis_distributivity
  (lem-coef-system-scalar-basis-distributivity).
- WeilConjectures.SystemScalarProjection.scalar_refinement_restriction
  (lem-coef-system-scalar-refinement-restriction).

The item module has zero sorry; the data module has zero sorry; each new statement module
has exactly one whole-proof sorry. This is a decomposition, not a net proof gain: one upper
hole closed and three lower holes added. In particular invertibility and the upper
refinement laws are proved in the item, not included among the new obligations.

## No longer needed

The direct private import of Sheaf.Paper.SystemCompactificationProjectionSubstitution is
removed from the original data prefix. Its lower-tower theorem is still needed by the
refinement restriction subargument, so no claim of global pruning is made for that module.
The original public imports move with their unchanged definitions into the publicly
reexported data module; they are not withdrawn from the public API. No module or existing
DAG node is withdrawn, and no dependency of the unit route is bypassed.

The old proof dependencies remain used below the new subarguments: finite-free system
restriction, semilinear derived sections, adjunction mates, open tensor normalization,
system projection coherence and system compactification substitution. The original node
now records the three strict subargument nodes as its immediate proof dependencies.
No whole-library pruning is claimed.

## Where the brief, the DAG or earlier work was wrong

The original single sorry covered several substantial compatibility constructions. The
existing dependencies provide their underlying calculus, but not a ready-made theorem
for the simultaneously pinned TensorNormalization, LevelData and fixed BasisCoordinates
records. These are now explicit independent obligations rather than silent gaps in a
proof body. The original mathematical statement is preserved.

The original ramification distinction is retained. Only the lower DVR tower supplies
refinement laws directly; upper gamma invertibility is obtained through restriction in
the refinement subargument, and upper refinement coherence is proved by scalar comparison
cancellation in the main theorem. No faithfulness of restriction or of level evaluation
on derived morphisms is assumed.

Edge cases checked mathematically: zero and empty-scheme inputs give zero equations;
identity scalar extension and identity geometric maps give identity mate equations;
ramified towers use the same reduced integral basis and the same quotient transitions;
n=0 is exponent 1; no uniform cohomological or Tor interval is introduced. The finite-sum
inverse argument also works with an empty indexing type, since totality forces its
corresponding object to be zero. The fixed basis existence assertion itself retains its
original coefficient-basis hypotheses through s.

## New nodes

- def-coef-system-scalar-projection-data records the unchanged data definitions now in
  Sheaf.Paper.SystemScalarProjectionData. No existence assertion or hole is added here.
- lem-coef-system-scalar-tensor-constituents isolates original Steps 1--4: normalized
  tensor presentations, pinned geometry, proper/open word identities and finite evaluation.
  It omits scalar comparison invertibility, basis distributivity and every refinement law.
- lem-coef-system-scalar-basis-distributivity isolates the fixed-coordinate construction
  and summand equations of Steps 1 and 5. The item proves that these imply invertibility.
- lem-coef-system-scalar-refinement-restriction isolates the lower refinement theorem and
  restriction of its factors, including upper gamma invertibility and naturality at the
  scalar unit. The item proves the upper scalar square and upper coherence from it.

The new statement nodes inherit the source and unit of the original obligation. Searches
used LeanSearch, LeanFinder and grep, with their actual queries/results recorded. General
Mathlib adjunction, finite-biproduct and scalar-restriction facts do not already state the
project-specific normalized system words. Blueprint searches found no duplicate statement.

Source text read in the current blueprint: `literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-prop-scalar-six/sk-prop-scalar-six.proof.md`, Ordinary direct image, Compactly supported direct image, and Construction of comparison maps. The new nodes spell out the system refinements of those paragraphs following the original reviewed node Steps 1--7.

## Review by V8

I checked the reduction against the unchanged original conclusion and each new theorem
signature. The basis obligation asserts only coordinates and summand equations; the
finite-sum inverse is constructed in the item. The tensor obligation supplies projection
and scalar-mate equations with the same normalized presentation. The refinement obligation
supplies lower laws and geometric restriction, while the item proves the upper square by
adjunction injectivity and then proves all upper laws by cancellation. In particular the
ramified upper tower never receives lower-tower coherence by an unsupported substitution.
All data bodies and existing declaration signatures were compared with the source.
This is the worker's own check; the maintainer's independent review remains necessary.

## Second reading by V8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
