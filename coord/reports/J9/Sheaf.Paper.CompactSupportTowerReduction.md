## What changed

Proved `AlgebraicGeometry.ProEtale.SpTowerCalculus.compact_support_tower_reduction`
with its signature unchanged. Added two proved private constructions: `evaluation`
assembles the prescribed finite comparison and proves its normalization equation;
`finite_normalization` obtains finite etale origins from the existing essential-image
criterion. The proof transports the existing finite compact-support bound to the
actual output levels, applies the existing transition-compatibility theorem, and uses
the proved reduction identity and composition helpers.

The proof imports the transition module, upstream smooth-dimension API and finite-field
characteristic API. Existing private proved helpers are accessed through `import all`
in CompactSupportUniformTorBound, FiniteRingConstructibleDerivedOrigin and
CoefficientTowerShriekCalculus. All original public imports are retained. Only the
item module and its proof-route node are changed; no source-library module, signature
or definition is changed. Updated the theorem docstring to match the compiled argument.

Validation: the complete proof compiled through lcompile.py without warnings in 12.7 s.
The delivery performs the final compile and axiom/preflight checks.

## Proved and sorry left

Closed 1 of 1 item holes:
`AlgebraicGeometry.ProEtale.SpTowerCalculus.compact_support_tower_reduction`
(node `lem-sp-compact-support-tower-reduction`).

Zero holes remain in the item. Zero holes added; zero split-off statements. The proof
uses existing dependency declarations, including the existing
`reduction_transition_compatibility`; those dependencies retain their own proof status.

## No longer needed

Removed the private proof import `Mathlib.AlgebraicGeometry.Morphisms.Etale`; the upstream
smooth-morphism API already supplies the needed base-change instances.

No node or module is withdrawn. The existing CoefficientTowerShriekCalculus module is
still needed for `finite_coordinates_exists`, `reduction_identity_aux` and
`reduction_composition_aux`. Its existential full calculus and its geometric-composition
branch are not invoked by this proof. The standalone uniform theorem's tower clause is
also unnecessary: its proved finite_bound helper supplies the stronger finite-level
package including cohomological vanishing, which is transported directly.

## Where the brief, the DAG or earlier work was wrong

The original plan proposed applying the full calculus to the supplied base, operations
and coordinates, after proving preservation for this smooth f. Its Lean theorem instead
existentially chooses those data and requires preservation for every separated finite-type
map. Preservation for this one f does not discharge that hypothesis. The existing
transition-compatibility declaration has the required universally supplied data and no
preservation premise. Constructing its FiniteNormalization directly resolves the mismatch
without changing any statement or adding a hole. The node now records this actual route.

FiniteFieldDatum records the cardinality and algebraic closure, not a CharP instance;
the proof derives characteristic p from cardinality before applying the coefficient bound.
The upstream smooth-dimension inequality proves the geometric-fibre bound directly and
covers the empty-fibre case. The item remains within the recorded tower route; no unit
statement or step is bypassed.

## Second reading by J9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
