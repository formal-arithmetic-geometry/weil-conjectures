## What changed

Proved `AlgebraicGeometry.ProEtale.CondensedRing.admissible_boundedConstructible_isTriangulated`
in `Sheaf.Paper.AdmissibleBoundedConstructibleTriangulated`, with its signature and original
public import unchanged. All new imports are private proof imports. No other existing
Lean module, public interface, definition, or target was changed.

The proof treats all six admissibility cases. Finite discrete rings are lifted explicitly
from Type 0 to the scheme universe, then compared with fixed-scalar sheaves using
`FiniteDiscreteOrdinary.encoding_constructibility`. The existing fixed-scalar Serre
closure, zero sheaf, and weak-Serre homology theorem give triangulated bounded
constructibility. The cover-index universe adjustment is proved in both directions.
For valuation rings use `isConstantModelConstructible_serre_padicIntegers`, with zero
represented by the rank-zero presentation, identity cover, and trivial stratification.
For finite rational extensions and the finite-subextension-valued algebraic closure use
`constantModelBoundedConstructible_field_triangulated`. The base Q_l and Z_l cases use
the existing condensed identifications with the bottom subextension. Finally, restriction
along the inverse monoid-object coefficient isomorphism is an exact equivalence;
constructibility transport, the derived homology comparison, and reflection of boundedness
identify the desired predicate with a triangulated inverse image.

Updated only `proof`, `proof_deps`, and `proof_origin` of
`lem-sfb-admissible-bounded-constructible-triangulated` to describe this implementation.
The parent internal-Hom devissage and the unit route are retained.

Validation: the required remote single-file compile passed without errors or warnings
in 28.0 seconds. The public theorem signature matches the original, and every Lean
line is at most 100 characters.

## Proved and sorry left

Closed the original single hole in
`AlgebraicGeometry.ProEtale.CondensedRing.admissible_boundedConstructible_isTriangulated`
(node `lem-sfb-admissible-bounded-constructible-triangulated`).

Original item: 1 hole. Delivered item: 0 holes. Holes added: 0. Split-off statements: 0.
Every private helper has a complete proof. There are no remaining `sorry` declarations
in this delivery. Existing dependency theorems are used as provided, without alteration.

## No longer needed

No original Lean import was removed: the original file imported only its statement
interface. The following original planned proof dependencies are omitted from the new
DAG route and are absent even from this item's new transitive import closure:

- `lem-sfb-discrete-noetherian-constructible-serre`, module
  `Sheaf.AlgebraicGeometry.DiscreteNoetherianConstructibleSerre`: use the proved
  fixed-scalar finite-coefficient Serre closure after normalized encoding instead.
- `prop-weil-pbc-module-bounded-constructible-triangulated`, module
  `Sheaf.UpstreamExtra.WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory`:
  apply the general weak-Serre homology theorem directly to each precise predicate.
- `sk-lem-int-integral-heart`, module `Sheaf.Paper.IntegralConstructibleHeart`:
  the existing constant-model valuation-ring Serre closure suffices directly.
- `sk-prop-sfb-cartesian-coefficients`, module `Sheaf.Paper.CartesianCoefficients`:
  shifts and triangles follow from exact derived inverse images; the separate
  pullback-and-twist theorem is unnecessary.

`det-def-sfb-constructible-tor-amplitude` remains needed for the existing
`constantModelConstructibleFiniteTor_wellDefined` isomorphism invariance; no finite-Tor
hypothesis is added. No module or declaration is withdrawn, and no claim is made that
other target branches cease to need any of the four modules above.

## Where the brief, the DAG or earlier work was wrong

No statement defect was found. The planned general integral-heart and cartesian-coefficient
steps were stronger than this obligation requires. Existing finite scalar encoding,
constant-model integral Serre closure, and coefficient-heart triangulation already provide
the needed closure without a further split. Finite discrete rings in admissibility live
in Type 0 whereas the normalized encoding uses the scheme universe; the explicit ULift
ring-object isomorphism handles this rather than identifying the two encodings by
unfolding. Zero coefficient rings and empty schemes need no extra hypotheses.

## Second reading by J4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
