## What changed

Proved `AlgebraicGeometry.isStrictNormalCrossingsBoundary_iff_parameters` without
changing its signature or any public import. The forward direction constructs
principal component equations from regular codimension-one quotients, extends their
list to parameters by lifting minimal generators of the total intersection quotient,
and identifies their product with the reduced-union stalk ideal. The reverse
direction proves reducedness and Cartier invertibility, then uses the existing
component/minimal-prime bijection and coordinate-stratum quotient calculation to
verify every regularity and dimension clause.

All added helpers are private and proved. The live node's forward proof step and
proof dependencies now describe the generator-lifting argument actually used.
No source-library file, definition, statement, or consumer was changed.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.isStrictNormalCrossingsBoundary_iff_parameters`
(node `lem-sfb-snc-boundary-parameter-criterion`). No holes added, none left in the
item, and no split-off modules. The complete proof compiled without warnings in
10.5 seconds through `lcompile.py`; delivery runs the final checks after removing
redundant imports and refreshing the proof docstring. The proof uses the already-stated
`RingTheory.parameter_product_ideal_properties` and
`AlgebraicGeometry.closed_component_stalk_calculus`, whose existing holes remain
in their own modules. Cartier spreading and the regular-quotient lemmas are also
used through their existing declarations.

## No longer needed

Removed proof imports:

- `Sheaf.RingTheory.RegularLocalUFDBoundaryFactorization`;
- `WeilConjectures.AlgebraicGeometry.ClosedImmersionIdealStalkRange`;
- `WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme`;
- `Mathlib.RingTheory.Localization.AtPrime.Basic`;
- `Mathlib.RingTheory.Spectrum.Prime.Topology`;
- `Mathlib.Topology.NoetherianSpace`;
- `Mathlib.RingTheory.Localization.Ideal`.

The quotient-nilpotent and localization-ideal facts are already publicly provided
by `ClosedComponentStalkCalculus` through `Localization.AtPrime.Basic`, so no
separate proof imports for them remain.

The replacement proof imports the three stated assembly dependencies:
`TransversePrimeIdealParameters`, `ClosedComponentStalkCalculus`, and
`StalkNonzerodivisorCartierSpreading`. It uses the coordinate-product assertion of
the first module; its `exists_parameters_of_transverse_primes` assertion is not
needed here because extending the chosen component generators directly avoids
proving a separate injectivity statement for the component stalk ideals. The
regular-local quotient-kernel and generator/quotient declarations remain needed.
The removed imports' nodes remain dependencies of the imported algebra/component
results where applicable: this delivery requests no whole-module withdrawal and
claims no global pruning of those dependencies. The unit route is preserved.

## Where the brief, the DAG or earlier work was wrong

The DAG's forward step proposed using transverse-prime selection on the boundary
family. Its available Lean assertion requires injective stalk ideals, whereas the
boundary predicate supplies distinct global supports. This extra comparison is
unnecessary: the regularity and dimension of the total intersection let the chosen
principal equations extend directly to parameters. The node now records this
shorter argument. The archived `lem-per-snc-boundary-parameter-criterion` attachment
records an obsolete declaration and a 2026-10-20 dead-module note; the current
`lem-sfb-snc-boundary-parameter-criterion` attachment matches the unchanged signature
and is the node updated by this packet.

## Second reading by Z8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
