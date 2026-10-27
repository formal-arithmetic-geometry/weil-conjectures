## What changed

Filled `WeilConjectures.RationalSmoothPurityCanonical.ordinaryModel_existsUnique`
in `Sheaf.Paper.PuritySourceTransports`, following its existing proof docstring.
Restrict the fixed `RingedSiteDualityModel.models.comparison` along the inclusion
of flat-term K-flat complexes into all coefficient K-flat complexes. This gives
the required `ProEtaleTensorModel` with the prescribed tensor functor and the
prescribed comparison at every pair of representatives. For uniqueness, first
substitute the specified tensor functor, then use extensionality of isomorphisms
and natural transformations with the component normalization.

All existing signatures, definitions, public imports, and local options are
unchanged. The proof specifies the site and coefficient universes explicitly.
No new declarations, imports, or modules are introduced. The existing definition
node has no numbered proof plan; its ordinary-model docstring already states
this restriction argument. The unit route in `sk-lem-finite` is retained.

Searches used the required launcher Lean Finder, Loogle and grep services and
direct searches of both library roots. The fixed coefficient tensor comparison
already supplies the construction; no new existence theorem is needed.

## Proved and sorry left

Closed one of the five original holes:

- `WeilConjectures.RationalSmoothPurityCanonical.ordinaryModel_existsUnique`.

Four original holes remain unchanged, all recorded in
`def-pur-canonical-purity-source-transports`:

- `WeilConjectures.RationalSmoothPurityCanonical.scalarShift_existsUnique`.
- `WeilConjectures.RationalSmoothPurityCanonical.tensorAugmentation_existsUnique`.
- `WeilConjectures.RationalSmoothPurityCanonical.tensorAugmentation_isIso`.
- `WeilConjectures.RationalSmoothPurityCanonical.tensorToOrdinary_existsUnique`.

Zero holes added; zero split off. This is a proof of the ordinary-model
specification from the existing coefficient calculus, not a claim that the
calculus's transitive axiom closure is already free of sorry.

## No longer needed

None. Both existing public imports still provide the statement-level interfaces
and definitions used by the module. No node, module or dependency is withdrawn.

## Where the brief, the DAG or earlier work was wrong

No mathematical correction was needed. The item node is a definition with an
empty proof plan; the existing theorem docstring supplies the implemented route.
The apparent missing ordinary model is obtained directly from the already
recorded tensor comparison. The two K-flat predicates agree by the existing
`CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat` theorem. Universe
annotations are necessary when projecting the comparison from the duality model.

## Second reading by N3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
