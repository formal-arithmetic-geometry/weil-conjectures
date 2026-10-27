## What changed

Proved `AlgebraicGeometry.ProEtale.geoCartier_normalized_scalar_units` with its existing
statement unchanged. The mathematical constructions remain in the assigned module. The constant coefficient
map is constructed by the constant-sheaf adjunction and normalized at every object by
naturality. The Tate coefficient map is constructed by the roots tensor Hom equivalence and
the comparison adjunction; this gives its pure-root formula and ordinary universal property.
The supported constant universal property is transported from the existing ordinary etale
one through the specified source comparison, using its mate unit equation. Flatness and
`SheafExactDegreeZero.scalarUniversal_of_flat` give the two unbounded derived properties.
The construction helpers are private and fully proved. A separate fully proved predicate
conversion module keeps the kernel checks within the per-file time limit. Updated the assigned node's proof and
proof dependencies to record this route.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.ProEtale.geoCartier_normalized_scalar_units`
(node `lem-sfb-cartier-normalized-scalar-units`). No holes added; no `sorry` remains in the
item. No unproved statements were split off. The new
`AlgebraicGeometry.ProEtale.geoCartierScalarUnit_of_scalarUniversal` is fully proved. No existing signature or definition was changed.

## No longer needed

The following original direct proof dependencies are unnecessary for this argument:

- `lem-geo-cartier-coeff-extension`: use the existing ordinary supported scalar-unit lemmas
  and transport their Hom universal property directly.
- `lem-asd-finite-etale-twist-line`: obtain the line's tensor inverse from the finite Tate
  tensor-family API, and use its roots Hom equivalence for scalar extension.
- `lem-pur-derived-change-of-rings` and
  `lem-pur-sheaf-ring-derived-coefficient-adjunction`: use the proved flat-source
  `scalarUniversal_of_flat` interface instead of constructing a new derived adjunction.
- `lem-weil-pbc-ringed-topoi-derived-tensor-pullback`: transport ordinary Hom equivalences
  through comparison, then apply the flat-source lemma on the pro-etale site.

Their recorded modules are `Sheaf.SixFunctors.GeoCartierCoeffExtension`,
`Sheaf.AlgebraicGeometry.FiniteEtaleTwistLine`,
`Sheaf.Algebra.Homology.OrdinaryDerivedChangeOfRings`,
`Sheaf.Algebra.Homology.SheafRingDerivedCoefficientAdjunction`, and
`Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`.
These dependencies are removed from this node's direct plan. No existing Lean import was
removed, and no module is withdrawn or claimed globally unreachable. The supported-source
comparison remains necessary. Proof imports are private.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement was changed. The original plan is valid but unnecessarily general:
the comparison and roots Hom adjunctions suffice, without first constructing a general
comparison for derived scalar extension. The previous full-obligation split is closed here
without another split. Empty support, zero rings and the identity coefficient map require
no additional hypothesis in this proof.

## New nodes

`lem-sfb-geo-cartier-scalar-unit-of-universal`, in
`Sheaf.AlgebraicGeometry.GeoCartierScalarUnitOfUniversal`, identifies the canonical
scalar universal property with the Cartier scalar-unit predicate in the needed direction.
It is fully proved, has no finiteness or flatness hypotheses, and retains all unbounded test
objects. The initial direct proof checked but its predicate conversion alone took about
43 seconds, making the full item exceed 60 seconds. Local abstraction and direct unfolding
were tried first; direct unfolding was substantially slower. Keeping the proved conversion
in its own module avoids repeating it for the two Cartier objects. The final bridge uses
the existing abstract `scalarUniversal_derivedUnit` interface and a general categorical
associativity lemma to avoid normalization of concrete sheaf localization data. No change record is needed:
no existing module besides the assigned item, nor any other existing node, is changed.

## Second reading by Q1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
