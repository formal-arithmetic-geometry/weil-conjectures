## What changed

Completed `Sheaf.Paper.GeoCartierExponentIndependence`, preserving its public statements,
definition bodies and public imports. Updated the existing exponent-independence node's
proof, proof dependencies and proof origin to describe the implemented argument.

The proof uses the existing normalized quotient and Kummer units in
`DivisibleReduction.Identifications`. Flat single-object computations make `ordinarySingle`
invertible. Full faithfulness then recovers both ordinary isomorphisms from conjugated
transitivity. A generic composite-adjunction diagram gives the quotient square and the
shifted Kummer boundary square. A kernel lift of multiplication by `m / n`, together with
vanishing of maps from the divisible middle term to the torsion sheaf, identifies the
underlying torsion map. The rotated triangle's exact Hom sequence justifies injectivity;
the proof does not cancel a Kummer boundary without this vanishing argument.

All supporting lemmas are private and proved in this module. They include localization
coherence on single objects, its shift compatibility, the ordinary-unit normalization,
the composite-unit diagram, and the boundary injectivity argument. Proof imports add the
existing independent-universe bounded-flat criterion, tensor comparison, zero-object
flatness, and exact-functor shift coherence. Local irreducibility hints keep constant
sheafification and sheafification behind their functor APIs. Explicit localization
universes keep typeclass search from comparing the two different coefficient categories.
These hints do not alter any exported definition or attribute.

The cases `m = n`, `n = 1`, and zero sheaves are covered by the same argument. Division is
used only through `n ∣ m`, via `n * (m / n) = m`; the kernel argument and exactness also
cover the zero residue ring. The Cartier unit's construction and route are preserved.

## Proved and sorry left

Closed the one existing hole:
`SheafOfModules.GeoCartierExponent.geoCartier_exponent_independence`
(node `lem-geo-cartier-exponent-independence`).

Holes closed: 1 of 1. Holes added: 0. Split off: 0. Sorries left in delivered Lean files:
none. Existing normalized-adjunction and single-exponent theorems are used as declared;
their pre-existing obligations are not new holes in this delivery.

Validation: `lcompile.py --all` compiled the complete file with artifacts in 33.7
seconds and its unchanged direct consumer `Sheaf.AlgebraicGeometry.GeoCartierCycleClass`
in 52.9 seconds. The item compiled with no warnings. The temporary consumer copy is
excluded from this delivery. Delivery additionally runs the required compile, preflight
and axiom checks. Every new import was checked with `tools/import_direction.py may`
and creates no import cycle.

## No longer needed

Removed these direct proof imports:

- `Sheaf.Algebra.Homology.BoundedAboveFlatSheafKFlat`: replaced by the existing criterion
  at independent coefficient universes in `BoundedFlatIndependentCoefficients`.
- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`: the given normalized
  identifications already include the quotient and Kummer unit equations.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`: available through public imports.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`: no direct use.
- `Sheaf.Algebra.Homology.SheafRingDerivedCoefficientAdjunction`: the normalized model
  adjunction used here is declared in `DivisibleExtensionDerivedReduction`; required
  scalar machinery also remains available through public imports.
- `Mathlib.Algebra.Homology.DerivedCategory.ShortExact`: available through the public
  single-triangle import.
- `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`: no homology calculation is
  needed; the rotated triangle's exact Hom sequence supplies the injectivity used here.
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`: publicly imported already.

Removed direct proof-dependency edges and obsolete tool approvals for
`lem-pc-bounded-above-flat-kflat-site`, `lem-pc-kflat-resolution`,
`lem-pur-sheaf-ring-derived-coefficient-adjunction`, and
`lem-sf-derived-homology-long-exact`. The replacement bounded-flat criterion is
`lem-weil-pbc-independent-bounded-flat-kflat`; its tensor comparison is recorded by
`lem-weil-pbc-independent-sheaf-tensor-colimits`.

The original plan's separate local tensor-quotient and torsion-surjectivity calculations
(steps 7 and 8) are unnecessary: both ordinary maps are isomorphisms by the derived
comparison, flatness and full faithfulness. Their formulas are established afterwards
by the normalized units and the kernel/triangle argument. No module is withdrawn, and
no claim is made that any of these modules becomes globally unreachable: other parents
and retained public imports may still need them.

## Where the brief, the DAG or earlier work was wrong

No statement repair was needed. The original plan repeated the resolution-based proof
of unit normalizations already present as fields of the declared identifications. It
also proved ordinary invertibility separately although the derived isomorphisms and
flatness already imply it. The revised node records the shorter proof and retains the
required Kummer-boundary uniqueness argument, including its vanishing hypothesis.

The initial elaboration slowdown came from expanding chosen constant-sheafification
adjoints while comparing coefficient rings and localization instances. Local API
boundaries, explicit universes and limiting permissive unification to helpers that need
it address this without changing mathematical definitions or the compiler limit.

The preflight-requested command-environment record is
`coord/changes/Y3-geo-cartier-exponent-proof-scope.md`. It documents the proof-local
attributes, scoped options and omitted private-helper parameters, and lists every
transitive downstream module with its synchronized holder. The sole direct importer
is checked without adapting its source. No forced adaptation is included.

## Second reading by Y3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
