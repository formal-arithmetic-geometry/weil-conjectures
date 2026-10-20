## What changed

Proved `AlgebraicGeometry.Etale.geoCartierCoeffExtension`, including all three
isomorphisms, the coefficient-unit composition equation, the normalized identity
and the fixed scalar-extension composition equation. Its signature is unchanged.

The shorter route applies the existing
`AlgebraicGeometry.Etale.supported_kummer_scalar_source` to the maps from
`ULift (ZMod (ringChar A))` to A and B. Its generator normalization identifies its
units with the constructed units. Cancellation of universal arrows gives the
universal property for A → B, and the adjunction/Yoneda argument gives the specified
isomorphism. Uniqueness of maps from ZMod proves the required coefficient-map
factorization. Constant-sheaf adjunction, exact-single coherence and conjugation
of adjunctions prove the identity and composition clauses.

Added the fully proved canonical interface `Sheaf.CategoryTheory.ExactDegreeZero`.
Its named irreducible object/map/unit functions and structured functor retain the
actual single-functor construction and its canonical exact comparison. This is a
representation repair: raw localization/Shrink projections made specializing the
coherence proof exceed 60 seconds. The complete named unit and its general-site scalar specialization allow the same
calculation to compile without unfolding localization data. It does not split a
slow proof into files or substitute existentially chosen data.

`supportedConstantDerived` and `coefficientUnitDerived` use this interface.
`SupportedDerivedScalarUnit` in the unclaimed module
`Sheaf.AlgebraicGeometry.OrdinarySupportedKummerScalar` uses its `scalarUniversal` predicate.
`SheafExactDegreeZero.scalarUniversal_iff` proves equivalence with the old raw formula,
with every unbounded test object still quantified. The public signatures and
mathematical constructions are unchanged. The scalar module locally uses the existing
proved weak-sheafification instance through `scalarWeakSheafify`; this prevents
expensive searches for general right-adjoint decompositions in its unchanged
constant-generator clauses. The instance is a proposition, so the represented data
is unchanged by proof irrelevance. New public imports expose the definitions
they use. All source-library declarations and non-theorem bodies are untouched.

Change records:
`coord/changes/M9-supportedConstantDerived-named-exact-unit.md`,
`coord/changes/M9-coefficientUnitDerived-named-exact-unit.md`, and
`coord/changes/M9-supported-scalar-unit-named-interface.md`.
The definitions' target-dependent meanings are submitted to the normal re-review.

Validation: the complete item compiled in 19.2 seconds with zero errors or warnings.
The scalar-predicate module compiled in 23.2 seconds.
The unchanged SupportedKummerScalarSource consumer compiled in 18.5 seconds against
the new predicate and interface. `#print axioms` for `unit_comp`, `unit_id`,
`universal_iff`, `scalarWeakSheafify`, `scalarObj`, `scalarUnit` and
`scalarUniversal_iff` reports only `propext`, `Classical.choice` and `Quot.sound`.

Consumer searches found 654 transitive importers, with no external textual user
of the two changed item definitions. The only external textual user of the scalar
predicate is `SupportedKummerScalarSource` (held by D3); its original source is
checked against the changed predicate without an adaptation.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Etale.geoCartierCoeffExtension`
(node `lem-geo-cartier-coeff-extension`). Zero holes remain in the item.
Zero holes are added or split off. All declarations in the new interface are proved,
and the adapted scalar-predicate module has zero holes, as before.

The imported existing theorem
`AlgebraicGeometry.Etale.supported_kummer_scalar_source`
(node `lem-asd-supported-kummer-scalar-source`) remains a dependency with its
existing proof hole; this delivery proves the item from its stated declaration,
as stage 3 requires. It does not claim the entire target closure is axiom-free.

## No longer needed

Removed these private imports from the item:

- `WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Comparison`
- `Sheaf.AlgebraicGeometry.GeometricStalkAsPullback`
- `WeilConjectures.AlgebraicGeometry.ConstantSheafGeometricStalk`
- `WeilConjectures.SixFunctors.Finite.Stalk`
- `WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint`
- `Mathlib.CategoryTheory.Sites.Point.Basic`
- `Mathlib.CategoryTheory.Sites.Point.Skyscraper`
- `Mathlib.Algebra.Homology.ShortComplex.ShortExact`

The private exact-single proof import is in the new interface, where its equations
are used, rather than in the item. The original statement imports are preserved.

The item's proof no longer directly needs these old proof dependencies:
`def-weil-closed-immersion`, `lem-kun-inverse-image-monoidal`,
`lem-kun-stalk-as-pullback`, `lem-pur-sheaf-ring-derived-coefficient-adjunction`,
`lem-sfb-successive-derived-quotient-normalization`,
`lem-weil-pbc-constant-sheaf-geometric-stalk`,
`lemma-weil-pbc-finite-stalk-formula`,
`lemma-weil-pbc-geometric-stalk-conservative`, and
`prop-weil-pbc-geometric-stalks-exact`.
The original statement dependencies remain unchanged. Stalk computations are now
encapsulated by the already stated supported-residue theorem; those dependencies
can still be needed by that theorem or other modules. No module is withdrawn.

Withdrew all seven old top-level tool-use entries from this node: the derived
coefficient adjunction, successive quotient normalization, stalk-as-pullback,
inverse-image monoidality, finite stalk formula, constant-sheaf stalk and stalk
conservativity. This only withdraws this proof's direct uses.

## Where the brief, the DAG or earlier work was wrong

The original plan is mathematically valid but repeats the supported-residue
calculation. Finite characteristic and cancellation of universal arrows extend
that existing result to arbitrary finite coefficient maps, including nonflat maps.
The zero-ring case has characteristic 1 and is covered.

The raw projection-based definitions are correct but cause excessive kernel
normalization when proving their coherence. Named canonical data and a proved API
repair that representation without changing the mathematical objects or units.
No statements were disputed or weakened, and the unit's route is preserved.

The revised proof requests independent review of its generic reuse of
`lem-asd-supported-kummer-scalar-source` and of the new exact-degree-zero interface.
No new maintainer tool-use approvals have been manufactured.

## New nodes

`def-geo-exact-degree-zero-interface` records the named canonical single-functor
object/map, exact comparison, complete derived unit, its universal property and the
proved identity/composition/formula equations. It is a generic interface needed by
the repaired definitions, not a deferred mathematical result; it contains no sorry.
The three associated definition-change records are listed above. The existing item
node's proof, proof dependencies and proof origin follow the implemented argument.
The existing scalar-predicate node records the representation and equivalence check
in its proof fields; its mathematical statement is unchanged.

## Second reading by M9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
