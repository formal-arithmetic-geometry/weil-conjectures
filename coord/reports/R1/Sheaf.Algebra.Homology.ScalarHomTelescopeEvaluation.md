## What changed

Replaced the proof hole of `CategoryTheory.scalarHom_telescope_evaluation`.
All existing library declarations and their signatures, definitions and public imports are preserved.
The construction uses the already proved private complex-colimit and normalized derived-unit
helpers of `InternalHomLocalizationComparison`, through a proof-only `import all`.
A second proof-only import accesses the elementary inverse-scalar calculation in
`ScalarLocalizationModuleColimit`.

The proof constructs the telescope presentation for every representative, proves its legs
by scalar cancellation and induction, and proves its change equation using full derived
restriction and the normalized zeroth leg. It verifies the scalar action on internal Hom
using the actual Hom representative comparison, without assuming the resolution functor
is linear. The existing conditional localization theorem then supplies invertibility and
the zeroth unit equation. Induction proves the comparison equation at every leg. Functoriality,
isomorphism cancellation, and counit naturality finish the two squares, representative
compatibility, and evaluation formula.

The private colimit isomorphisms have explicit equations and local irreducibility attributes
to prevent repeated unfolding of their constructions during elaboration. Derived restriction
is locally irreducible after its scalar equation is proved.
The existing `RationalTermHom.coefficientSheafify`, `RationalTermHom.coefficientCompose`,
and `RationalTermHom.coefficientLocallyBijective` are registered as local instances through
a proof-only import of `RationalTermHomComparison`. Private caches are retained only for
ring sheafification and sequential colimits. All registrations remain local to this
module, including the final comparison proof, to avoid reconstructing the standard
instances there. All cached instance classes are propositions; proof irrelevance
preserves the original public types and definition data.

The returned duplicate private declarations `telescopeCompose` and
`telescopeLocallyBijective` are removed. The redundant additive sheafification cache
`telescopeSheafifyAdd` is also removed. Their callers now use the existing coefficient
instances directly, without new aliases or duplicate proofs. Generic private helpers
are placed before the large ringed-site section-variable context, and the existing
coefficient instances are registered before elaborating that context to avoid repeated
instance construction. No helper statement or argument changes in this rearrangement.

Only the assigned module and its existing DAG node change. All new helpers are private and
proved; no public definition, public theorem, assumption, or axiom is introduced.

The local import-pruning check passes; existing theorem statements and public imports
match the current library, and the delivered Lean file contains zero `sorry` tokens.
An initial compile passed at 56.7 seconds, but the delivery probe exceeded 60 seconds;
the local instance registrations are therefore retained through the final comparison
proof to remove the repeated instance reconstruction from that proof. The revised
module compiled cleanly in 51.4 seconds.

## Proved and sorry left

Closed: `CategoryTheory.scalarHom_telescope_evaluation`
(`lem-sfb-scalar-hom-telescope-evaluation`), the single original hole.

Added holes: none. Holes remaining in the delivered module: none. No split-off statements.
The theorem is proved from the existing library declarations; this does not claim their
transitive dependencies have all been proved.

## No longer needed

The repair also removes the returned private caches `telescopeCompose`,
`telescopeLocallyBijective`, and `telescopeSheafifyAdd`, reusing the existing library
instances above. No module withdrawal is requested.

Removed the following direct proof imports:

- `Sheaf.Paper.CoefficientRingedTensorHomModel`
- `Sheaf.CategoryTheory.ScalarLocalizationSheafExact`
- `Sheaf.CategoryTheory.ExactFunctorDerivedFunctor`
- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`
- `Sheaf.CategoryTheory.ScalarLocalizationTelescopeCore`
- `Sheaf.CategoryTheory.ScalarLocalizationUnitFactors`
- `Sheaf.Algebra.Homology.RingedDerivedClosedSymmetricMonoidal`

The first and last APIs are already visible through the retained public scalar model data.
The other results need not be applied again: the existing localization comparison module
already constructs the normalized unbounded colimit identification. Accordingly the node
no longer has direct proof dependencies on
`lem-weil-pbc-scalar-localization-sheaf-exact`,
`lem-pur-sheaf-ring-derived-coefficient-adjunction`,
`lem-weil-pbc-exact-functor-derived-functor`, `lem-pc-kflat-resolution`,
`lem-pur-derived-change-of-rings`,
`lem-weil-pbc-scalar-localization-complex-colimit`,
`lem-weil-pbc-scalar-localization-unit-factors`,
`lem-sfb-dc-hom-scalar-adjunction`, or
`lem-sf-ringed-derived-closed-symmetric-monoidal`.
Its obsolete top-level tool-use entries are removed. These results can remain transitively
needed by retained modules; no global withdrawal or module deletion is claimed.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement repair was necessary. The plan repeats normalization work already
completed in the private helpers of `InternalHomLocalizationComparison`. Reusing those helpers
shortens the proof, preserves the unit route, and supplies the prescribed actual maps.
The scalar action on the fixed Hom resolution is checked after applying Q; no unjustified
linearity assumption on that resolution is used. No boundedness is imposed on PH or PL.

The returned delivery duplicated standard coefficient-instance theorems already stated
in the library. The repair imports and uses the existing declarations directly.

## Second reading by R1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
