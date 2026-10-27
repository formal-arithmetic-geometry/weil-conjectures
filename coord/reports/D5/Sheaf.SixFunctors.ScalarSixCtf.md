## What changed

Replaced the hole in `AlgebraicGeometry.ProEtale.CondensedRing.scalarSixCtf` by a
complete Lean assembly of the three clauses. The public theorem signature is unchanged.
The proof derives admissibility of both endpoints by induction on listed coefficient
maps, including compositions and coefficient isomorphisms. It proves preservation of
local perfectness directly from `sfbPerfectScalarChangeModel` and
`sfbPerfectScalarChangeModels`, retaining the specified local cover and support bounds.

For the last clause the proof equips scalar change with the shift structure of its
derived adjunction, obtains triangulatedness by Mathlib's adjunction theorem, pulls back
the thick target property, and proves containment by finite shift, extension-product,
and retract closure. The generic closure argument and the local model calculation are
proved private helpers, with no new holes.

Five remaining geometric/presentation steps are separate public statements with sources,
proofs in words, and nodes. The two generation steps separate finite coefficients from
integral/field coefficients. They require the native constant-ring and locally closed
extension comparisons before the existing generation results apply. The other steps are
constructibility thickness, bounds on a locally perfect extension, and the canonical
locally closed scalar comparison. These are reductions, not completed proofs of the
underlying geometric statements.

Moved the two existing definitions `sfbLocallyClosedDerivedExtension` and
`sfbPerfectScalarGenerator` verbatim into `ScalarSixCtfGenerators`, publicly reexported
by the original module. This prevents an import cycle between the assembly theorem and
its new helper statements. The original public imports remain. No adopted source-library
module changes. See `coord/changes/D5-scalar-six-ctf-generator-data.md` for the unchanged
interfaces and the consumer check. Local irreducibility attributes avoid unnecessary
unfolding of derived-category constructions during elaboration.

## Proved and sorry left

Original holes: 1. The hole in
`AlgebraicGeometry.ProEtale.CondensedRing.scalarSixCtf` is closed by decomposition;
its combining proof has no `sorry`. There are five added holes, each exactly one named
public theorem in its own new module:

- `AlgebraicGeometry.ProEtale.CondensedRing.sfbFiniteScalarGeneration`:
  `lem-sfb-scalar-six-finite-generation`.
- `AlgebraicGeometry.ProEtale.CondensedRing.sfbNonfiniteScalarGeneration`:
  `lem-sfb-scalar-six-nonfinite-generation`.
- `AlgebraicGeometry.ProEtale.CondensedRing.sfbAdmissibleConstructibleThickness`:
  `lem-sfb-scalar-six-admissible-thickness`.
- `AlgebraicGeometry.ProEtale.CondensedRing.sfbPerfectLocallyClosedExtension`:
  `lem-sfb-scalar-six-perfect-extension`.
- `AlgebraicGeometry.ProEtale.CondensedRing.sfbCanonicalExtensionScalarComparison`:
  `lem-sfb-scalar-six-canonical-extension-comparison`.

No holes occur in either definition or in the four private helper proofs. Net hole
change for this packet before other concurrent work: one closed, five added (+4).
This is a decomposition, not a claim of an axiom-free proof of the original theorem.

## No longer needed

Removed the following original private proof imports from the assembly module:

- `Sheaf.Paper.FiniteDiscreteCondensedRing`.
- `Sheaf.Paper.FiniteDiscreteSchemeRing`.
- `Sheaf.SixFunctors.FlatModelGeneration`.
- `Sheaf.Paper.IntegralTensorShriek`.
- `Sheaf.Paper.CoefficientHeartGeneration`.
- `Sheaf.SixFunctors.CtfStabilityDirectImages`.
- `Sheaf.Paper.ProEtaleBoundedConstructibleTriangulated`.
- `Sheaf.Paper.IntegralConstantModelHeart`.
- `Sheaf.Paper.CoefficientHeartTriangulated`.
- `Sheaf.Algebra.Homology.OrdinaryDerivedChangeOfRings`.

Retained `Sheaf.Paper.CoefficientHeart` as the unit-route import.
These results remain part of the documented native-presentation arguments of the new
nodes where needed. They are not claimed globally pruned. In particular the finite,
integral, field, uniform-bound, and scalar-pullback unit routes remain in the new nodes;
no existing upstream declaration is removed. The assembly uses Mathlib's derived
adjunction directly for triangulatedness, and handles composite maps directly with the
local scalar calculation rather than iterating scalar-tower isomorphisms. No module is
withdrawn, and no globally unnecessary node is claimed.

Validation: the complete assembly compiled with profiling in 18.1 seconds. Profiling
options were then removed. The delivery tool checks the final packet independently.
The supporting modules previously compiled in 32–49 seconds each.

## Where the brief, the DAG or earlier work was wrong

The existing dependency statements provide native coefficient categories and generation
or direct-image functors, whereas this theorem specifies arbitrary isomorphic condensed
coefficient presentations and the canonical image-factorization composite. Their
conclusions cannot be applied verbatim without the presentation comparisons and finite
closure normalization recorded in the new nodes. No dependency being unfinished was
treated as an obstruction. The local perfectness step does fit the existing two
scalar-model declarations and is proved from them without a new statement.

Checked the new statements against the source's three steps. Zero complexes, rank-zero
projectives and empty strata are allowed; no claim of flatness for a listed map is used.
The extension comparison is stated for an arbitrary derived object; its proof uses the
open/closed comparison from scalar-six-pullback. Constructibility thickness does not
assert finite Tor amplitude for arbitrary constructible complexes. The original target
and generator definitions are unchanged. No statement is marked disputed.

## New nodes

`def-sfb-scalar-perfect-generators` attaches the two existing generator definitions to
their factored data module; it introduces no new mathematical object or hole. Change
record: `coord/changes/D5-scalar-six-ctf-generator-data.md`.

`lem-sfb-scalar-six-finite-generation` is the finite-coefficient portion of the source's
generation step, including constant-ring transport and normalization of finite closure.

`lem-sfb-scalar-six-nonfinite-generation` is its integral/field portion, using the
integral tensor-shriek and coefficient-heart generation arguments and native transports.

`lem-sfb-scalar-six-admissible-thickness` isolates the bounded-constructibility closure
argument. The assembly separately intersects with the already-stated finite-Tor closure.

`lem-sfb-scalar-six-perfect-extension` combines uniform local bounds with the direct-image
stability of a locally closed immersion; it contains no coefficient change operation.

`lem-sfb-scalar-six-canonical-extension-comparison` identifies scalar change of the
specified image-factorization extension with extension of scalar change. It has no
constructibility, generation or finite Tor conclusion.

## Second reading by D5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
