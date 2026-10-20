## What changed

The unchanged `CategoryTheory.scalarInternalHomAdjunction_exists` is proved by
constructing the normalized scalar models, the strong tensor comparisons and the
five-Hom-bijection internal-Hom isomorphism. Evaluation, uniqueness, representing
bijections and conservativity are proved. The coefficient-tower and identity equations
are proved from the separate tensor-coherence result described below.

The existing data declarations move to `ScalarInternalHomData`, publicly reexported
by the item. Their names, signatures and mathematical content remain unchanged.
`ScalarHomTensorComparison.normalization` has its definitionally equal representative
square packaged as `ScalarHomTensorNormalization`, to control repeated elaboration.
The change record gives both expressions verbatim and lists consumers. No declaration
or public import of the adopted `WeilConjectures` source tree is changed.

The new proof modules establish the abstract closed-Hom construction, its composition
and transport formulas; independent-universe ordinary scalar tensor cancellation;
all-K-flat preservation; the normalized ordinary tensor comparison; and its actual
chain and derived comparisons. `ScalarHomCanonicalIso` names the explicit five-bijection
construction. `ScalarInternalHomTowerCoherence` combines the abstract composition and
transport calculations with tensor coherence, including the exact recorded restriction
and left-adjoint comparison maps. `ScalarTensorTowerComparison` assembles the family.
All new proof imports are private; public imports support signatures and definitions.

## Proved and sorry left

Original holes closed: `CategoryTheory.scalarInternalHomAdjunction_exists` (one).

New hole: `CategoryTheory.scalarHomTensorCoherence`, node
`lem-sfb-scalar-hom-tensor-coherence`, in `ScalarHomTensorCoherence` (one).
Its proof is exactly `by sorry`, with its source and full generator/descent argument
in the docstring and node. It is a genuine separate tensor-coherence result from
Stacks 07A4/0D6D, comprising only the compatibility of strong tensor maps with scalar
composition and identity. It contains no internal-Hom construction, evaluation,
representing bijection, uniqueness or conservativity. This is a decomposition of the
original hole, not a net hole closure: one closed, one added, net zero. There are no
other new holes, and no hole in any definition or private declaration.

Proved public results include `ClosedScalarHom.bijection_precomp`,
`ClosedScalarHom.bijection_naturality`, `ClosedScalarHom.component_rep`,
`ClosedScalarHom.representing`, `ClosedScalarHom.evaluation`, `ClosedScalarHom.unique`,
`ClosedScalarHom.composition`, `ClosedScalarHom.transport`,
`ClosedScalarHom.adjunction_compatibility`, `ClosedScalarHom.identity`,
`ClosedScalarHom.transport_identity`,
`ScalarHomCancellation.exists_changeOfRings_tensorCancellation`,
`scalarExtension_preservesKFlat`, `ScalarHomOrdinary.scalarOrdinaryTensorComparison_exists`,
`ScalarHomTensor.scalarHomTensorComparison_exists`, `scalarInternalHomTowerCoherence`
and `scalarTensorTowerComparison_exists` (with the namespaces in their Lean modules).
The last two and the item depend on the named tensor-coherence hole; the cancellation,
K-flat preservation, ordinary/chain/derived tensor construction and abstract closed-Hom
calculations do not. The tensor-coherence module also proves private total-generator
extensionality, uniqueness of the chain comparison, uniqueness of the derived tensor
isomorphism, and uniqueness of the entire normalized comparison. These establish that
the construction selects determined data. Existing imported theorem holes are left to
their existing items.

The tensor-coherence edge cases are arbitrary nonflat maps, zero rings, unbounded
complexes, and identity maps. The balanced tensor formulas and unit equations cover
all of them. No flatness assumption on a coefficient map has been inserted.

## No longer needed

The item and its extracted data no longer import the proof modules
`RingedInternalHomExactRestriction`, `RhomGlobalSectionsOfUniverses`,
`WeilSiteDerivedTensorDescent`, `RingedTopoiCanonicalTensorPullbackOfUniverses`,
`RingedInternalHomShiftOfUniverses`, or `SiteDerivedTensorDescentIndependentCoefficients`
merely to leave the main theorem unproved. The actual new proof imports are listed above.

From the item's old proof dependency list, the direct routes through
`lem-weil-pbc-ringed-internal-hom-exact-restriction`, `lem-pur-rhom-global-sections`
and `lem-weil-pbc-adjunction-of-natural-bijection` are unnecessary: the recorded
closed tensor adjunctions give all five Hom bijections directly. The direct uses of
`lem-weil-pbc-site-derived-tensor-descent` and `def-weil-abstract-derived-category`
are replaced by the precise existing resolving-representative and tensor-descent APIs;
these ambient constructions can remain transitive dependencies of other modules.
The old top-level `tool_uses` approvals for the general tensor pullback, exact internal
Hom restriction, global sections, K-flat resolutions and site tensor descent are removed
from this node, since this node's proof no longer directly invokes them. Their relevant
parts now occur in the appropriate new nodes. The general total-complex tensor
construction is still used by `ScalarHomTensorComparison`; it is not withdrawn.

No existing library module is withdrawn and no source-tree declaration is removed.
No blueprint unit statement or realized proof step is bypassed. Pruning here concerns
this proof's dependencies, not an unsupported claim of global module deletion.

## Where the brief, the DAG or earlier work was wrong

The original plan did not supply a declaration with the complete all-K-flat scalar
normalization required by the existing data interface. General ringed-topos tensor
pullback comparisons normalize on K-flat representatives with flat terms. The present
field quantifies over all K-flat pairs. I proved the stronger scalar-specific result
using exact conservative restriction and balanced tensor cancellation, then the
existing fully faithful representative descent. The cancellation bridge also retains
the coefficient universe independent of the site's universes.

The original tower proof was a verbal pure-tensor argument. Its categorical
closed-Hom portion is now Lean: composition, adjoint transport, the identity comparison,
and all the specified coefficient transports. The remaining genuinely tensor-specific
argument is identifying the unit-normalized adjoint-composition map on representatives
and descending its tensor square. It is stated separately, rather than asserted to follow merely from existence
of an arbitrary tensor isomorphism. The new statement retains every normalization.

The existing `cochainPullbackTensorCoherence` also supplies the chain-level
composition square for identity geometric inverse images. Its packaging must still
be related to the normalized scalar adjunctions and their derived representative
comparisons; the retained tensor-coherence node records this route.

The data extraction is to avoid an import cycle between the interface and its proof
modules. It is not a statement weakening. The original theorem statement is unchanged.
The normalization-field repair is definitionally equal, as the change record shows.

## New nodes

`def-sfb-scalar-hom-comparison-data`: the extracted existing scalar pair, model,
normalization, comparison and coherence data; includes the named normalization Prop.

`lem-sfb-closed-scalar-hom-comparison`: proved construction from the five Hom
bijections, including naturality, evaluation normalization and uniqueness.

`lem-sfb-closed-scalar-hom-composition`: proved equality of the comparison for a
composite scalar adjunction with the two successive closed-Hom comparisons.

`lem-sfb-closed-scalar-hom-transport`: proved transport along compatible left/right
adjoint isomorphisms, canonical adjoint-uniqueness compatibility and the identity case.

`lem-sfb-scalar-tensor-cancellation-independent`: proved balanced tensor cancellation
for sheaf modules with the independent coefficient universe, natural in both inputs.

`lem-sfb-scalar-extension-kflat`: proved preservation of every K-flat complex under
arbitrary scalar extension, using the cancellation total isomorphism and reflection
of exactness by restriction.

`lem-sfb-scalar-ordinary-tensor-comparison`: proved normalized ordinary tensor
comparison for the recorded scalar extension, transported from the existing explicit
binary scalar-extension core and sheaf tensor models.

`lem-sfb-scalar-tensor-comparison`: proved actual chain generator comparison and
its all-K-flat normalized derived strong tensor isomorphism.

`def-sfb-scalar-hom-canonical-iso`: the explicit closed-Hom isomorphism specialized
to the scalar models and chosen normalized tensor map; it selects no arbitrary map.

`lem-sfb-scalar-hom-tensor-coherence`: the sole new hole, the sourced scalar tensor
composition/identity calculation on K-flat representatives and its descent.

`lem-sfb-scalar-internal-hom-tower-coherence`: proved deduction of the exact
internal-Hom tower and identity equations from tensor coherence using the general
composition and transport theorems.

`lem-sfb-scalar-tensor-tower-comparison`: proved assembly of the simultaneous
normalized scalar tensor comparisons with the two internal-Hom coherence equations.

Change record: `coord/changes/S7-scalar-hom-normalization-interface.md`.

Validation: all thirteen packet modules have compiled, including the chain and
derived uniqueness helpers. A final complete packet run and delivery preflight
are recorded by the delivery tool. Consumer checks and baseline timeout comparisons
are listed in the change record. No consumer adaptation is delivered.

The final main-file elaboration uses transparency controls only in the model
assembly namespace, leaving its normalized chain-adjunction proof unchanged. It
compiled directly in 17.7 seconds. The first preflight findings about consumer
records are repaired. Node signatures are generated with the actual stage-2/3
declaration parser, including its declaration keyword and short name.

## Second reading by S7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
