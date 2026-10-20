## What changed

Repair of returned head `56a146233`: the canonical scalar-pullback change record
now explicitly lists `Sheaf.Paper.OpenRestrictionScalarExchange` in `## Users`,
as requested by the landing tools. Its comparison retains the same type and is
proved equal to the old inverse-mate construction; no consumer adaptation is
needed. The module is absent from both current source trees and has no current
claim or rework row, so it cannot be compiled individually or restored from the
current tree. The record preserves this returned consumer explicitly. No Lean
proof or declaration is changed by this repair.

Filled the six original proof holes in `Sheaf.Paper.FiniteCoefficientDirectImage`.
All existing public statements, definitions and public imports of the item are unchanged.

Geometric composition and coefficient-chain coherence follow from adjunction-unit
identities, exact restriction squares, conjugacy of the canonical derived
compositors and the interchange law for mates. These proofs work for arbitrary
coefficient maps and complexes, as the original statements require.

The étale isomorphism uses the finite-constant projection theorem, the published
uniform cohomological-dimension bound over a separably closed field, and exact
faithful restriction of scalars. A cochain calculation identifies the two canonical
scalar/pullback isomorphisms. The bounded-below restriction mate is identified with
the published comparison using the actual derived adjunction unit and counit
identities. Bounds for the required scalar extensions follow from Tor amplitude
and the projection isomorphism. The pro-étale assertion is transported through the
recorded canonical étale/pro-étale scalar-mate compatibility square.

The private helper proofs cache proposition-valued sheaf instances and use explicit
functorial equations, avoiding repeated unfolding of derived and sheafification
data. The cochain scalar unit is a component family, matching the published
representative formula directly. In the unclaimed existing module
`Sheaf.AlgebraicGeometry.FiniteConstantProjectionFormula`, the original proof's
intermediate `hα` is named by a proved private theorem and used by its unchanged
public theorem. The item imports this private component API, avoiding repeated
unfolding of the composite projection map. Every existing public signature,
definition and import in that module is preserved. The existing DAG node's proof,
proof dependencies and proof origin now describe the item's argument.

In the unclaimed `Sheaf.Paper.EtaleProEtaleScalarMate`, consolidate the duplicate
canonical étale scalar/pullback comparison: its compatibility name now abbreviates
the published normalized definition. A complete private comparison proves equality
with its old inverse-mate construction. The item uses this API for its coherence
calculations, and the projection proof uses the common definition. The three
existing dependency holes are untouched. The corresponding existing DAG node
records the compatibility argument. The definition change reopens semantic review
for targets using it; its proved equality preserves their meaning.

Change records:
`coord/changes/finite-constant-projection-component-api.md` and
`coord/changes/canonical-etale-scalar-pullback-reuse.md`.

## Proved and sorry left

Closed 6 original holes:

- `AlgebraicGeometry.Etale.finiteCoefficientDirectImageMap_comp`
- `AlgebraicGeometry.Etale.finiteCoefficientDirectImageMap_coefficientChain`
- `AlgebraicGeometry.ProEtale.finiteCoefficientDirectImageMap_comp`
- `AlgebraicGeometry.ProEtale.finiteCoefficientDirectImageMap_coefficientChain`
- `AlgebraicGeometry.Etale.finiteCoefficientDirectImageMap_isIso`
- `AlgebraicGeometry.ProEtale.finiteCoefficientDirectImageMap_etaleOrigin_isIso`

Holes added: 0. Holes remaining in the item: 0. No new modules or nodes.
The adapted projection-formula module also has 0 holes. The definition
consolidation introduces no proof holes.
Unchanged holes in the adapted compatibility module, all on existing node
`lem-sfb-etale-proetale-scalar-mate`:

- `AlgebraicGeometry.ProEtale.scalarPullbackReverse_isIso`
- `AlgebraicGeometry.ProEtale.directImageComparisonAmbient_isIso`
- `AlgebraicGeometry.ProEtale.etaleProEtale_scalar_mate`

The proof uses existing stated dependencies; it does not claim that their own
remaining holes are closed.

## No longer needed

Removed these direct proof imports:

- `Sheaf.Algebra.Homology.BoundedFlatIndependentCoefficients`
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`
- `Sheaf.AlgebraicGeometry.ComparisonDirectImage`
- `Sheaf.AlgebraicGeometry.EtaleDirectImageVanishing`
- `Sheaf.AlgebraicGeometry.FixedComparisonDirectImageMate`
- `Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations`
- `Sheaf.AlgebraicGeometry.ProEtaleFixedScalarRestrictionDirectImage`
- `Sheaf.CategoryTheory.ModulePullbackTensorIso`
- `Sheaf.Paper.ComparisonPullbackExact`
- `Sheaf.Paper.ComparisonTorAmplitude`
- `Sheaf.Paper.DirectImageTorAmplitude`
- `Sheaf.Paper.FiniteCoefficientFlatModel`
- `Sheaf.Paper.ProjectionMateExact`
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`
- `WeilConjectures.SixFunctors.Etale.Derived.Tensor`
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`
- `WeilConjectures.SixFunctors.ProEtale.Comparison.Flat`

The newly considered direct import `Sheaf.Paper.PurEtaleScalarMateProjection` is
also unnecessary: the compatibility module's canonical definition now publicly
imports that interface. Its mathematics remains needed through that dependency.

The revised proof does not need these former direct proof dependencies:

- `lem-sf-etale-direct-image-vanishing`
- `thm-sf-direct-image-tor-amplitude`
- `lem-weil-pbc-ringed-projection-mate-exact`
- `lem-weil-pbc-ringed-topoi-derived-tensor-pullback`
- `lem-sf-flat-model`
- `lem-weil-pbc-independent-bounded-flat-kflat`
- `prop-weil-pbc-comparison-direct-image`
- `lem-weil-pbc-comparison-direct-image-canonical-mate`
- `lem-sf-comparison-pullback-exact`
- `lem-exc-constant-inverse-image-flat`
- `lem-weil-pbc-ringed-topoi-module-pullback-tensor`
- `lem-weil-proetale-direct-image-restriction-of-scalars`
- `def-weil-pbc-proetale-operations`
- `lem-sf-comparison-tor-amplitude`

The flat-model, independent bounded-flat-model, direct-image Tor-amplitude and
output constructibility routes are unnecessary: the isomorphism proof only needs
cohomological bounds, and the projection isomorphism supplies the remaining bound.
The general exact ringed projection machinery and module pullback/tensor
construction are replaced by the already stated scalar/projection identity.
The general pro-étale restriction/direct-image theorem is unnecessary; only the
canonical étale-origin compatibility square is used. Its obsolete top-level
`tool_uses` entry, `lem-weil-proetale-direct-image-restriction-of-scalars`, is removed.

These are removals from this item's direct proof route and imports. Some modules
remain transitively imported by the canonical interfaces or needed elsewhere.
No source-library declarations, modules or DAG nodes are withdrawn.

## Where the brief, the DAG or earlier work was wrong

The original route asks for more preservation theory than these six statements
need. Composition and coefficient-chain coherence have no finiteness or
boundedness requirement. The isomorphism assertions do not assert constructibility
or Tor-amplitude preservation of the output, so those preservation theorems are
not required. The unchanged hypotheses of the isomorphism statements still supply
the cohomological bounds used here.

The two scalar/pullback comparisons are separately specified canonical maps;
treating them as definitionally equal would be unjustified. The delivery proves
their equality from their ordinary adjunction mates and their cochain
normalizations before using the projection/mate identity. Faithfulness is used
only for exact scalar restriction on cohomology and reflection of isomorphisms,
not as a substitute for the scalar-adjunction uniqueness equation.

## Second reading by C4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
