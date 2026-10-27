## What changed

Reduced the original `AlgebraicGeometry.ProEtale.ComponentDerivedSquare.component_derived_pullback_square`
hole to two successive mathematical stages: an ordinary coherent component square,
and normalized derived tensor descent for a supplied ordinary square. The main proof
assembles the system and proves all three dualizability fields by the existing
`CategoryTheory.IsDualizable.map` theorem.

Moved the original data block, from `componentDirect` through `System`, verbatim into
`Sheaf.Paper.ComponentDerivedSquareData`, publicly re-exported by the original module.
Added `OrdinarySystem` (ordinary comparisons and coherence) and `TensorSystem` (tensor
lifts and monoidality) there. No existing declaration name, statement, definition body,
field or instance attribute changes. The original theorem statement is identical.

`Sheaf.Paper.ComponentDerivedSquareCoherence` proves derived identity/composition from
the ordinary equations. Its private generic helpers use the existing derived unit,
associativity, natural-isomorphism composition and whiskering laws. All localizations
remain the actual unbounded derived functors and all tensors remain the ordinary ones.

Validation: the server compiled the shared data, both split modules, the derived
coherence proof and the final assembly. The unchanged original data block was checked
byte-for-byte, and every new node dependency resolves.

Change record: `coord/changes/component-derived-square-data.md`. The two direct
external importers are `CondensedHenselianLisseRigidity` and
`CondensedIrreducibleGenericScalarModel`; their public API is preserved through the
re-export, with no source adaptation.

## Proved and sorry left

Closed the original textual hole in
`AlgebraicGeometry.ProEtale.ComponentDerivedSquare.component_derived_pullback_square`
(node `lem-zl-component-derived-pullback-square`) by an assembly proof.

Proved `AlgebraicGeometry.ProEtale.ComponentDerivedSquare.component_derived_square_coherence`
(node `lem-zl-component-derived-square-coherence`) from the ordinary identity and
composition equations, using no new hole.

Two added holes, each the entire proof of a public theorem in its own module:

- `AlgebraicGeometry.ProEtale.ComponentDerivedSquare.component_ordinary_pullback_square`
  (`lem-zl-component-ordinary-pullback-square`): only the ordinary site, coefficient
  and module comparisons, before derived tensor or localization.
- `AlgebraicGeometry.ProEtale.ComponentDerivedSquare.component_derived_tensor_lifts`
  (`lem-zl-component-derived-tensor-lifts`): only tensor descent for an already supplied
  ordinary system; no ordinary construction, derived coherence or duality conclusion.

This is a decomposition, not a net proof of the original theorem: one original hole
closed, two lower holes added (net minus one). The item module and shared data module
contain zero holes. No definition chooses an arbitrary witness from a holed existence
theorem, and no definition contains a hole.

## No longer needed

No existing mathematical module is withdrawn or globally pruned. The public imports
of the old item survive unchanged through its public data re-export.

The old private proof imports moved to the corresponding remaining stages:
`ProEtaleInverseImage`, `SiteInverseImageTensor`, `SiteMorphismComposition`,
`GeometricModuleTransport` and `GeometricInverseImageExact` belong to the ordinary
construction; `RingedDerivedMonoidalComparisons` and `ExactFunctorDerivedFunctor`
belong to tensor descent.

The private import `Sheaf.CategoryTheory.ExactDerivedComposition` is removed entirely:
its `existsUnique_mapDerivedCategoryCompIso` wrapper is unnecessary because the data
already use the existing canonical composition isomorphism. The coherence proof uses
the source library's proved unit, associativity and whiskering API directly. Thus
`lem-sfb-exact-derived-composition` is no longer a dependency of this component
argument. The exact-derived factorization and natural-isomorphism operations remain
present through the original public source imports and are not globally pruned.

The item's direct proof dependencies are now its three specialized component stages.
Removed all ten old top-level tool-use entries there, since those tools now belong
to the corresponding lower stages rather than the assembly:
`lem-weil-pbc-left-exact-site-inverse-image-tensor`,
`lem-weil-pbc-site-morphism-composition`,
`lem-weil-pbc-conjugate-iso-unit-equation`,
`lem-weil-pbc-geometric-module-transport`,
`lem-trf-geometric-inverse-image-exact`,
`lem-weil-pbc-exact-functor-derived-factorization`,
`lem-sfb-exact-derived-natural-iso`, `lem-sfb-exact-derived-composition`,
`lem-sfb-ringed-derived-monoidal-comparisons`,
`lem-weil-pbc-exact-functor-derived-functor`.

## Where the brief, the DAG or earlier work was wrong

No false statement or change to the unit route was found. The generic ringed-topos
theorem is stated on a different module encoding and on its chosen normalized derived
lifts. Applying it to these fixed internal-module functors requires transport and
localization comparisons; it is not an immediate application yielding `TensorLift`.
The two new remaining statements isolate that work and the ordinary geometric work.

Checked the identity and composite orientations against the actual definitions,
including coefficient transport, the zero coefficient ring, empty affine schemes
and arbitrary unbounded complexes. Neither split adds a henselian, w-contractible,
discreteness, nonemptiness or boundedness assumption. The main duality proof uses the
existing exact-pairing theorem, which preserves both triangle identities.

## New nodes

`def-zl-component-derived-square-data` owns the unchanged moved data and the two new
partial-stage structures in `ComponentDerivedSquareData`.

`lem-zl-component-ordinary-pullback-square` records the ordinary construction and its
normalized identity and composition equations in `ComponentOrdinaryPullbackSquare`.
It is strictly earlier than derived localization and tensor descent.

`lem-zl-component-derived-tensor-lifts` records only normalized derived tensors and
tensor/unit compatibility for a supplied ordinary system in
`ComponentDerivedTensorLifts`.

`lem-zl-component-derived-square-coherence` records the proved passage of the two
ordinary coherence laws to the fixed exact derived comparisons in
`ComponentDerivedSquareCoherence`.

All nodes inherit the item's chapter, unit, source route and blueprint ancestry.
The change record is `coord/changes/component-derived-square-data.md`.

## Second reading by D9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
