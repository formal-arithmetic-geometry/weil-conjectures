## What changed

Proved the original `finiteFieldPresentation` from two strictly smaller heart assertions.
Constructed `finiteHeartRealization` as the actual scalar-extension/intrinsic-realization
composite. Proved invertibility of the specified finite scalar map by the finite clopen
fibre cover (with the empty-cover injectivity case), and proved its scalar extension is
an equivalence. The main proof constructs E as that composite followed by H, proves the
derived compatibility using the two exact-derived comparison isomorphisms and two
composition isomorphisms, and lifts an E(M)/H(N) isomorphism through fully faithful H to
transport constructibility using the existing intrinsic encoding theorem.

Added three new modules, three nodes, and the change record
`coord/changes/G9-embedded-finite-field-presentation-decomposition.md`.
Existing public imports, definitions and the theorem signature are unchanged.
The item's new imports are private proof imports. No adopted source-library module changes.

## Proved and sorry left

Original hole closed:
`AlgebraicGeometry.ProEtale.IntegralModelsEmbedded.finiteFieldPresentation`
(node `lem-sfb-embedded-finite-field-presentation`). Its proof now contains no sorry.

Additional fully proved declarations:
`AlgebraicGeometry.ProEtale.IntegralModelsEmbedded.finiteScalarMap_isIso` and
`AlgebraicGeometry.ProEtale.IntegralModelsEmbedded.finiteScalarExtension_isEquivalence`
(node `lem-sfb-embedded-finite-heart-realization`).
`finiteHeartRealization` has a concrete, hole-free definition.

Two holes added and left, each the entire proof of its public theorem:

- `AlgebraicGeometry.ProEtale.IntegralModelsEmbedded.finiteHeartMonoidalPresentation`
  (node `lem-sfb-embedded-finite-heart-monoidal-presentation`): equivalence of the specified
  intrinsic heart realization and a monoidal comparison to the small coefficient site;
  no derived or constructibility assertion.
- `AlgebraicGeometry.ProEtale.IntegralModelsEmbedded.finiteHeartConstructibility`
  (node `lem-sfb-embedded-finite-heart-constructibility`): constructibility of a single
  module under the explicit heart functor; no equivalence, monoidal or derived assertion.

This is a decomposition, not a complete proof free of admitted dependencies: one upper
hole closed, two lower holes added (net minus one). The item has zero textual holes;
the delivered modules have two textual holes in total.

## No longer needed

No existing import removed and no module withdrawn.
The original node's direct dependencies on
`lem-weil-pbc-finite-discrete-condensed-ring-constant`,
`lem-sf-finite-discrete-normalized-encoding`,
`lem-pe-internal-section-tensor-comparison`,
`lem-ctf-finite-comparison-model-realization`,
`def-weil-pbc-proetale-modules`, `def-sfb-integral-model-generator-data`,
`lem-sf-finite-discrete-encoding-constructibility`, and
`def-weil-proetale-constructible-sheaf` are replaced by the actual proof dependencies.
The tensor, small-site, generator and constructibility ingredients remain in the
appropriate smaller nodes' plans. The scalar-map proof uses the canonical map directly,
so it does not choose the existential coefficient isomorphism from
`lem-weil-pbc-finite-discrete-condensed-ring-constant`. The normalized continuous
`Encoding` is not itself used as the embedded discrete presentation. These observations
remove no declarations or dependencies of other modules.

## Where the brief, the DAG or earlier work was wrong

The declared dependencies provide related continuous-coefficient encodings, but their
signatures do not directly identify the exact embedded discrete scalar-extension/derived
realization functor, with its double lift and specified small coefficient site. This
packet isolates the missing heart comparison and local-model comparison, while proving
the derived glue rather than shifting that full obligation again.

The original citation of Stacks Tag 03ET is about preservation of flatness by
sheafification, rather than the constant-function coefficient isomorphism itself.
The actual proof is the finite clopen local-bijection argument; Tag 03CY supplies
module sheafification, and Tag 00YV supplies functoriality of algebraic structures.
The original theorem statement and source docstring are retained.

## New nodes

`lem-sfb-embedded-finite-heart-realization`: actual scalar-map invertibility,
scalar-extension equivalence, and the concrete heart composite. Both assertions proved;
no arbitrary object is chosen from a holed existence theorem.

`lem-sfb-embedded-finite-heart-monoidal-presentation`: the underived monoidal heart
comparison, for finite commutative rings and arbitrary schemes, without a field or
Noetherian hypothesis. The source and pure-tensor coherence argument are in the docstring.

`lem-sfb-embedded-finite-heart-constructibility`: the single-sheaf local-model comparison
for finite fields on Noetherian schemes. Its proof in words keeps strata, covers, finite
presentation matrices, and the positive-stratum convention on empty schemes.

All three nodes stay in the integral-models unit; no unit statement or route is changed.

## Second reading by G9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
