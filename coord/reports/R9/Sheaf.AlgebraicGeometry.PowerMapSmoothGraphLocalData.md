## What changed

Proved `AlgebraicGeometry.powerMap_smooth_graph_local_data` in
`Sheaf.AlgebraicGeometry.PowerMapSmoothGraphLocalData`, preserving its complete
statement and all existing public definitions and instances. Added only proved
private helpers. The differential calculation compares dual-number-valued section
maps on the given structural constants and generators. The product tangent
isomorphism supplies the projection formulas, and pullback extensionality proves
the graph and diagonal formulas. Linear algebra proves intersection and sum.

For the smooth clause, choose affine W inside V intersect h⁻¹(V), with V inside U.
Smoothness and regularity transfer along these open charts. The rational
cotangent-dual identification gives both local dimensions. Sections of the first
projection have surjective stalk maps; their quotient-by-kernel isomorphisms give
the two regular quotients. A private universal-property argument identifies the
quotient by the sum of kernels with the actual fixed-scheme stalk, with its
prescribed stalk-map formula. Its composition with the inverse structural field
isomorphism gives the final field isomorphism and maximal-ideal equality.

The recorded searches found smooth-algebra and differential lemmas, but no
existing result combining this power differential with the graph/equalizer stalk
identifications. The proof reuses the existing product-tangent and rational
tangent/cotangent equivalences rather than rebuilding them.

Updated the existing DAG node's proof, proof dependencies and proof origin to
match this argument. Proof imports are private. No source-library module is
changed, no public interface is changed, and no change record is needed.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.powerMap_smooth_graph_local_data`
(node `lem-trf-power-map-smooth-graph-local-data`).

Item holes before: 1. Item holes left: 0. Holes added: 0. Split off: 0.
Every private helper has a complete proof. There are no new modules or nodes.

The complete file compiled without errors or warnings in 39.3 seconds before
preflight. The first preflight flagged a file-wide elaboration option and a
private instance with a global instance attribute. The option is now scoped
to individual proof declarations and the unused instance is removed. The revised
file compiles without errors or warnings in 36.8 seconds, and the project
interface checker reports no changes. The proof
uses the project's existing product-tangent and rational-cotangent results;
the delivery's axiom probe determines the resulting dependency axioms.

## No longer needed

Removed the proof imports
`Sheaf.AlgebraicGeometry.RationalTangentCotangentDuality`,
`WeilConjectures.AlgebraicGeometry.RationalPointStalkTopologicalLocalDimension`, and
`Mathlib.AlgebraicGeometry.Morphisms.Etale` from the original item. The new proof
uses the narrower existing
`WeilConjectures.AlgebraicGeometry.RationalPointTangentDerivationIdentification`
directly. Development-only redundant imports of
`WeilConjectures.Mathlib.RingTheory.DualNumber` and
`Mathlib.Algebra.Ring.Subring.Basic` were also removed.

The following former planned dependencies are unused by this proof:

- `lem-sc-rational-tangent-cotangent-duality`: only the rational-point linear
  equivalence is needed, supplied directly by
  `lem-sc-rational-point-tangent-derivation-identification`.
- `lem-ag-rational-point-stalk-topological-local-dimension` and
  `sbc-lem-smooth-relative-dimension-locally-constant`: no chart of constant
  relative dimension is required. Compute the ambient dimension from its
  product tangent space and regularity instead.
- `lem-weil-pbc-fibre-product-affine-spectra`: the local quotient is obtained
  from the fibre-product and local-spectrum universal properties.
- `lem-weil-pbc-closed-immersion-affine-cover-criterion`: the local graph maps
  are sections of a separated projection, so Mathlib's composition criterion
  proves they are closed immersions directly.
- `lem-weil-pbc-spec-map-stalk-localization`: stalk section identities prove
  surjectivity directly; explicit localization fractions are unnecessary.

Retained `lem-weil-pbc-affine-open-stalk-localization` for the open-immersion
stalk isomorphism recorded among its Mathlib declarations. Added the existing
`lem-weil-pbc-morphism-from-spec-local-ring` dependency for reconstruction from
a local stalk homomorphism. No module is withdrawn and no adopted source
library declaration is removed. These pruning statements concern this item's
proof dependencies, not a claim that every listed module is globally unused.

## Where the brief, the DAG or earlier work was wrong

The original DAG route is mathematically valid but longer than necessary:
constant-relative-dimension shrinking and affine tensor/localization models can
be replaced by the existing rational tangent equivalence, stalk section
identities and the universal property of a local-ring spectrum. No statement
repair is made and the unit's realized route is retained.

This is the same R9 item dispatch resumed on 2026-10-24 after the launcher paused
it to shorten the compile queue. Its sandbox already contained partial work.
The launcher refreshed the budget metadata (current recorded start
2026-10-23T16:38:37Z); the worker did not change that metadata or create `.check`.
The paused process's tool session was no longer available, so its compile was
rerun. There was no earlier R9 delivery of this item to repeat.

## Second reading by R9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
