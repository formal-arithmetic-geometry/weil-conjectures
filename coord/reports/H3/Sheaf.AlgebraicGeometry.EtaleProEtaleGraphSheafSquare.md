## What changed

Replaced the proof of `AlgebraicGeometry.ProEtale.etale_proEtale_graph_sheaf_square`
with an assembly proof. The exactness assertions use the source library's
`SmallSite.preservesFiniteLimits_op_lan_overMap_of_isGrothendieckAbelian` and the
actual sum adjunctions. The comparison uniqueness assertion uses injectivity of
`conjugateIsoEquiv`, and its generator equation is obtained by evaluating
`Adjunction.unit_leftAdjointUniq_hom_app` for the two composite adjunctions.

Two new modules isolate the remaining geometric work:
`Sheaf.AlgebraicGeometry.ProEtaleCompactifiedGraphExistence` constructs and uniquely
characterizes the graph map for a specified restriction adjunction;
`Sheaf.AlgebraicGeometry.CompactifiedGraphComparisonGenerators` proves compatibility
of a given graph map with a generator-preserving site comparison. The main proof
uses existence, uniqueness, equality substitution, and this compatibility statement
to obtain its original graph characterization and square.

The three files passed the server single-file compilation in import order:
comparison-generators 17.6 s, graph-existence 3.4 s, and the item 32.6 s.
The delivery preflight also checks the final import cleanup and all declaration axioms.

Every existing declaration signature, definition body, docstring, and public import
is unchanged. Only the item's proof, its private imports, and its node's proof
metadata change. No other existing module or node is adapted.

The new statements were checked on the empty source and empty test schemes, the
zero ring, identity compactifications, proper etale maps, and the non-monomorphic
fold map. The first and second fibre-product equations uniquely determine the graph;
the arbitrary specified adjunction is handled by its unit-preserving comparison.
The comparison lemma assumes a given graph map and its generator condition and does
not assert existence, uniqueness, or exactness.

## Proved and sorry left

Original textual holes: 1. The hole in
`AlgebraicGeometry.ProEtale.etale_proEtale_graph_sheaf_square`
(node `lem-sp-et-proet-graph-sheaf-square`) is closed by a proof from two strictly
smaller graph statements. The item module has zero remaining textual holes.
The exactness, uniqueness of the normalized sum comparison, and raw generator
clauses are proved directly from existing declarations, without either new hole.

Two named holes are added:

- `AlgebraicGeometry.ProEtale.compactified_graph_existsUnique`, node
  `lem-sp-proetale-compactified-graph-existence`.
- `AlgebraicGeometry.ProEtale.compactified_graph_comparison_of_generators`, node
  `lem-sp-compactified-graph-comparison-generators`.

This is a decomposition of the original theorem, not a complete proof free of
`sorry`. Textual accounting is one hole closed and two added, net minus one.
The existing graph-map definition still chooses only an object uniquely determined
by its graph values; no definition contains a hole or chooses an arbitrary witness
of a mere existence statement.

## No longer needed

Removed these private imports from the item:

- `Mathlib.CategoryTheory.Adjunction.Basic` (already supplied by Mates/Unique).
- `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`.
- `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`
  (the public etale imports supply its declarations).
- `Sheaf.Paper.ComparisonPullbackExact`.
- `Sheaf.Paper.LocalizeRingedSiteMorphismGeneral`.
- `Sheaf.AlgebraicGeometry.OpenComparisonUnitNormalization`.
- `Sheaf.AlgebraicGeometry.ComparisonPullbackOpenUnit`.
- `Sheaf.AlgebraicGeometry.ProEtaleIntrinsicOpenUnit`.
- `Sheaf.AlgebraicGeometry.EtaleAmbientAdjointLocality`.
- `WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf`.
- `WeilConjectures.SixFunctors.OpenClosed.Complex`.

The new graph nodes retain the sheafification, graph-evaluation, localization,
and open-unit dependencies needed for their geometric arguments. Their unproved
statements do not import modules solely for a future proof. Existing public imports
stay to preserve the item's public interface; no claim is made that removing a direct
import makes every listed module globally unreachable.

`lem-sf-comparison-pullback-exact`, `lem-pur-site-restriction-module-adjunction-exact`,
`lem-amb-etale-adjoint-locality`, and
`lem-weil-pbc-etale-inverse-image-restriction` are unnecessary for the parent's new
assembly proof: the fixed-coefficient sum exactness and actual adjunctions already
exist directly. All other old direct proof dependencies are either still used in
the assembly or assigned to the appropriate new graph node. The parent's former
`tool_uses` approvals are removed from that direct proof route; the new comparison
node explicitly records the generic open-unit tools it still needs. No existing
module is withdrawn, and no global pruning of a module is claimed.

## Where the brief, the DAG or earlier work was wrong

The generic ringed-slice and derived ambient-adjoint lemmas in the old plan are
unnecessary for the main exactness and unit-normalization clauses: the source
library already proves the arbitrary-morphism sum-over-lifts Kan extension result.
The semilinear graph-evaluation statement uses ringed-module categories and chosen
left adjoints, so its constant-system specialization does not immediately supply
the fixed-scalar graph predicate or its uniqueness. The first new statement records
that remaining graph construction/transport and uniqueness work explicitly.
The second records the actual canonical etale graph formula and mate calculation,
not an assumption that an unspecified graph map already satisfies the square.

## New nodes

`lem-sp-proetale-compactified-graph-existence` belongs to the existing smooth-tower
unit and isolates the parent's graph construction and uniqueness step. Its new
module contains one public theorem with a whole-proof `sorry`, source citation,
and complete natural-language proof.

`lem-sp-compactified-graph-comparison-generators` belongs to the same unit and
isolates the graph comparison calculation for an arbitrary specified adjunction
and generator-preserving sigma. Its new module likewise contains one public
whole-proof hole with source and proof in words. The two new statements do not
import the item, so no import or DAG dependency cycle is introduced.

## Second reading by H3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
