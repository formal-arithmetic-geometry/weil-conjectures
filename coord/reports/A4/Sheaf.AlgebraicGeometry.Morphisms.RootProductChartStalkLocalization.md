## What changed

The existing `rootProductChart_stalk_localization` signature is unchanged. Its complete
Lean proof now lifts the two points using Mathlib, applies a compatible product-chart
stalk presentation, constructs the flat local map using the etale first projection,
and proves the ideal identity by the proved source-library unramified stalk lemma and
ideal-map composition. The private `maximalIdeal_stalkMap_comp` helper is proved.

Added `RootProductChartCore`: its theorem `rootProductChart_stalk_localization_core`
is proved. Mathlib's finite-product prime decomposition selects a factor; the spectrum
map of evaluation is an open immersion. Composing it with the inverse chart gives the
factor inclusion, its stalk isomorphism, and the structural compatibility calculation.
Its private `stalkMap_comp_hom` helper is proved.

Added `RootFactorStalkLocalization`: the remaining statement concerns just one
concrete polynomial quotient and its base localization. It has no etale chart,
fibre-product point construction, flat local map, or extended base ideal identity.
The new nodes and the original node's proof route match these Lean proofs.
Only proof imports were added to the existing module; its public imports are unchanged.
The unit's trait-chart route is retained.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Scheme.rootProductChart_stalk_localization`.
Proved the new
`AlgebraicGeometry.Scheme.rootProductChart_stalk_localization_core`
(node `lem-sbc-root-product-chart-stalk-localization-core`).

Added one hole:
`AlgebraicGeometry.Scheme.rootFactor_stalk_localization`
(node `lem-sbc-root-factor-stalk-localization`). Its module includes the full
localization/quotient/transitivity proof in words. This is a decomposition:
one original hole closed and one strictly smaller algebraic hole added,
so the net hole change is zero. No other delivery declaration contains `sorry`.

Edge cases checked: a point in the empty product is impossible, and
Mathlib's sigma-to-product surjectivity includes this case without choosing an
inhabitant of `Fin 0`. Positive exponents ensure monicity. The base stalk is
nontrivial because it is at a spectrum point. Neither a regularity nor an
invertibility assumption on f or the exponents is needed for the remaining
localization assertion. Nilpotent f and exponent one are allowed.

## No longer needed

None. The original module had no proof-dependency imports or proof-dependency nodes
to prune. Its public imports all remain necessary for its unchanged statement.
The proof uses no section, trait, DVR, normalization or generic-factor theorem.
The downstream private `root_local` theorem was inspected but is not imported;
importing its module would create a cycle.

## Where the brief, the DAG or earlier work was wrong

The original node contained the whole geometric/algebraic argument as one step with
no proof dependencies. Much of its geometry is already supplied by Mathlib and the
source library: point lifting, finite-product factor selection, open-immersion stalk
isomorphisms, etale pullback flatness, and unramified maximal-ideal extension.
The actual missing interface is localization of the single polynomial quotient
at a prime over the chosen base point. The remaining statement records exactly this
part, and the rest is proved in Lean.

The sources were checked at Stacks Tags 0EYH and 0EYI. The localization argument
is the algebraic unpacking of their affine root factors, without imposing their
additional divisor regularity or tame-invertibility hypotheses.

## New nodes

`lem-sbc-root-product-chart-stalk-localization-core`, in
`dag/nodes/sec-smooth-base-change/`, records the proved product-factor presentation
and its structural compatibility, from the single-factor lemma and Mathlib.

`lem-sbc-root-factor-stalk-localization`, in the same directory, records the one
remaining base-localization statement for a single monic root polynomial.
No change records or forced adaptations are needed: no existing signature changed.

## Second reading by A4

1. **Visible declarations and statements.** Compared the delivered item module with the repository version. The existing `rootProductChart_stalk_localization` signature is byte-for-byte unchanged; only proof-only imports, a private helper, and its proof body were added. The two additional modules are new declarations recorded by new DAG nodes, so no existing declaration was altered.

2. **Proof validity and axioms.** Compiled all three sandbox modules with `lcompile.py --all`; they compile without errors. Searched delivered Lean files for forbidden `axiom`, `unsafe`, `opaque`, `extern`, and `implemented_by`; none occur. The only remaining `sorry` is the named `rootFactor_stalk_localization` split-off theorem, with its source and proof plan documented above and its matching node. The item theorem and core theorem are fully proved.

3. **Statement strength and decomposition.** Checked the new core theorem against its use in the item: it supplies exactly the finite-product factor, maximal localization, stalk equivalence, and structural compatibility required by the item. The root-factor theorem is a strictly smaller single-factor localization statement and removes the product-chart, etale, flatness, and extended-ideal obligations. Edge cases (empty product, exponent one, nilpotent coefficient) are addressed in the report; no hypothesis was added to the existing target.

4. **Shortest route and imports.** The proofs use Mathlib's finite-product prime decomposition, open-immersion stalk isomorphism, localization constructions, and the source-library unramified maximal-ideal lemma. The added imports are proof-only imports in the existing module; public imports remain unchanged. No old proof-dependency import or node is unused, so the `No longer needed` list is empty.

5. **DAG and unit route.** The existing node's proof route was updated to name the core theorem and the source-library lemmas actually used. The two new nodes contain matching declarations, sources, proof steps, and `proof_deps`. The unit's trait-chart route remains realized; the core theorem is the product-factor presentation step and the remaining sorry is explicitly recorded as a decomposition.

Changed during second reading: added this required review section only; no Lean code, node, or statement changes were needed.
