## What changed

Proved `AlgebraicGeometry.flatCurve_derivedStructure_model` with its signature and all four
auxiliary definitions unchanged. The canonical unit kills the sole differential in a
finite-free residue model supported in degrees zero and one. Its homology identifies the
second term with the actual H1, giving finite local freeness and the stated local splitting.
The proof also establishes the canonical H0 unit, vanishing and arbitrary base change.

All added helpers are private and proved. A private proper relatively flat single-module
perfectness argument descends to a Noetherian stage, uses proper coherence and local finite
Tor dimension, then transports back by canonical base change. The existing global scheme
localizations in this module suffice for this argument. The DAG proof follows these actual
steps. No source-library file, target, existing definition or public interface changes.

## Proved and sorry left

Closed the one original hole, `AlgebraicGeometry.flatCurve_derivedStructure_model`
(node `lem-weil-pbc-flat-curve-derived-structure-model`).

Added zero holes; zero holes remain in the delivered Lean module. No statements are split
off. Existing named dependency theorems are used under the stage-3 policy. The complete
module compiled cleanly through `lcompile.py` in 35.7 seconds, with no warnings.

## No longer needed

Removed the proof import
`WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.PerfectBaseChange` and direct
proof dependency `lem-pc-rf-perfect-base-change`: its adopted declaration concerns an affine
Cech model and does not directly identify the specified derived object or canonical arrow.
The proof instead uses geometric Noetherian descent, derived proper coherence and finite
Tor dimension, followed by canonical relatively flat base change.

Removed the existential `Sheaf.AlgebraicGeometry.FlatDerivedStructureUnit` import and
`lem-sc-flat-derived-structure-unit` dependency in favour of
`flat-derived-structure-unit-properties`, which applies directly to the specified unit.

Removed the obsolete `tool_uses` entries `lem-pc-rf-perfect-base-change` and
`lem-sc-flat-derived-structure-unit`, preserving the order of all remaining approvals.

The positive-summand decomposition in the old plan is unnecessary: applying the residue
model directly to K and using the canonical unit proves the two-term splitting. No module
is withdrawn and no claim about other consumers of these dependencies is made.

The exploratory sandbox restorations and two-term public lemma were not needed and are
excluded from the delivery. Every archived module and existing node attachment remains
intact in the shared repository; there is no deletion list.

## Where the brief, the DAG or earlier work was wrong

The adopted `lem-pc-rf-perfect-base-change` declaration supplies an affine Cech statement,
not the stronger derived-object conclusion used by the old plan. An archived general
single-module perfectness theorem exists, but its restoration chain reaches quarantined
comparison modules, including a recorded build failure. The proof here supplies the needed
common-universe special case by a complete private argument from available APIs instead of
adding a duplicate public declaration or changing any archived interface.

The local finite-free residue model can be applied directly to K. Rank-one residue H0
and the actual canonical unit make its degree-zero chain component invertible on the whole
chosen open, killing the differential. This preserves the unit route and all hypotheses.

No mathematical statement or definition repair, change record, forced adaptation, new node
or new public theorem is required.

## Second reading by J6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
