## What changed

Filled `AlgebraicGeometry.henselian_pair_h0` in
`Sheaf.Paper.HenselianPairH0`, preserving its statement and both helper definitions.
The set-valued proof identifies the closed-fibre image with the inverse image of
V(J), applies the existing Stein connectedness theorem on every finite cover,
and obtains the Zariski hypotheses of Gabber's criterion through the existing
universe-compatible closed-immersion restriction theorem. The terminal-object
transport is an isomorphism. Naturality follows directly from naturality of the
adjunction unit and of the inverse-image sheaf morphism. The abelian and module
conjuncts use the existing `DegreeZero` specializations on the canonical pullback
square. Updated the item's DAG proof and proof dependencies to this route.
All added imports are private proof imports; no public interface changed.
The final single-file compile passed without warnings in 12.1 seconds through
`lcompile.py`. The revised DAG was checked for dependency cycles; none was found.

## Proved and sorry left

Closed the one original hole, `AlgebraicGeometry.henselian_pair_h0`
(node `sk-thm-pbc-henselian-h0`). No holes added, no statements split off,
and no `sorry` remains in the delivered module. This is a proof from existing
library declarations, rather than a decomposition into new obligations.

## No longer needed

Removed direct proof imports:

- `Sheaf.Paper.ZariskiH0ProperHenselianPair`
- `WeilConjectures.AlgebraicGeometry.EtaleSetInverseImageCompositionUnits`
- `WeilConjectures.AlgebraicGeometry.EtaleInverseImageAlgebraicStructures`
- `WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact`

The corresponding direct proof dependencies are no longer needed:
`lem-weil-pbc-zariski-h0-proper-henselian-pair`,
`lem-weil-pbc-sets-etale-inverse-image-composition-units`,
`lem-weil-pbc-etale-inverse-image-algebraic-structures`, and
`prop-weil-pbc-inverse-image-modules-exact`.
Naturality is proved directly; existing coefficient comparisons replace the
structured inverse-image reconstruction. The Zariski argument still follows the
unit's integral Stein connectedness and spectral restriction route, through
`thm-weil-pbc-stein-inputs` and
`lem-weil-pbc-zariski-closed-immersion-connected-restriction`.
These are direct dependency removals only: the source library retains all its
declarations, and other imports may still reach some of these modules.
No module is withdrawn and no source-library declaration is removed.

## Where the brief, the DAG or earlier work was wrong

The DAG's Zariski comparison dependency is stated for sheaves in `Type u`, whereas
Gabber's criterion here requires `Type (u+1)`. Its direct application does not fit.
The existing connectedness theorem and the universe-compatible Zariski
closed-immersion restriction theorem supply exactly the needed hypothesis,
without changing any definition or statement. The existing source-library
`DegreeZero` module already provides both coefficient-valued conclusions, so
reconstructing them through the two large inverse-image packages is unnecessary.
There are no new nodes or definition repairs.

## Second reading by K7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
