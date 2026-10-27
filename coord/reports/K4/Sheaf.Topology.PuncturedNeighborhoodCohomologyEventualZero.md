## What changed

Replaced the proof of `TopCat.puncturedNeighborhood_cohomology_eventual_zero` with
application of `TopCat.Sheaf.spectralLimit_cohomology_eventual_zero` to the explicit
punctured-neighborhood inverse system. Its signature and original docstring are unchanged.
The proof transports the zero-image equation through the coefficient comparison, applies
general continuity, and cancels the stage comparison to obtain the required restriction.
Two proved private lemmas perform these square calculations for arbitrary abelian groups,
keeping the cohomology definitions folded; a third proves normalization of canonical pullback, and a fourth specializes the
general continuity theorem to those canonical families. These private helpers are all proved.

Added `Sheaf.Topology.PuncturedNeighborhoodSpectralSystem`: real constructions of the
reverse-inclusion index, punctured stages, transition inclusions and projections; complete
proofs of nonemptiness, directedness, spectral stages, spectral transitions and the
pointwise/topological limit description. The crucial separation argument covers the
compact closed set Z by finitely many compact opens avoiding the closure of an excluded
point. No data is selected from an unproved existence theorem.

Added `Sheaf.Topology.PuncturedNeighborhoodCoefficientPresentation`, separating the
restriction coefficient system and its cohomology map identifications from continuity.
The coefficient fields are bundled in `TopCat.PuncturedNeighborhoodCoefficients` to
avoid repeated expansion during kernel checking. The named existence theorem is only
eliminated inside the assigned proposition proof; no definition chooses its data.
It asserts neither generation of classes nor eventual vanishing, and needs no compactness
of the complement. This is step 4 and the comparison part of step 5 of the original plan.
Updated the item's proof dependencies and added matching nodes for the new modules.

## Proved and sorry left

Closed the original hole `TopCat.puncturedNeighborhood_cohomology_eventual_zero`
(node `lem-weil-pbc-punctured-neighborhood-cohomology-eventual-zero`) by a complete
proof from named dependencies. Added one hole:
`TopCat.puncturedNeighborhood_coefficient_presentation`
(node `lem-weil-pbc-punctured-neighborhood-coefficient-presentation`).
This is a decomposition: one original hole closed, one strictly different coefficient/map
comparison obligation added, net zero holes. The original module has zero remaining holes.
The existing general spectral-limit eventual-zero theorem remains a dependency and has
not been modified.

The spectral-system module has zero holes. Its six public theorem proofs establish
`puncturedNeighborhoodIndex_nonempty`, `puncturedNeighborhoodIndex_directed`,
`puncturedNeighborhoodSpace_spectral`, `puncturedNeighborhoodTransition_spectral`,
`puncturedNeighborhood_topologicalLimit`, and `puncturedGeneralizations_spectral`; `mem_all_neighborhoods` is a proved private
helper. All are in namespace `TopCat`.

## No longer needed

No original imports or modules are withdrawn. The original public imports remain required
by its statement. The spectral directed-limit import moved from the item to the new spectral-system
module, where the proved spectrality lemma uses it. The proof uses the general eventual-zero half. The class-lifting half and parent
colimit module are not imported.

The original direct proof dependencies
`def-weil-pbc-topological-inverse-image`, `def-weil-pbc-category-colimit`,
`lem-weil-pbc-cohomology-over-object-localization-addEquiv`, and
`lem-weil-pbc-site-cohomology-pullback-composite` move into the coefficient-presentation
node: they remain mathematically needed there and are not claimed pruned. The spectral-space
and diagram definitions move through the concrete spectral-system node. No mathematical
node is pruned by this delivery; no old top-level tool approval is changed.

## Where the brief, the DAG or earlier work was wrong

The plan's general continuity theorem does not directly accept the ambient
object-cohomology diagram. Its hypotheses require actual sheaves on the subspaces,
a compatible inverse-image diagram, and cohomology comparisons respecting the specified
canonical maps. These comparisons are now explicit in the coefficient-presentation
statement instead of being hidden in an application.

Read Stacks Cohomology `lemma-colimit` (0A37) and
`lemma-cohomology-of-neighbourhoods-of-closed` (0A3D), and Topology
`lemma-make-spectral-space` (0A31), `lemma-spectral-sub` (0902), and
`lemma-make-spectral-space-minus` (0AP0). The coefficient lemma is the restriction-system
setup in that argument, not a second copy of the assigned eventual-vanishing obligation.
For empty Z the index contains the empty open; for Z=T every puncture is empty; for
empty T the index still contains the whole space. The topological proofs handle all
three without a nonempty-space assumption, and the proposed coefficient construction
uses the zero sheaf cohomology on empty subspaces. Degree zero uses the ordinary unit
and restriction identities.

No unit statement or route changed. No existing public declaration signature, definition,
instance, or public import changed, and no consumer needs adaptation. The only direct
existing consumer is `Sheaf.Topology.PuncturedNeighborhoodCohomologyColimit`, whose call
retains exactly the same type. The blueprint-ancestor helper follows `created.item`
through module names and returns None for this previously split node; the new nodes
preserve the explicit existing blueprint ancestor `lemma-weil-pbc-smooth-curve-artin-schreier`
and add the assigned node to its existing via chain.

## New nodes

`lem-weil-pbc-punctured-neighborhood-spectral-system` records the concrete index, spaces,
transitions and projections, with fully proved topological-system properties. Searches
found Mathlib's spectral open-subspace theorem and compactness API, which the proof uses,
but no existing punctured-neighborhood limit identification.

`lem-weil-pbc-punctured-neighborhood-coefficient-presentation` states the remaining
restriction-system presentation and the exact stage/projection map identities. It has
one public named sorry theorem with a source and complete natural-language argument.
Searches found sheaf-level open-embedding pullback isomorphisms but no cohomology-map
comparison. Change record: `coord/changes/K4-punctured-neighborhood-system.md`.

Validation: the final three-module server compile passed with no errors or warnings;
the assigned module compiled in 54.1 seconds under the fixed 60-second limit.

## Second reading by K4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
