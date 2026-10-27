## What changed

Proved `AlgebraicGeometry.LocallyRingedSpace.affinization_localization_stalk_criterion`
in `Sheaf.AlgebraicGeometry.AffinizationLocalizationStalkCriterion`, preserving its
statement and public imports. Added a proved private ring-theoretic helper
`localization_stages_bijective`. Added the private proof import
`Mathlib.Geometry.RingedSpace.OpenImmersion` for the sheafed-space stalk criterion.
Updated the node proof, proof dependencies, proof origin and declaration proof
explanation to describe the implemented route.

The actual affinization stalk map is used throughout: the germ square identifies its
restriction to each stage, and localization uniqueness identifies the stage composite
with the given isomorphism. Injectivity needs only a stage representative of one
numerator; surjectivity needs one nonempty stage. The factorization uses the prescribed
inverse-image sheaf and the adjunction unit, then lifts the sheafed-space isomorphism.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.LocallyRingedSpace.affinization_localization_stalk_criterion`
(node `lem-a1-affinization-localization-stalk-criterion`).
Added 0 holes; split off 0 statements. No `sorry` remains in the delivery.
The private helper is fully proved. Remote single-file compilation passed (16.7 s);
`#print axioms` reports only `propext`, `Classical.choice`, and `Quot.sound`.

## No longer needed

Removed private import
`WeilConjectures.AlgebraicGeometry.FilteredColimitLocalizationAtPrime`.
The proof does not use node `lem-weil-pbc-filtered-colimit-localization-at-prime`
or its module. Also removed redundant private imports
`Mathlib.Algebra.Category.Ring.FilteredColimits` and `Mathlib.Topology.Sheaves.Stalks`;
the retained inverse-image stalk module already publicly imports these APIs.
Instead of constructing a colimit of stage localizations, the proof lifts a
single numerator from the original filtered colimit and uses localization uniqueness.
This prunes that dependency from this item's proof; no claim is made that other
consumers no longer need it. All other declared proof dependencies remain used.
Removed the corresponding obsolete top-level `tool_uses` entry
`lem-weil-pbc-filtered-colimit-localization-at-prime`. No modules are withdrawn.

## Where the brief, the DAG or earlier work was wrong

No statement error. The original DAG's localized-colimit construction was sufficient
but unnecessary: the given stage isomorphisms prove surjectivity immediately and
injectivity follows by lifting a single numerator. The unit's route is preserved.
The Stacks source read was `more-groupoids.tex`, Tag 0API,
`lemma-sits-in-functions`, particularly the sentence beginning “For any e”.

## Second reading by E5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
