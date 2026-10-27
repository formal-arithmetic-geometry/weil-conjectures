## What changed

Proved `AlgebraicGeometry.nonempty_moduleSheafExt_stalk_linearEquiv` with its original
signature, universes, hypotheses and public imports. It composes the existing
`derivedInternalHom_stalk_localization` equivalence with the ring-valued cohomology/Ext
comparison. Faithful skyscrapers and faithful evaluation supply the required local
one-point derived category in the given universe, without an additional assumption.

Added `Sheaf.Paper.RHomCohomologyExtRing`, realizing the existing node
`lem-sc-rhom-cohomology-ext-ring` with the fully proved theorem
`CategoryTheory.nonempty_rhom_cohomology_ext_ring`. The proof constructs the exact
one-point evaluation equivalence, identifies the evaluated sheaf Hom complex with
ordinary cochains using `normalizedHomGlobalCochains_comm`, and constructs linear
homology data from Mathlib's injective-resolution cocycles-to-Ext map. Evaluation
then transfers Ext to ordinary modules. All its auxiliary declarations are private
and proved; no data is obtained from a new unproved existence assertion.

Updated the two existing nodes' proof records and attached the new comparison module
to its existing node. No existing definition or statement was changed, no source-library
file was edited, and no consumer adaptation or change record is required.

Validation: both sandbox modules compile together through `lcompile.py --all`.
The comparison takes approximately 30 seconds, below the per-file limit. Checked
module import direction, unchanged original signature/public imports, and the
100-character line limit. `#print axioms` confirms that the new ring comparison uses
only `propext`, `Classical.choice` and `Quot.sound`; the item retains `sorryAx` through
the existing stalk-localization dependency. The proof works uniformly in degree zero, for zero modules,
and for the zero ring; it introduces no nonzero or positive-degree assumption.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.nonempty_moduleSheafExt_stalk_linearEquiv`
(node `lem-sc-ext-stalk-localization`). Zero holes remain in the item.

Also fully proved `CategoryTheory.nonempty_rhom_cohomology_ext_ring`
(node `lem-sc-rhom-cohomology-ext-ring`), which previously had only a Mathlib match
and no Lean attachment. Added zero holes, split off zero unfinished statements.
Neither delivered Lean module contains `sorry`.

The unchanged imported theorem
`AlgebraicGeometry.derivedInternalHom_stalk_localization`
(node `lem-sc-derived-internal-hom-stalk-localization`) still has its existing hole.
This delivery uses that declared proof dependency as the stage-3 brief requires;
it does not claim a hole-free target import closure.

## No longer needed

None. The original mathematical route and all three original proof dependencies
are used. No original import, node, module, or unit step is pruned. Added imports
are used for the comparison or its size infrastructure.

## Where the brief, the DAG or earlier work was wrong

The ring-comparison node's Mathlib match described a one-line specialization, but
Mathlib's `InjectiveResolution.extEquivCohomologyClass` ends at ordinary cohomology
classes and is not directly a linear equivalence from the evaluated sheaf-valued
`derivedInternalHom`. The new proved module supplies the evaluation, complex,
scalar-compatibility and homology bridges. This realizes the existing node rather
than introducing a new mathematical statement or bypassing the unit route.

The localization dependency needs a local derived category in the same universe as
the global one. The original item does not assume it separately. The private
faithfulness argument derives it from the existing hypotheses; neither the item
nor the dependency signature needs repair.

## Second reading by T4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
