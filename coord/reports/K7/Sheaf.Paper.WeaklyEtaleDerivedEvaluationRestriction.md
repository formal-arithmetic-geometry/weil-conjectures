## What changed

Proved `AlgebraicGeometry.ProEtale.CondensedRing.weaklyEtale_derived_evaluation_restriction_iff`
with its original signature. Only the assigned Lean module changes. Added private proof imports
and proved private helpers for the exact module adjunction, canonical section comparisons,
K-injective representatives and composition. Updated the existing node's proof, proof dependencies
and proof origin to describe the direct internal-module argument.

The adopted abelian-sheaf weakly-etale extension has an exact left adjoint. Its projection formula
follows from the existing internal-Hom comparison theorem. Linearizing this adjunction and
changing scalars along the coefficient isomorphism proves preservation of K-injective complexes
for the internal-module inverse image. The specified localization restriction is invertible on
sections and therefore on K-injective representatives. Adjunction unit coherence identifies the
specified composite restriction, and the derived composition formula permits cancellation.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.ProEtale.CondensedRing.weaklyEtale_derived_evaluation_restriction_iff`
(node `lem-sfb-weakly-etale-derived-evaluation-restriction`).

No holes remain in the assigned module. No holes were added or split off. Every private helper
is proved. The original public statement and public imports are unchanged.

## No longer needed

The following declared proof dependencies are not used by this proof:

- `lem-weil-proetale-weakly-etale-localization`
  (`Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization`): the adopted source-library
  localization restriction and germ comparison already give the needed canonical map.
- `lem-sfb-internal-module-operations-transport`
  (`Sheaf.AlgebraicGeometry.InternalModuleOperationsTransport`): the argument works directly
  with internal modules, linearizing the exact adjunction by the projection formula.
- `lem-sbc-ringed-topos-sheaf-slice-derived-comparison`
  (`Sheaf.Paper.SheafSliceDerivedComparison`): the K-injective representative calculation
  derives the localization comparison directly.
- `lem-weil-pbc-ring-sheaves-grothendieck`
  (`Sheaf.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses`): no section-ring module
  category is introduced; the existing internal-module instances supply the derived categories.

These are removals from this node's planned dependencies, not withdrawals of their modules.
Other consumers may still need them. No adopted source-library declarations are removed.
No original Lean imports were removed: the two public statement imports are retained.
All six added private imports provide declarations used by the proof.

## Where the brief, the DAG or earlier work was wrong

The original proof plan is mathematically valid but uses more general transport machinery than
needed. The adopted source library already supplies exact weakly-etale extension on abelian
sheaves, internal-Hom preservation and the normalized germ comparison. Their module-object
linearization avoids the section-ring and ringed-slice comparison obligations. No statement,
definition, coefficient convention or unit route was changed. Empty schemes and unbounded
complexes require no extra assumptions.

## Second reading by K7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
