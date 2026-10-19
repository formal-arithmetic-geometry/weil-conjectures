## What changed

Proved `AlgebraicGeometry.ProEtale.etaleOrigin_restriction_to_proetale_base_change`
in `Sheaf.Paper.FullCDClassRestriction` without changing its statement or the existing
`etaleOriginRestrictionWitnessIso` definition. Mathlib's `IsPullback.of_hasPullback`
and the weakly-etale pullback instance prove the first two clauses. Destructing the
essential-image hypothesis gives an etale witness; the inverse of the existing
constructed restriction isomorphism supplies its essential-image witness after base
change. The same construction proves the arbitrary-witness clause. Naturality follows
from `(comparisonCoefficientPullbackIso _ _).inv.naturality`, simplifying the identity
witness and unfolding only the inverse-image wrappers and etale topology abbreviation.

Followed all three existing DAG proof steps; no route change or new nodes. Removed four
unused imports, recorded in `coord/changes/S9-fullcd-class-restriction-imports.md`.

The complete proof compiled cleanly through `lcompile.py` in 5.1 seconds before pruning
and 5.8 seconds after pruning. The source-only import-pruning check passes. Delivery
validation recompiles the pruned module and probes the axioms of both declarations.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.ProEtale.etaleOrigin_restriction_to_proetale_base_change`
(node `lem-sf-fullcd-class-restriction`).

No `sorry` remains in the item. No holes added and no statements split off.
The witness definition already had real data and is unchanged.

## No longer needed

Removed imports:

- `Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory`: no derived-category statement is used.
- `Sheaf.CategoryTheory.RingedSiteModules`: the theorem uses fixed-coefficient
  `ModuleCat`-valued sheaves, without the general ringed-site abbreviation.
- `WeilConjectures.AlgebraicGeometry.EtaleSheaves`: no locally constant,
  constructible, or torsion-sheaf predicates are used.
- `Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence`: the canonical unprefixed
  comparison is already public in `ComparisonPullbackCoherence`; no coherence theorem
  for identities, composites, or chosen squares is needed for this restriction proof.

No declared proof dependency is discarded: the comparison-pullback node remains used
through the same canonical isomorphism already present in the witness definition.
There are no new modules or withdrawn nodes. The unit route is preserved.

## Where the brief, the DAG or earlier work was wrong

No mathematical defect found. The original plan gives the proof directly from existing
constructions. Lean's naturality expression uses inverse-image abbreviations whose
etale topology arguments need explicit unfolding for the final simplification.
The first search found no shorter theorem covering all five clauses. Loogle identified
`Functor.essImage`; direct use of its existential definition suffices. Local Mathlib and
library searches confirmed the pullback instances and comparison isomorphism.

## Second reading by S9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
