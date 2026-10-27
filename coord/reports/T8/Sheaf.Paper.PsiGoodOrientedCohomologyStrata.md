## What changed

Restored Sheaf.Paper.PsiGoodOrientedCohomologyStrata from the quarantine path recorded in
coord/rework.tsv. Replaced the retired LocallyClosedStratification alias by its defining
Scheme.Stratification and its withdrawn public import by the upstream canonical module.
This repairs the unknown-constant errors in the recorded global build while preserving
the elaborated conclusion, including both explicit constructible-strata clauses.
Updated the attached node's Lean signature to the current spelling.

Proved the existing upContinuous theorem from Mathlib's equivalence-of-sites instance,
using a private import of Mathlib.CategoryTheory.Sites.Equivalence. The underlying
AsSmall equivalence and induced topology are the original ones.

Change record: coord/changes/T8-psi-good-strata-restoration.md.

## Proved and sorry left

The archived item had four holes. Closed one:
AlgebraicGeometry.OrientedNearbyCycles.PsiGoodStrata.upContinuous.
No holes added and no statements split off. Three existing holes remain, each attached
to lem-trf-psi-good-oriented-cohomology-strata and retaining its original proof docstring:

- AlgebraicGeometry.OrientedNearbyCycles.PsiGoodStrata.restrictSite_properties
- AlgebraicGeometry.OrientedNearbyCycles.PsiGoodStrata.vanishing_finiteLimits
- AlgebraicGeometry.OrientedNearbyCycles.PsiGoodStrata.exists_constructible_cohomology_strata

This is the assigned quarantine/build repair with one additional helper proof, not a
completed proof of the main cohomological constructibility theorem. No arbitrary data,
new definitions, or new axioms were introduced. Single-file lcompile validation passes.

## No longer needed

The withdrawn Sheaf.AlgebraicGeometry.LocallyClosedStratification import is replaced
by WeilConjectures.AlgebraicGeometry.LocallyClosedStratification. No mathematical node
or module is pruned; all archived proof-dependency imports and the unit route remain.
No new proof is based on the three existing postponed properties.

## Where the brief, the DAG or earlier work was wrong

The item is absent from lean/ because it was quarantined, not because it was withdrawn.
The archive's conclusion and node Lean record still spelled the alias retired by F9.
The old alias was definitionally Scheme.Stratification, so substituting the current
FiniteLocallyClosedStratification type would be an unnecessary interface change.
The explicit constructibility clauses are kept even though Stratification also stores
those properties. The case of an empty scheme and the finite zero coefficient ring
are unaffected by the name port and the unconditional site-equivalence proof.

The live downstream tool reports zero users for this absent module. The quarantine
scan identifies NearbyCycleSheafFiniteness as a preserved unfinished parent. It does
not name the retired alias or apply the restored theorem yet, and needs no adaptation.

## Second reading by T8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
