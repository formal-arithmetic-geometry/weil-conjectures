# CategoryTheory.homComplexFunctor (local proof transparency)

## Reason

The proof exposes the Hom differential using its projection specification and
then keeps the chosen bifunctor abstract during nested localized evaluations.
The delivery checker conservatively classifies this command as an interface
change. This is a local attribute: it affects elaboration in this module only,
not importers, declaration signatures or mathematical meanings.

## Old

No local irreducibility attribute for `homComplexFunctor` in this module.
The imported definition and its signature are unchanged.

## New

```lean
attribute [local irreducible] homComplexFunctor
```

The imported definition and its signature remain unchanged. No global
attribute, public definition or theorem statement is changed.

## Users

`tools/downstream.py` with `--uses homComplexFunctor` lists the six downstream
textual users below. The direct importer is also listed. Since the attribute
is local, each module retains exactly its previous elaboration environment;
none requires adaptation and no target meaning is changed.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Algebra.Homology.HomComplexHypercohomology | unclaimed | No effect: the attribute is local to this file. |
| Sheaf.Algebra.Homology.HomTensorTotal | unclaimed | No effect: the attribute is local to this file. |
| Sheaf.AlgebraicGeometry.CanonicalTensorHomUncurryChainNaturality | unclaimed | No effect: the attribute is local to this file. |
| Sheaf.AlgebraicGeometry.ExactSourceEvaluationLocalComparisons | unclaimed | No effect: the attribute is local to this file. |
| Sheaf.AlgebraicGeometry.ExactSourceEvaluationOpenModels | P4 | No effect: the attribute is local to this file. |
| Sheaf.AlgebraicGeometry.StrictlyPerfectEvaluationComparisons | unclaimed | No effect: the attribute is local to this file. |
| Sheaf.Algebra.Homology.HomTensorDifferentialSummand | unclaimed | No effect: the attribute is local to this file. |

## Status

landed 20261013T143549-L-561851 2026-10-13 (merge of deliver/N2/Sheaf.Algebra.Homology.HomTensorDifferentialSummandPure)
