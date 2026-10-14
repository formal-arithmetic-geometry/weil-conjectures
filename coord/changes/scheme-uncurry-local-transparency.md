# CategoryTheory.homComplexFunctor (local transparency only)

## Reason

The returned delivery took 119 seconds in the global build and exceeded the
single-file limit. The expensive definition is the chosen `homComplexFunctor`
from `homComplex_exists`. Rewrites over its large specification repeatedly reduce
it. Use a local irreducible attribute and a proved explicit component equation
instead. All shared definitions, signatures, visibility and imports stay identical.
The return also requested importer adaptation or an unchanged public interface;
the latter is used, and the unchanged direct importer compiles in 11.5 seconds.

## Old

No local transparency commands in the original module. `homComplexFunctor` retains
its existing semireducible definition globally.

## New

```lean
attribute [local irreducible] homComplexFunctor
-- Abstract functor and tensor-Hom lemmas.
attribute [local semireducible] homComplexFunctor
-- Prove the explicit component formula by rfl.
attribute [local irreducible] homComplexFunctor
```

These commands apply only in the delivered module. The component definition itself
is unchanged; its formula theorem is private and fully proved. No target needs a
statement re-review: no definition or statement it uses changes meaning.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.SchemeTensorHomUncurrySummandNaturality | M3 | Local transparency and private proof helpers; unchanged public theorem type. |
| Sheaf.AlgebraicGeometry.SchemeOrdinaryEvaluationTripleComponent | unclaimed | Direct importer; compiled unchanged against the delivered module in 11.5 s. |

No importer is edited. Local attributes do not propagate to other modules. The
only shared user-facing declaration remains exactly the original theorem.

## Status

landed 20261014T075200-L-3630614 2026-10-14 (merge of deliver/M3/Sheaf.AlgebraicGeometry.SchemeTensorHomUncurrySummandNaturality)
