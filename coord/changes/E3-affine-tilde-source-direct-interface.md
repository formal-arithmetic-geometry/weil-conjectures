# AlgebraicGeometry.exists_affineTildeTensorSourceComparison

## Reason

The current source comparison and its complete proof have already been adopted
upstream. W6 restored this Sheaf interface on 2026-10-21, after the route note
was written. There are no remaining proof holes or unresolved definition repairs
in the current item. Retain that restoration and simplify its public imports:
the core-final Sheaf wrapper contributes no declarations, and its entire public
interface is supplied by the adopted comparison together with the normalization
module defining the legacy `affineTildeFunctor` abbreviation and its instance.

This is import pruning, not a new proof or a second quarantine restoration.
No source-library file, theorem signature, definition, archive or target changes.
The source comparison and affine-core argument remain used and fully proved.

## Old

```lean
public import Sheaf.Algebra.Homology.AffineTildeTensorSourceComparisonCoreFinal
public import WeilConjectures.Algebra.Homology.AffineTildeTensorSourceComparison
```

## New

```lean
public import Sheaf.Algebra.Homology.AffineTildePushforwardCohomologyNormalization
public import WeilConjectures.Algebra.Homology.AffineTildeTensorSourceComparison
```

The normalization import is public because consumers use `affineTildeFunctor`
in their statements. The adopted comparison transitively publicly imports the
adopted core-final theorem and `DerivedBaseChangeUnitCompatibility`.
Comparing recursive public-import closures, the only removed module is the
declaration-free Sheaf core-final wrapper. All declarations and instances remain
publicly available. Its current holder K7's module is not edited or withdrawn.

## Users

The direct `tools/downstream.py` query reports zero live direct importers and
zero live modules mentioning the comparison through this interface. Searching
the quarantine also finds these four direct importers; none has a claim file
in the current shared snapshot. They retain the old associated-sheaf spelling.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Algebra.Homology.AffineTildeDerivedTensorMate | unclaimed | The theorem call and legacy tilde abbreviation retain exactly their types. |
| Sheaf.Algebra.Homology.AffineTildeTensorOrdinaryExchange | unclaimed | Identical declarations and instances remain public. |
| Sheaf.Algebra.Homology.AffineTildeTensorOrdinaryExchangePreNormalization | unclaimed | Identical declarations and instances remain public. |
| Sheaf.Algebra.Homology.AffineTildeTensorOrdinaryExchangePreNormalizationChain | unclaimed | Identical declarations and instances remain public. |

No consumer adaptation is needed. The item's DAG node keeps its attachment,
statement, mathematical proof and dependencies. The unit route is unchanged.

Validation: the changed interface compiles in 1.8 seconds. A scratch consumer
imports only this interface, repeats the entire archived theorem statement
with `affineTildeFunctor`, and repeats its archived proof from the core theorem.
Only local instance names and the explicit sheaf universe in the archived
abelian-instance elaboration were adjusted. It compiles in 31.7 seconds.
`#print axioms` for that consumer, the re-exported source theorem and the
core-final theorem gives only `propext`, `Classical.choice`, `Quot.sound`.
The replacement import passes the import-direction check. The scratch consumer
is retained outside `lean/` in the sandbox and is not a delivered library module.

## Status

landed 20261021T193049-L-846111 2026-10-21 (merge of deliver/E3/Sheaf.Algebra.Homology.AffineTildeTensorSourceComparison)
