# AlgebraicGeometry.Etale.scalarSupportTriangle_mate_identification

## Reason

Stage-3 preflight requests a change record for the local transparency attributes
used by the new proof. Keeping the chosen derived functors and adjoints abstract
prevents diagram elaboration from expanding their localization and resolution data.
The complete file compiles cleanly through `lcompile.py` in 10.4 seconds.
Every existing public signature, definition body and public import is unchanged.
No target meaning or statement changes, and no consumer needs adaptation.

## Old

The original file has no local transparency attributes. The existing definition
ends immediately before the theorem docstring:

```lean
      (scalarExtension φ P).map
        ((Adjunction.ofIsLeftAdjoint (R(lowerStar (ModuleCat.{u + 1} A) i))).counit.app K))
```

## New

The same definition body is retained verbatim. The following commands precede
five proved private helpers and the original public theorem:

```lean
-- Abstract the chosen derived functors during diagram elaboration.
attribute [local irreducible] Functor.leftAdjoint Functor.rightAdjoint
  Functor.leftDerivedFunctor Functor.mapDerivedCategory
  upperStar lowerStar
```

The attributes are local to this file's section. They change proof elaboration only;
none is exported and no definition is changed. The five private helpers are complete
proofs, and the original theorem is proved without changing its type.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.SupportedTriangleMateIdentification | B9 | Local proof elaboration only; one hole closed. |
| Sheaf.Paper.FiniteCoefficientAdjointComparisons | unclaimed | DAG parent; unchanged statement and definitions, so no adaptation. |

`python3 tools/downstream.py Sheaf.Paper.SupportedTriangleMateIdentification --uses
AlgebraicGeometry.Etale.scalarSupportTriangle_mate_identification` reports zero
downstream Lean modules and one textual use, the item's declaration itself.
The DAG parent `lem-pur-finite-coefficient-adjoint-comparisons` keeps this dependency.
There are no forced adaptations and no changes to any module held by another group.

## Status

landed 20261021T134314-L-813842 2026-10-21 (merge of deliver/B9/Sheaf.Paper.SupportedTriangleMateIdentification)
