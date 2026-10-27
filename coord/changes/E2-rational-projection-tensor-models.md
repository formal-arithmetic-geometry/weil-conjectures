# WeilConjectures.rationalProjectionTensorComparison

## Reason

Prove the compact-support compatibility hole. The combined file took 86.6 seconds
after local reducibility improvements, shared normalization, and removal of
expensive equality rewriting. Extract the self-contained tensor-model calculation
to `Sheaf.Paper.RationalProjectionTensorModels`, retaining the declaration names,
signatures and the definition body of the canonical tensor comparison. The item
publicly imports the new module, preserving every existing importer's access.
This changes location and adds a proved normalization API, not mathematical data.
All reducibility changes are local to proof compilation.

## Old

In `Sheaf.Paper.RationalProjectionTensorCompatibility`:

```lean
theorem rationalProjectionTensorFunctorEq
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    {E : Type u} [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] (H : SixFunctorHigherOperations D C E)
    (X : SixFunctorSpace D) :
    Functor.uncurry.obj (H.integralTensor X) ⋙
        sfRationalConstructibleLocalization C.l E X.obj.left =
      (sfRationalConstructibleLocalization C.l E X.obj.left).prod
          (sfRationalConstructibleLocalization C.l E X.obj.left) ⋙
        Functor.uncurry.obj (H.rationalTensor X)

def rationalProjectionTensorComparison
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    {E : Type u} [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] (H : SixFunctorHigherOperations D C E)
    (X : SixFunctorSpace D) :=
  eqToIso (rationalProjectionTensorFunctorEq H X)
```

## New

The same declarations, with verbatim signatures and definition body, are in
`Sheaf.Paper.RationalProjectionTensorModels`:

```lean
theorem rationalProjectionTensorFunctorEq
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    {E : Type u} [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] (H : SixFunctorHigherOperations D C E)
    (X : SixFunctorSpace D) :
    Functor.uncurry.obj (H.integralTensor X) ⋙
        sfRationalConstructibleLocalization C.l E X.obj.left =
      (sfRationalConstructibleLocalization C.l E X.obj.left).prod
          (sfRationalConstructibleLocalization C.l E X.obj.left) ⋙
        Functor.uncurry.obj (H.rationalTensor X)

def rationalProjectionTensorComparison
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    {E : Type u} [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] (H : SixFunctorHigherOperations D C E)
    (X : SixFunctorSpace D) :=
  eqToIso (rationalProjectionTensorFunctorEq H X)
```

The original module retains its existing public import and additionally has:

```lean
public import Sheaf.Paper.RationalProjectionTensorModels
```

The new module also proves `WeilConjectures.rationalProjectionPullTensorSquare`,
the common canonical-model calculation for the proper and open pullbacks.
It has no compact-support or projection-formula hypothesis. No target statement,
operation data, instance or public simplification attribute changes.

## Users

The downstream scan finds one external textual user of the moved comparison,
`RationalProjectionComparisonEquations`, and no external textual user of the
moved tensor equality. The six direct importers are below. Their signatures and
sources require no adaptation. All other transitive importers receive the same
public declarations through these imports.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.RationalProjectionTensorCompatibility | E2 | Imports the extracted normalization and proves the remaining hole. |
| Sheaf.Paper.CommonProjectionProperTensorCompatibility | unclaimed in local claim records | Public names and definitions preserved; original compiled unchanged (lcompile exit 0). |
| Sheaf.Paper.ProjectionMateFactors | unclaimed in local claim records | Public names and definitions preserved; original compiled unchanged (lcompile exit 0). |
| Sheaf.Paper.CommonProjectionProperFactor | unclaimed in local claim records | Public names and definitions preserved; original compiled unchanged (lcompile exit 0). |
| Sheaf.Paper.RationalProjectionComparisonEquations | unclaimed in local claim records | Public names and definitions preserved; original compiled unchanged (lcompile exit 0). |
| Sheaf.Paper.CommonProjectionOpenFactor | unclaimed in local claim records | Public names and definitions preserved; original compiled unchanged (lcompile exit 0). |
| Sheaf.Paper.CommonProjectionTensorCompatibility | unclaimed in local claim records | Public names and definitions preserved; original compiled unchanged (lcompile exit 0). |

## Status

landed 20261027T050552-L-238639 2026-10-27 (merge of deliver/E2/Sheaf.Paper.RationalProjectionTensorCompatibility)
