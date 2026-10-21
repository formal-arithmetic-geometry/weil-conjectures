# AlgebraicGeometry.standardSingleFlatCounitOnOpen_affine

## Reason

Restore the assigned quarantined affine flat-counit presentation theorem. Its
`coord/rework.tsv` row names the absent source and the preserved archive
`quarantine/Sheaf/AlgebraicGeometry/StandardSingleFlatCounitAffine.lean`.
The archive contains a complete proof and no `sorry`; this is a zero-hole rework
item rather than a new theorem proof.

The archive initially fails with a missing tensor-pullback additivity instance
and unknown `SingleComplexBaseChange.counit`. Add an ordinary proof import of
`WeilConjectures.AlgebraicGeometry.SingleComplexBaseChangeStalkCondition`,
the provider already attached to the corresponding dependency node. The private
comparison uses the same standard derived categories, single complex, ordinary
exchange and canonical unit compatibility. Its derived-category universe choices
are made explicit. The public theorem's signature and docstring and the public
import of the presentation predicate are preserved verbatim. No definition or
source-library declaration is changed.

## Old

The source path is absent. Its preserved archive exports exactly:

```lean
theorem standardSingleFlatCounitOnOpen_affine
    {Y B A : Scheme.{u}} (p : Y ⟶ B) [IsAffine B] [IsAffine A]
    (g : A ⟶ B) (U : Y.Opens) (hU : IsAffineOpen U) :
    StandardSingleFlatCounitOnOpen p g U
```

The archive's public import is:

```lean
public import Sheaf.AlgebraicGeometry.StandardSingleFlatCounitPresentation
```

## New

The original source path again exports exactly:

```lean
theorem standardSingleFlatCounitOnOpen_affine
    {Y B A : Scheme.{u}} (p : Y ⟶ B) [IsAffine B] [IsAffine A]
    (g : A ⟶ B) (U : Y.Opens) (hU : IsAffineOpen U) :
    StandardSingleFlatCounitOnOpen p g U
```

Its public import is unchanged, and the new proof import is:

```lean
import WeilConjectures.AlgebraicGeometry.SingleComplexBaseChangeStalkCondition
```

There is no change of hypotheses, conclusion, universe of the public theorem,
visibility or mathematical construction. The existing DAG attachment and all
statement and proof dependencies remain valid. The quarantine archive stays intact.

## Users

`tools/downstream.py Sheaf.AlgebraicGeometry.StandardSingleFlatCounitAffine
--uses standardSingleFlatCounitOnOpen_affine --allow-missing` reports zero live
consumers, because the item and its consumer are quarantined. A reverse import
scan of `lean/` and `quarantine/`, preferring live sources, finds one direct
archived consumer and 76 transitive consumers. The one direct consumer is also
the only DAG parent, `lem-pc-standard-single-stalk-flat-counit-model`. It supplies
the affine case of source-open induction by applying this exact unchanged theorem.
No consumer is adapted or weakened; the same affine argument, including the
empty source and zero module cases, is restored.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.StandardSingleFlatCounitAffine | C1 | Assigned root restored with its existing public theorem. |
| Sheaf.AlgebraicGeometry.StandardSingleStalkFlatCounitModel | quarantined; not adapted | The affine induction branch uses the identical signature. |

The unit record `sk-thm-picard-coherence` is unchanged. Restoration retains the
affine input to its bounded flat model construction; no unit step is bypassed.
No target statement or definition used by a target changes its meaning.

The final restored source compiles without errors or warnings through `lcompile.py`
(48.6 seconds). A scratch consumer reproduces the original affine induction branch
verbatim and compiles against that source (2.5 seconds). The public theorem's
axioms are exactly `propext`, `Classical.choice` and `Quot.sound`. The scratch
consumer is not delivered. The independent delivery probe checks all declarations.

## Status

landed 20261021T005725-L-1885266 2026-10-21 (merge of deliver/C1/Sheaf.AlgebraicGeometry.StandardSingleFlatCounitAffine)
