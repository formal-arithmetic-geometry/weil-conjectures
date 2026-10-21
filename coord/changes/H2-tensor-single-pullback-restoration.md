# AlgebraicGeometry.tensorSingleCoefficientMap

## Reason

Restore the assigned module after the cluster-restore regression recorded in
`coord/rework.tsv`. Its live library path is absent, while its complete
implementation is preserved in quarantine. Both DAG attachments and its
quarantined consumers still require its four public declarations.

The delivered Lean file is byte-for-byte identical to
`quarantine/Sheaf/AlgebraicGeometry/TensorSinglePullbackComposition.lean`.
No definition, statement, public import, universe parameter, or attribute is
changed from that archive. The adopted source comparison and coefficient
implementations now provide its prerequisites. This record documents restoration
of a public definition; it does not authorize a different proof route or an
arbitrary choice of data.

## Old

No module exists at the live library path. The archived definition is:

```lean
@[irreducible]
def tensorSingleCoefficientMap {A B X : Scheme.{v}}
    (q : A ⟶ X) (q1 : B ⟶ X) (a : B ⟶ A) (h : a ≫ q = q1)
    (L : X.Modules) :
    (derivedPullback a).obj ((DerivedCategory.singleFunctor
      (SheafOfModules.{v} (moduleRings A.toRingedSpace)) 0).obj
        ((Scheme.Modules.tensorPullback q).obj L)) ⟶
      (DerivedCategory.singleFunctor
        (SheafOfModules.{v} (moduleRings B.toRingedSpace)) 0).obj
          ((Scheme.Modules.tensorPullback q1).obj L) :=
  Scheme.Modules.canonicalSinglePullbackMap a ((Scheme.Modules.tensorPullback q).obj L) ≫
    (DerivedCategory.singleFunctor
      (SheafOfModules.{v} (moduleRings B.toRingedSpace)) 0).map
        (Scheme.Modules.tensorCoefficientComparison q q1 a h L).hom
```

## New

```lean
@[irreducible]
def tensorSingleCoefficientMap {A B X : Scheme.{v}}
    (q : A ⟶ X) (q1 : B ⟶ X) (a : B ⟶ A) (h : a ≫ q = q1)
    (L : X.Modules) :
    (derivedPullback a).obj ((DerivedCategory.singleFunctor
      (SheafOfModules.{v} (moduleRings A.toRingedSpace)) 0).obj
        ((Scheme.Modules.tensorPullback q).obj L)) ⟶
      (DerivedCategory.singleFunctor
        (SheafOfModules.{v} (moduleRings B.toRingedSpace)) 0).obj
          ((Scheme.Modules.tensorPullback q1).obj L) :=
  Scheme.Modules.canonicalSinglePullbackMap a ((Scheme.Modules.tensorPullback q).obj L) ≫
    (DerivedCategory.singleFunctor
      (SheafOfModules.{v} (moduleRings B.toRingedSpace)) 0).map
        (Scheme.Modules.tensorCoefficientComparison q q1 a h L).hom
```

Restore its defining-equation theorem together with the complete proofs of
`tensorSinglePullback_composition` and
`tensorSingleCoefficientMap_composition`. All three theorem signatures are
identical to the archive. In particular the data remain the explicit canonical
single comparison followed by the single embedding of the fixed ordinary
coefficient comparison; no existence witness replaces this construction.

## Users

`tools/downstream.py` cannot analyze the absent live module and reports
`unknown module(s)`. A direct source search through both `lean/` and
`quarantine/` finds the following consumers. The DAG search also finds the
coefficient transpose pasting parent, whose dependencies remain intact.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.TensorSinglePullbackComposition | H2 | Restore the assigned module and all four original public declarations. |
| Sheaf.AlgebraicGeometry.PicardCoefficientTransposePasting | unclaimed; quarantined | Direct public importer and user of the coefficient morphism and its composition theorem. The identical restored interface requires no adaptation. |
| Sheaf.AlgebraicGeometry.PicardDirectImageDerivedTransposeFactorization | unclaimed; quarantined | Transitive importer and user of the defining-equation theorem. The identical restored interface requires no adaptation. |

The fixed mathematical definitions and elaborated statements are unchanged;
no target statement or unit route is changed. No consumer or upstream source
module is edited.

## Status

landed 20261021T011020-L-2028917 2026-10-21 (merge of deliver/H2/Sheaf.AlgebraicGeometry.TensorSinglePullbackComposition)
