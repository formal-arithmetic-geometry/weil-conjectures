# AlgebraicGeometry.ProEtale.CondensedRing.coefficientProjectionSquare

## Reason

The delivery adds scoped variables, proved private helpers, private proof imports and
file-local irreducibility/instance settings to check the canonical derived comparison
calculation without unfolding large concrete constructions. This record documents those
local commands conservatively. No existing signature, definition, public import, exported
attribute or global instance changes. The existing hole is proved from the declared
realization/normalization dependencies and the existing projection-mate square theorem.

## Old

```lean
theorem coefficientProjectionSquare
    (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    {X Y : Over (Spec (.of k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (f : X ⟶ Y)
    {R S : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj R] [IsCommMonObj R] [MonObj S] [IsCommMonObj S]
    (a : R ⟶ S) [IsMonHom a]
    [∀ Z : Scheme.{u}, PreservesFiniteLimits (Mod.extendScalars (coefficientMap a Z))]
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
      (condensedRingObj R X.left)))
    (M : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y.left) Ab.{u + 1})
      (condensedRingObj R Y.left))) :
    ((internalScalarTensorComparison a Y.left).app
        ((moduleObjectDerivedPushforward R f.left).obj K)).app M ≫
      ((derivedTensor S Y.left).map ((derivedPushHom a f.left).app K)).app
        ((internalScalarExtension a Y.left).obj M) ≫
      moduleObjectProjectionMap S f.left
        ((internalScalarExtension a X.left).obj K)
        ((internalScalarExtension a Y.left).obj M) =
    (internalScalarExtension a Y.left).map
        (moduleObjectProjectionMap R f.left K M) ≫
      (derivedPushHom a f.left).app
        (((derivedTensor R X.left).obj K).obj
          ((moduleObjectDerivedPullback R f.left).obj M)) ≫
      (moduleObjectDerivedPushforward S f.left).map
        (((internalScalarTensorComparison a X.left).app K).app
            ((moduleObjectDerivedPullback R f.left).obj M) ≫
          ((derivedTensor S X.left).obj
            ((internalScalarExtension a X.left).obj K)).map
              ((derivedPullIso a f.left).hom.app M))
```

## New

```lean
theorem coefficientProjectionSquare
    (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    {X Y : Over (Spec (.of k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (f : X ⟶ Y)
    {R S : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj R] [IsCommMonObj R] [MonObj S] [IsCommMonObj S]
    (a : R ⟶ S) [IsMonHom a]
    [∀ Z : Scheme.{u}, PreservesFiniteLimits (Mod.extendScalars (coefficientMap a Z))]
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
      (condensedRingObj R X.left)))
    (M : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y.left) Ab.{u + 1})
      (condensedRingObj R Y.left))) :
    ((internalScalarTensorComparison a Y.left).app
        ((moduleObjectDerivedPushforward R f.left).obj K)).app M ≫
      ((derivedTensor S Y.left).map ((derivedPushHom a f.left).app K)).app
        ((internalScalarExtension a Y.left).obj M) ≫
      moduleObjectProjectionMap S f.left
        ((internalScalarExtension a X.left).obj K)
        ((internalScalarExtension a Y.left).obj M) =
    (internalScalarExtension a Y.left).map
        (moduleObjectProjectionMap R f.left K M) ≫
      (derivedPushHom a f.left).app
        (((derivedTensor R X.left).obj K).obj
          ((moduleObjectDerivedPullback R f.left).obj M)) ≫
      (moduleObjectDerivedPushforward S f.left).map
        (((internalScalarTensorComparison a X.left).app K).app
            ((moduleObjectDerivedPullback R f.left).obj M) ≫
          ((derivedTensor S X.left).obj
            ((internalScalarExtension a X.left).obj K)).map
              ((derivedPullIso a f.left).hom.app M))
```

The identical signature now has a complete proof. The local helpers perform only
conjugation, derived-composition normalization, exact-functor transport and iterated mates.

## Users

`tools/downstream.py Sheaf.Paper.CoefficientProjectionSquare --uses
coefficientProjectionSquare` reports zero downstream modules and only the item itself
using the declaration name. The DAG parents continue to use the unchanged statement.
No consumer requires adaptation and no target-statement review is reopened.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.CoefficientProjectionSquare | N1 | One proof hole closed; public API unchanged. |

## Status

landed 20261023T231848-L-3652690 2026-10-23 (merge of deliver/N1/Sheaf.Paper.CoefficientProjectionSquare)
