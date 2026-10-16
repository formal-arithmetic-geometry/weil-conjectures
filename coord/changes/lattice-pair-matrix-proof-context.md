# AlgebraicGeometry.ProEtale.integralLatticePair_matrixAtBasis

## Reason

The proof adds generic private helpers and needs extra universe names, scoped tensor
and matrix notation, and the existing module elaboration settings. The static
interface checker conservatively records these non-declaration commands as an
interface change. This record documents that context change. No existing public
signature, definition body, binder, universe parameter of the theorem, or target
meaning changes. No new global instance or rewrite rule is registered.

## Old

Original elaboration context, verbatim:

```lean
universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale
```

Original theorem signature, verbatim:

```lean
theorem integralLatticePair_matrixAtBasis (X : Scheme.{u})
    (K : Type u) [Field K] [TopologicalSpace K] [IsTopologicalRing K] (A : Subring K)
    (L : SheafOfModules.{u + 1} (latticeModuleRing X K))
    (U : X.ProEt) (n : ℕ) (e : L.over U ≅ latticeFreeSheaf X K U n)
    (V : X.ProEt) (f : V ⟶ U)
    (P : IntegralLatticePair (latticeCoefficientSheafMap X A.subtype continuous_subtype_val)
      L V)
    (q : P.module.LocalGeneratorsData) [q.IsLocallyFreeData] [q.IsFiniteType]
    (i : q.I) (W : X.ProEt) (a : W ⟶ V) (t : Over.mk a ⟶ q.X i) :
    ∃ G : Matrix.GeneralLinearGroup (Fin n)
        ((latticeCoefficientSheaf X K).obj.obj (op W)),
      ∀ T : Over W,
        Set.image (e.hom.val.app (op (Over.mk (T.hom ≫ a ≫ f))))
          (P.image (op (Over.mk (T.hom ≫ a)))) =
        sectionMatrixLatticeImage X K A U n (op (Over.mk (T.hom ≫ a ≫ f)))
          (Matrix.GeneralLinearGroup.map
            (((latticeCoefficientSheaf X K).obj.map T.hom.op).hom) G)
```

## New

New elaboration context, verbatim:

```lean
universe u v w

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types true

open scoped ChangeOfRings Matrix
```

The theorem signature is identical, verbatim:

```lean
theorem integralLatticePair_matrixAtBasis (X : Scheme.{u})
    (K : Type u) [Field K] [TopologicalSpace K] [IsTopologicalRing K] (A : Subring K)
    (L : SheafOfModules.{u + 1} (latticeModuleRing X K))
    (U : X.ProEt) (n : ℕ) (e : L.over U ≅ latticeFreeSheaf X K U n)
    (V : X.ProEt) (f : V ⟶ U)
    (P : IntegralLatticePair (latticeCoefficientSheafMap X A.subtype continuous_subtype_val)
      L V)
    (q : P.module.LocalGeneratorsData) [q.IsLocallyFreeData] [q.IsFiniteType]
    (i : q.I) (W : X.ProEt) (a : W ⟶ V) (t : Over.mk a ⟶ q.X i) :
    ∃ G : Matrix.GeneralLinearGroup (Fin n)
        ((latticeCoefficientSheaf X K).obj.obj (op W)),
      ∀ T : Over W,
        Set.image (e.hom.val.app (op (Over.mk (T.hom ≫ a ≫ f))))
          (P.image (op (Over.mk (T.hom ≫ a)))) =
        sectionMatrixLatticeImage X K A U n (op (Over.mk (T.hom ≫ a ≫ f)))
          (Matrix.GeneralLinearGroup.map
            (((latticeCoefficientSheaf X K).obj.map T.hom.op).hom) G)
```

The extra `v` and `w` universe names belong to generic private proof helpers.
Scoped notation and elaboration options govern this module's elaboration; they
introduce no exported declaration. All added imports of the existing module are
proof-only imports. The new helper module has a separate DAG node and fully proved
public theorem.

## Users

`tools/downstream.py Sheaf.Paper.LatticePairMatrixAtBasis --uses
integralLatticePair_matrixAtBasis` reports the twenty downstream modules below,
with direct textual uses only in `Sheaf.Paper.LatticePairLocalMatrix` and the
assigned module. All existing consumers retain the same theorem signature and
meaning; no consumer is adapted. In particular, no definition used by a target
changes, so no target statement review is reopened.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.IntegralLatticeCoefficientTransport | unclaimed | No adaptation: statements and definitions retain their meanings. |
| Sheaf.AlgebraicGeometry.LisseLatticeClassSheaf | unclaimed | No adaptation: statements and definitions retain their meanings. |
| Sheaf.AlgebraicGeometry.LisseLatticeCoefficientNormalization | unclaimed | No adaptation: statements and definitions retain their meanings. |
| Sheaf.AlgebraicGeometry.LisseLatticeEtaleLocal | unclaimed | No adaptation: statements and definitions retain their meanings. |
| Sheaf.AlgebraicGeometry.LisseLatticePresentationTransport | unclaimed | No adaptation: statements and definitions retain their meanings. |
| Sheaf.AlgebraicGeometry.LisseLatticeSliceTransport | unclaimed | No adaptation: statements and definitions retain their meanings. |
| Sheaf.Paper.ContinuousAffineEtaleLattice | unclaimed | No adaptation: statements and definitions retain their meanings. |
| Sheaf.Paper.ContinuousConstructibleIntegralModel | unclaimed | No adaptation: statements and definitions retain their meanings. |
| Sheaf.Paper.ContinuousConstructibleIntegralSingle | unclaimed | No adaptation: statements and definitions retain their meanings. |
| Sheaf.Paper.ContinuousConstructibleIntegralStratum | unclaimed | No adaptation: statements and definitions retain their meanings. |
| Sheaf.Paper.ContinuousEtaleLocalLattices | unclaimed | No adaptation: statements and definitions retain their meanings. |
| Sheaf.Paper.ContinuousExchangeIntegralModel | unclaimed | No adaptation: statements and definitions retain their meanings. |
| Sheaf.Paper.ContinuousLisseStratifiedLattices | unclaimed | No adaptation: statements and definitions retain their meanings. |
| Sheaf.Paper.LatticeCosetLocalSurjectivity | unclaimed | No adaptation: statements and definitions retain their meanings. |
| Sheaf.Paper.LatticePairLocalMatrix | unclaimed | No adaptation: statements and definitions retain their meanings. |
| Sheaf.Paper.LatticeSheafLocallyConstant | unclaimed | No adaptation: statements and definitions retain their meanings. |
| Sheaf.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperApp | unclaimed | No adaptation: statements and definitions retain their meanings. |
| TargetsCheck | unclaimed | No adaptation: statements and definitions retain their meanings. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.CompactSupport | unclaimed | No adaptation: statements and definitions retain their meanings. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.Proper | unclaimed | No adaptation: statements and definitions retain their meanings. |
| Sheaf.Paper.LatticePairMatrixAtBasis | C2 | Assigned item; proof completed, original signature unchanged. |

## Status

landed 20261016T102627-L-2294632 2026-10-16 (merge of deliver/C2/Sheaf.Paper.LatticePairMatrixAtBasis)
