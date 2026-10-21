# AlgebraicGeometry.ProEtale.CondensedRing.integralResidueExchange_comparison

## Reason

Restore the missing module assigned by coord/rework.tsv, preserved at
quarantine/Sheaf/Paper/IntegralResidueExchange.lean after a merge-queue cluster restore.
This restores the actual nonempty theorem module and its complete proof, not an empty
replacement or a withdrawal. All public imports, declarations, attributes, options,
proof dependencies and the original Lean attachment are preserved.

## Old

The live source is absent; the quarantined theorem has this signature in its original
namespace, universe and variable context:

```lean
theorem integralResidueExchange_comparison
    (sq : CommSq g' f' f g)
    (M : integralConstructible ℓ E X)
    (hPerfect : ∀ T : Scheme.{u},
      IsDualizable ((DerivedCategory.singleFunctor _ 0).obj
        ((Mod.comap (coefficientMap (integralReductionMap ℓ E) T)).obj
          (Mod.regular (condensedRingObj
            (Profinite.continuousMapRingObj.{u} (integralResidue ℓ E)) T)))))
    (hTensor : ∀ T : Scheme.{u},
      ∃ ε : DerivedCategory.Qh ⋙ (integralReduction ℓ E T ⋙
            (Mod.comap (coefficientMap (integralReductionMap ℓ E) T)).mapDerivedCategory) ⟶
          Functor.mapHomotopyCategory
            (MonoidalCategory.tensorLeft
            ((Mod.comap (coefficientMap (integralReductionMap ℓ E) T)).obj
              (Mod.regular (condensedRingObj
                (Profinite.continuousMapRingObj.{u} (integralResidue ℓ E)) T)))) (.up ℤ) ⋙
            DerivedCategory.Qh,
        Functor.IsLeftDerivedFunctor
          (integralReduction ℓ E T ⋙
            (Mod.comap (coefficientMap (integralReductionMap ℓ E) T)).mapDerivedCategory)
          ε (HomotopyCategory.quasiIso
            (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
              (condensedRingObj (integralCoeff ℓ E) T)) (.up ℤ))) :
    ∃ N : ProEtale.BoundedConstructible
        (condensedRingObj (Profinite.continuousMapRingObj.{u} (integralResidue ℓ E)) X),
      Nonempty (N.obj ≅ (integralReduction ℓ E X).obj M.obj) ∧
      Nonempty (Arrow.mk ((integralReduction ℓ E Y').map
          ((boundedConstructibleBaseChange (integralCoeff ℓ E) ℓ (sq.asOver (Spec (.of k)))).app M).hom) ≅
        Arrow.mk ((boundedConstructibleBaseChange (Profinite.continuousMapRingObj.{u} (integralResidue ℓ E)) ℓ (sq.asOver (Spec (.of k)))).app N).hom)
```

## New

Restore the signature below with its original complete proof. Only whitespace differs
from the archived file, to remove four long-line warnings. The complete file was
checked to have the identical non-whitespace character sequence to its archive.
The DAG lean.statement is wrapped correspondingly; the proof route is unchanged.

```lean
theorem integralResidueExchange_comparison
    (sq : CommSq g' f' f g)
    (M : integralConstructible ℓ E X)
    (hPerfect : ∀ T : Scheme.{u},
      IsDualizable ((DerivedCategory.singleFunctor _ 0).obj
        ((Mod.comap (coefficientMap (integralReductionMap ℓ E) T)).obj
          (Mod.regular (condensedRingObj
            (Profinite.continuousMapRingObj.{u} (integralResidue ℓ E)) T)))))
    (hTensor : ∀ T : Scheme.{u},
      ∃ ε : DerivedCategory.Qh ⋙ (integralReduction ℓ E T ⋙
            (Mod.comap (coefficientMap (integralReductionMap ℓ E) T)).mapDerivedCategory) ⟶
          Functor.mapHomotopyCategory
            (MonoidalCategory.tensorLeft
            ((Mod.comap (coefficientMap (integralReductionMap ℓ E) T)).obj
              (Mod.regular (condensedRingObj
                (Profinite.continuousMapRingObj.{u} (integralResidue ℓ E)) T)))) (.up ℤ) ⋙
            DerivedCategory.Qh,
        Functor.IsLeftDerivedFunctor
          (integralReduction ℓ E T ⋙
            (Mod.comap (coefficientMap (integralReductionMap ℓ E) T)).mapDerivedCategory)
          ε (HomotopyCategory.quasiIso
            (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
              (condensedRingObj (integralCoeff ℓ E) T)) (.up ℤ))) :
    ∃ N : ProEtale.BoundedConstructible
        (condensedRingObj (Profinite.continuousMapRingObj.{u} (integralResidue ℓ E)) X),
      Nonempty (N.obj ≅ (integralReduction ℓ E X).obj M.obj) ∧
      Nonempty (Arrow.mk ((integralReduction ℓ E Y').map
          ((boundedConstructibleBaseChange (integralCoeff ℓ E) ℓ
            (sq.asOver (Spec (.of k)))).app M).hom) ≅
        Arrow.mk ((boundedConstructibleBaseChange
          (Profinite.continuousMapRingObj.{u} (integralResidue ℓ E)) ℓ
          (sq.asOver (Spec (.of k)))).app N).hom)
```

## Users

The source-only downstream tool with --allow-missing reports no live downstream modules.
A search of both live and quarantined Lean finds the archived direct consumer below.
Its call still supplies the same perfectness and tensor hypotheses and composes the
returned arrow isomorphism with the finite discrete comparison. It needs no adaptation.
The DAG parent remains attached, so absence of live importers is not a withdrawal reason.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.IntegralResidueExchange | H4 | Restore the assigned module with identical declarations and proof. |
| Sheaf.Paper.IntegralFiniteExchangeComparison | quarantined; not adapted | Identical theorem and exported context; its original call is preserved. |

## Status

landed 20261021T023312-L-2946396 2026-10-21 (merge of deliver/H4/Sheaf.Paper.IntegralResidueExchange)
