# sfQcqsCompactSupport_normalizedLift_existsUnique

## Reason

Separate the constructed normalized natural isomorphism from the disputed assertion of uniqueness from torsion inputs. The parent now consumes the proved existence lemma; its uniqueness proof and public interface stay identical. No definition or theorem statement changes.

## Old

```lean
theorem sfQcqsCompactSupport_normalizedLift_existsUnique :
    ∃! τ : (sfIntegralConstructible l E X).ι ⋙ image (completed l E) c ⟶
      sfCompactSupportFiniteIntegralFunctor l K₀ hl c E ⋙
        (sfIntegralConstructible l E Y).ι,
      SfQcqsCompactSupportMorphismSpec l E K₀ hl c τ
```

## New

```lean
theorem sfQcqsCompactSupport_normalizedLift_existsUnique :
    ∃! τ : (sfIntegralConstructible l E X).ι ⋙ image (completed l E) c ⟶
      sfCompactSupportFiniteIntegralFunctor l K₀ hl c E ⋙
        (sfIntegralConstructible l E Y).ι,
      SfQcqsCompactSupportMorphismSpec l E K₀ hl c τ
```

The proof takes the hom of `sfQcqsCompactSupport_normalizedIso_exists`; the old private projection calculation moves into that lemma.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.QcqsCompactSupportNormalizedLift | unclaimed | Proof and private import refactored; signature unchanged. |
| Sheaf.Paper.QcqsCompactSupportRealization | unclaimed | Unchanged consumer; compiled against the refactoring. |

## Status

landed 20261027T034729-L-3679934 2026-10-27 (merge of deliver/Q7/Sheaf.Paper.QcqsCompactSupportTorsionInputDetection)
