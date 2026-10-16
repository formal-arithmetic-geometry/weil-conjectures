# condensedConstructiblePiece

## Reason

The original predicate repeats the fully specialized finite-field ring throughout a
nested existential telescope. Kernel checking its elimination against the abstract
coefficient-ring continuity argument exceeds the per-file limit. Introduce the identical
predicate with a coefficient-ring parameter, `condensedLocallyClosedPiece`, and make the
existing predicate its specialization. This changes no witness, hypothesis, conclusion,
universe, or visibility. Unfolding the new definition gives the old body verbatim.
The new predicate constructs only a proposition; no data are chosen from existence.

## Old

```lean
def condensedConstructiblePiece
    (T : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    (E : Padic.FiniteCoefficientFields ℓ (PadicAlgCl ℓ)) :
    ObjectProperty (DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
        (condensedRingObj (Profinite.continuousMapRingObj E.val) T))) :=
  fun K ↦ ∃ (Z U : Scheme.{u}) (i : Z ⟶ T) (j : U ⟶ Z),
    Exists fun [_hi : IsClosedImmersion i] ↦ Exists fun [_hj : IsOpenImmersion j] ↦
      QuasiCompact j ∧ ∃ (P : Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1})
        (condensedRingObj (Profinite.continuousMapRingObj E.val) U)),
        IsLocallyFinitelyPresented
          (condensedRingObj (Profinite.continuousMapRingObj E.val) U) P ∧
        Nonempty (K ≅ (DerivedCategory.singleFunctor _ 0).obj
          ((CondensedRing.lowerStar (Profinite.continuousMapRingObj E.val) i).obj
            ((CondensedRing.openImmersionLowerShriek
              (Profinite.continuousMapRingObj E.val) j).obj P)))
```

## New

```lean
def condensedConstructiblePiece
    (T : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    (E : Padic.FiniteCoefficientFields ℓ (PadicAlgCl ℓ)) :
    ObjectProperty (DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
        (condensedRingObj (Profinite.continuousMapRingObj E.val) T))) :=
  condensedLocallyClosedPiece (Profinite.continuousMapRingObj E.val) T
```

The new definition is in `Sheaf.Paper.CondensedLocallyClosedPiece`; its body is the old
existential telescope with the coefficient expression replaced by its parameter Λ.
The public signature of `condensedConstructiblePiece` is identical. Definitions used
by the targets are touched: their semantic review should confirm this definitional
identity. The five direct users below keep exactly the same meaning and signatures.
No other existing module is edited or requires adaptation.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.CondensedConstructibleExtensionTower | unclaimed | definitionally identical predicate; no edit required |
| Sheaf.Paper.CondensedConstructibleOneStep | J1 | definitionally identical predicate; no edit required |
| Sheaf.Paper.CondensedConstructiblePiece | unclaimed | definition body factored; signature unchanged |
| Sheaf.Paper.CondensedLocalPieceHomContinuity | H3 | proof uses the abstract API |
| Sheaf.Paper.CondensedSheafExtContinuity | unclaimed | definitionally identical predicate; no edit required |

## Status

landed 20261016T011145-L-265743 2026-10-16 (merge of deliver/H3/Sheaf.Paper.CondensedLocalPieceHomContinuity)
