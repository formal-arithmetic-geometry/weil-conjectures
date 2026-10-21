# AlgebraicGeometry.Scheme.picard_connective_model_comparison

## Reason

Restore the theorem preserved at the quarantine path recorded in coord/rework.tsv.
The cluster restore removed its live module; this did not withdraw its statement or
its parent obligation. The quarantined PicardScalarDerivedCycles module still applies
this theorem. Preserve its existing DAG attachment, statement and proof dependencies.
The private cycle equivalence now uses the existing integer-indexed
HomologicalComplex.fromSingleEquiv and proves additivity explicitly, replacing the
duplicate constructor and inverse proofs. This needs only a private proof import.
The restoration uses the current upstream definitions and the existing termwise
comparison, with no new mathematical obligations.

## Old

The live Lean path is absent. The quarantined theorem has signature:

```lean
theorem picard_connective_model_comparison
    [∀ Y : Scheme.{v},
      HasDerivedCategory.{v + 1} (SheafOfModules.{v} (moduleRings Y.toRingedSpace))]
    [∀ (Y : Scheme.{v}) (U : Y.Opens), HasDerivedCategory.{v + 1}
      (SheafOfModules.{v} ((moduleRings Y.toRingedSpace).over U))]
    (W : Scheme.{v}) (E : schemeDerivedCategory W) (U : W.Opens)
    (K : CochainComplex
      (SheafOfModules.{v} ((moduleRings W.toRingedSpace).over U)) ℤ)
    (hK : IsStrictlyPerfect W U K) (hneg : ∀ i : ℤ, i < 0 → IsZero (K.X i))
    (hE : Nonempty ((SheafOfModules.overFunctor.{v}
      (moduleRings W.toRingedSpace) U).mapDerivedCategory.obj E ≅
        DerivedCategory.Q.obj K)) :
    ∃ q : ∀ {T : Scheme.{v}} (t : T ⟶ W) (s : T ⟶ U.toScheme),
        s ≫ U.ι = t →
          picardDerivedModelSections E t ≃+ picardOrdinaryModelCycles W U K t s,
      ∀ {T T' : Scheme.{v}} (i : T' ⟶ T) (t : T ⟶ W) (t' : T' ⟶ W)
        (s : T ⟶ U.toScheme) (s' : T' ⟶ U.toScheme)
        (ht : i ≫ t = t') (hs : i ≫ s = s')
        (hf : s ≫ U.ι = t) (hf' : s' ≫ U.ι = t')
        (ξ : picardDerivedModelSections E t),
        (q t' s' hf' (picardDerivedModelRestriction E i t t' ht ξ)).val =
          picardOrdinaryModelRestriction W U K i t t' s s' ht hs
            (q t s hf ξ).val
```

## New

Restore that exact signature and its complete proof. There are no `sorry` terms.
The proof obtains the coherent termwise isomorphisms, constructs the additive
localization and degree-zero cycle equivalences, and proves restriction naturality
by the uniqueness of the inverse localization representative.

## Users

The live downstream.py query reports an unknown module because the assigned path is
quarantined. Searches in lean/ and quarantine/ find the direct consumer below;
DAG statement dependencies, proof dependencies and proof-step uses retain this parent.
No consumer signature changes. No adopted-source file is changed.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.PicardConnectiveModelComparison | F2 | Restore the complete theorem. |
| Sheaf.AlgebraicGeometry.PicardScalarDerivedCycles | unclaimed | The same comparison theorem is available again; no adaptation. |

## Status

landed 20261021T005735-L-1887060 2026-10-21 (merge of deliver/F2/Sheaf.AlgebraicGeometry.PicardConnectiveModelComparison)
