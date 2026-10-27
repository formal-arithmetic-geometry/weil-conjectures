# chartAffineGamma_zero

## Reason

Compose the identity exceptional comparison and identity pullback comparison as
natural isomorphisms before evaluating at the coefficient unit. This has precisely
the previous value by `NatIso.trans_app` (definitionally). The proposition,
hypotheses, normalization, and every map remain unchanged. This avoids repeating
the conversion between the derived-functor endpoint presentations at the unit.
The displayed comparison is checked at an abstract ring and specialized through
a local function in the proposition; beta and zeta reduction recover the old
proposition. No hypothesis or conclusion changes.
No target statement or mathematical definition changes.

## Old

```lean
theorem chartAffineGamma_zero (P : PurityFiniteSetting.{u})
    (B : Scheme.{u}) [IsAffine B] (aB : B ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aB] [QuasiCompact aB]
    (t : Etale.OrdinaryFiniteTwistTransport P.Coefficient P.diagonalExponent
      P.diagonalExponent_annihilates)
    (D : ∀ (T : Scheme.{u}) [IsNoetherian T]
      (hT : IsUnit (P.diagonalExponent : Γ(T, ⊤))),
      Etale.OrdinaryFiniteP1Datum P.Coefficient P.diagonalExponent
        P.diagonalExponent_annihilates t T hT) :
    P.chartAffineGamma B aB 0 t D =
      ((Etale.rightDerivedUpperShriekIsoOfIso
        (ModuleCat.{u + 1} P.Coefficient) (Iso.refl B)).app
          (Etale.ordinaryFiniteUnit P.Coefficient B) ≪≫
        (Etale.leftDerivedUpperStarId (ModuleCat.{u + 1} P.Coefficient) B).app
          (Etale.ordinaryFiniteUnit P.Coefficient B)).symm
```

## New

```lean
theorem chartAffineGamma_zero (P : PurityFiniteSetting.{u})
    (B : Scheme.{u}) [IsAffine B] (aB : B ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aB] [QuasiCompact aB]
    (t : Etale.OrdinaryFiniteTwistTransport P.Coefficient P.diagonalExponent
      P.diagonalExponent_annihilates)
    (D : ∀ (T : Scheme.{u}) [IsNoetherian T]
      (hT : IsUnit (P.diagonalExponent : Γ(T, ⊤))),
      Etale.OrdinaryFiniteP1Datum P.Coefficient P.diagonalExponent
        P.diagonalExponent_annihilates t T hT) :
    let identityComparison (A : Type (u + 1)) [CommRing A] (S : Scheme.{u}) :=
      (((Etale.rightDerivedUpperShriekIsoOfIso
        (ModuleCat.{u + 1} A) (Iso.refl S)) ≪≫
        Etale.leftDerivedUpperStarId (ModuleCat.{u + 1} A) S).app
          (Etale.ordinaryFiniteUnit A S)).symm
    P.chartAffineGamma B aB 0 t D = identityComparison P.Coefficient B
```

## Users

`tools/downstream.py --uses chartAffineGamma_zero` and the text search find no external
Lean consumer. The uses within this module have the same endpoints and maps by
`NatIso.trans_app`; no adaptation of another module is required.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.DiagonalDncChartNormalization | T5 | identical map, composed before evaluation |

## Status

landed 20261026T002820-L-117385 2026-10-26 (merge of deliver/T5/Sheaf.Paper.DiagonalDncChartNormalization)
