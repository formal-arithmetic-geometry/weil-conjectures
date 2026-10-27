# AlgebraicGeometry.Etale.ordinary_chart_exceptional_scalar

## Reason

The item's existing intrinsic reduction-exceptional proof plan assumes a field base,
which is absent from its Noetherian statement. Isolate the ordinary local chart
mate equation; prove the coordinate cover, cancellation and global detection in Lean.
This adds one public supporting theorem in a new module, imported privately by the item.
All existing public declarations and imports retain their signatures and visibility.

## Old

No declaration named `AlgebraicGeometry.Etale.ordinary_chart_exceptional_scalar`.
The existing `finite_smooth_dualizing_scalar` proof was `by sorry`.

## New

The new supporting theorem has the following exact signature and one named proof hole.

```lean
theorem ordinary_chart_exceptional_scalar
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (N : ℕ) (hN : 0 < N)
    (hA : (N : A) = 0) (hB : (N : B) = 0)
    {V S U : Scheme.{u}} [IsNoetherian V] [IsNoetherian S] [IsNoetherian U]
    (hS : IsUnit (N : Γ(S, ⊤))) (g : V ⟶ S) [HasCompactification g]
    (i : U ⟶ V) [IsOpenImmersion i] (d : ℕ)
    (e : U ⟶ affineTraceTower S d) [AlgebraicGeometry.Etale e]
    [IsSeparated e] [LocallyOfFiniteType e] [QuasiCompact e]
    (he : i ≫ g = e ≫ affineTraceProjection S d)
    (MA : EtaleCompactSupportNormalization A) (MB : EtaleCompactSupportNormalization B)
    (tA : OrdinaryFiniteTwistTransport A N hA)
    (tB : OrdinaryFiniteTwistTransport B N hB)
    (PA : ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (N : Γ(T, ⊤))),
      OrdinaryFiniteP1Datum A N hA tA T hT)
    (PB : ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (N : Γ(T, ⊤))),
      OrdinaryFiniteP1Datum B N hB tB T hT)
    (K : DerivedCategoryModule A S) :
    (scalarExtension φ U).map
        ((ProEtale.reductionEtaleChartRightIso A MA g i d e he
          (HasCompactification.compactification g)
          (rightDerivedUpperShriek (ModuleCat.{u + 1} A) g)
          (rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} A) g)
          N hA tA PA hS).hom.app K) ≫
      (ProEtale.reductionEtaleChartScalarIso φ N hA hB hS d e K).hom =
    (scalarPullbackIso φ i).inv.app
        ((rightDerivedUpperShriek (ModuleCat.{u + 1} A) g).obj K) ≫
      (ordinaryFinitePullback B i).map (ExceptionalCoefficients.mateMap φ g K) ≫
      (ProEtale.reductionEtaleChartRightIso B MB g i d e he
        (HasCompactification.compactification g)
        (rightDerivedUpperShriek (ModuleCat.{u + 1} B) g)
        (rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} B) g)
        N hB tB PB hS).hom.app ((scalarExtension φ S).obj K)
```

The item has a complete proof from this local equation. This is a decomposition,
with one original hole closed and one strictly local supporting hole added.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.SecSmoothPurity.FiniteSmoothDualizingScalar | M1 | Private proof import of the new local square; public statement unchanged. |

There are no pre-existing consumers of the new declaration. No existing dependency
module is changed and no consumer adaptation is needed.

## Status

landed 20261027T210134-L-1662152 2026-10-27 (merge of deliver/M1/Sheaf.SecSmoothPurity.FiniteSmoothDualizingScalar)
