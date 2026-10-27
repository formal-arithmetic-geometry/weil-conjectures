# AlgebraicGeometry.Etale.exists_presentedFiniteP1TraceAdjunction

## Reason

Record the proof-scope commands conservatively classified by preflight as an
interface change. The extra universe `v` and `CategoryTheory.Abelian` opening serve
private generic helpers. The added instance priorities and irreducibility attributes
are explicitly local; they prevent expensive unfolding of derived constructions
while checking this file. The transparency options remain true. These commands
introduce no exported instance, notation, simp/ext attribute or hypothesis. The
original public import and the theorem signature are identical. The other added
imports are private proof imports.

## Old

```lean
theorem exists_presentedFiniteP1TraceAdjunction
    (A : Type (u + 1)) [CommRing A] [Finite A] (N : ℕ) (hN : 0 < N)
    (hA : (N : A) = 0) (t : OrdinaryFiniteTwistTransport A N hA)
    (d : ∀ (T : Scheme.{u}) (hT : IsUnit (N : Γ(T, ⊤))),
      ArbitraryBaseFiniteP1Splitting A N hA t T hT)
    (hbc : ArbitraryBaseFiniteP1BaseChange A N hA t d)
    {X Y : Scheme.{u}} (q : X ⟶ Y) [IsProper q] [HasCompactification q]
    (e : X ≅ ProjectiveLine Y) (w : e.hom ≫ (ProjectiveLine Y ↘ Y) = q)
    (hY : IsUnit (N : Γ(Y, ⊤))) (hdiag : finiteP1DiagonalProperty A N hA t d Y hY) :
    ∃ adj : R(q)_![ModuleCat.{u + 1} A] ⊣
        ordinaryFiniteTwistedPullback A q ((ordinaryFiniteLine A N hA X)⟦(2 : ℤ)⟧),
      adj.counit = presentedFiniteP1Counit A N hA t q e w hY (d Y hY)
```

The body was `by sorry`; there were no private proof helpers or local proof attributes.

## New

```lean
theorem exists_presentedFiniteP1TraceAdjunction
    (A : Type (u + 1)) [CommRing A] [Finite A] (N : ℕ) (hN : 0 < N)
    (hA : (N : A) = 0) (t : OrdinaryFiniteTwistTransport A N hA)
    (d : ∀ (T : Scheme.{u}) (hT : IsUnit (N : Γ(T, ⊤))),
      ArbitraryBaseFiniteP1Splitting A N hA t T hT)
    (hbc : ArbitraryBaseFiniteP1BaseChange A N hA t d)
    {X Y : Scheme.{u}} (q : X ⟶ Y) [IsProper q] [HasCompactification q]
    (e : X ≅ ProjectiveLine Y) (w : e.hom ≫ (ProjectiveLine Y ↘ Y) = q)
    (hY : IsUnit (N : Γ(Y, ⊤))) (hdiag : finiteP1DiagonalProperty A N hA t d Y hY) :
    ∃ adj : R(q)_![ModuleCat.{u + 1} A] ⊣
        ordinaryFiniteTwistedPullback A q ((ordinaryFiniteLine A N hA X)⟦(2 : ℤ)⟧),
      adj.counit = presentedFiniteP1Counit A N hA t q e w hY (d Y hY)
```

The body is proved by the kernel adjunction, coefficient normalization, counit
trace change and proper projection comparison. Private helpers and local proof
commands support this proof; no statement or shared definition changes.

## Users

`tools/downstream.py --uses` finds only the item itself and the direct consumer
below mentioning this declaration; `--direct` confirms that this is its sole
direct importing module. The consumer compiled unchanged against this proof; the paired check accepted
the item (43.1 s) and consumer (47.7 s).

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.SixFunctors.ProjectiveLineTraceAdjunction | D3 | Same public statement/import; complete proof. |
| Sheaf.SixFunctors.ProjectiveLineExceptionalBaseChange | Not listed in local claim records | Same interface; unchanged consumer check. |

## Status

landed 20261026T222612-L-673395 2026-10-26 (merge of deliver/D3/Sheaf.SixFunctors.ProjectiveLineTraceAdjunction)
