# WeilConjectures.zlPullComp_existsUnique

## Reason

The remaining `zlPullComp_existsUnique` obligation descends the normalized integral
compositor through rationalization and the common-stage quotient. The proof uses
explicit representatives and equality-only copies of the prescribed pullback
functors. The compatibility with enlargement of a coefficient stage is isolated
as a strictly smaller theorem in a new module.

## Old

```lean
theorem zlPullComp_existsUnique {X Y Z : Scheme.{u}}
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    [∀ z : Z, Invertible (l : Z.residueField z)] (f : X ⟶ Y) (g : Y ⟶ Z) :
    ∃! e : commonStageDerivedPullback l Ω (f ≫ g) ≅
        commonStageDerivedPullback l Ω g ⋙ commonStageDerivedPullback l Ω f,
      ∀ (L : AlgebraicallyClosedCoefficients.Index l Ω)
        (K : sfIntegralConstructibleCategory l
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) Z),
        e.hom.app ((GeneralAlgebraicallyClosedCoefficients.inclusion L).obj
            ((sfRationalConstructibleLocalization l _ Z).obj K)) ≫
          (commonStageDerivedPullback l Ω f).map (zlStagePullIso l Ω g L K).hom ≫
          (zlStagePullIso l Ω f L ((constructibleIntegralPullback l _ g).obj K)).hom =
        (zlStagePullIso l Ω (f ≫ g) L K).hom ≫
          (GeneralAlgebraicallyClosedCoefficients.inclusion L).map
            ((sfRationalConstructibleLocalization l _ X).map
              ((zlIntegralPullComp l _ f g).hom.app K)) := by
  sorry
```

## New

The existing theorem's signature and all existing public definition bodies are
unchanged. Its proof privately imports `Sheaf.Paper.CommonStagePullbackCompNaturality`.
That module proves `commonStagePullbackIntegralObject`, constructs
`commonStagePullbackCompComponent` from the actual normalized integral comparison,
proves `commonStagePullbackCompComponent_heq`,
and leaves `commonStagePullbackCompComponent_naturality` as one sourced theorem.
The item assembles these components, verifies the integral component equation,
and proves uniqueness. Normal transparency checking for the proof prefix avoids
unnecessary expansion of large chosen functors. The composition proof locally
keeps chosen functors irreducible; its formula application supplies explicit
universes and the literal pair, preventing repeated coefficient reconstruction. No target changes meaning.

## Users

`tools/downstream.py Sheaf.Paper.WeilIndSheafCategory --uses
WeilConjectures.zlPullComp_existsUnique` lists only the assigned module as a direct
declaration user. The import closure has 1040 modules, all with unchanged public
signatures, imports and definitions. No consumer needs adaptation.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.WeilIndSheafCategory | C1 | Assemble and uniquely characterize the normalized compositor. |
| Sheaf.Paper.CommonStagePullbackCompNaturality | new C1 module | Construct normalized components; state their naturality. |

## Status

landed 20261025T180506-L-3995116 2026-10-25 (merge of deliver/C1/Sheaf.Paper.WeilIndSheafCategory)
