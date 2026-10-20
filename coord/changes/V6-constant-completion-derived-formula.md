# CategoryTheory.ConstantCompletion.derivedReductionTowerComparison

## Reason

Kernel checking of the long representative-computation equation repeatedly unfolded the
concrete functors while matching the intermediate objects. The assigned module then
crossed its compile limit. State that same equation using the generic, fully constructed
predicate `DerivedTowerComparisonFormula`, in the same module. Its body is exactly the
original equation, with abstract functors in place of the concrete functors. This changes
neither hypotheses nor conclusion: unfolding the predicate gives the old statement.
There is no new proof assumption or `sorry`. No target statement changes.

## Old

```lean
theorem derivedReductionTowerComparison (J : GrothendieckTopology C) (A : Type u)
    [CommRing A] [IsNoetherianRing A] (I : Ideal A) :
    ∃ e : dres (coefficientMap J A I) ⋙ (quotientPresentation J A I false).tower ≅
        (quotientPresentation J A I true).tower ⋙ tdres (coefficientMap J A I),
      ∀ P : Cx (completed J A I), P.IsAcyclicTensorKFlat →
        (∀ q : ℤ, SheafOfModules.IsFlat (P.X q)) →
        (quotientPresentation J A I false).tower.map
            ((resFactors (coefficientMap J A I)).inv.app P) ≫
          (quotientPresentation J A I false).comparison.app
            (((res (coefficientMap J A I)).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ≫
          (TQ (constant J A)).map
            ((reductionTowerComparisonComplex J A I).hom.app P) ≫
          (tresFactors (coefficientMap J A I)).hom.app (reductionComplex J A I true P) =
        e.hom.app ((Q (completed J A I)).obj P) ≫
          (tdres (coefficientMap J A I)).map
            ((quotientPresentation J A I true).comparison.app P) := by
  sorry
```

## New predicate

```lean
def DerivedTowerComparisonFormula
    {A₀ A₁ A₂ A₃ A₄ A₅ A₆ A₇ : Type*}
    [Category A₀] [Category A₁] [Category A₂] [Category A₃]
    [Category A₄] [Category A₅] [Category A₆] [Category A₇]
    {qB : A₀ ⥤ A₄} {qR : A₁ ⥤ A₅} {tqB : A₂ ⥤ A₆} {tqR : A₃ ⥤ A₇}
    {rc : A₀ ⥤ A₁} {tc : A₂ ⥤ A₃} {dr : A₄ ⥤ A₅} {dt : A₆ ⥤ A₇}
    {tr : A₅ ⥤ A₇} {tb : A₄ ⥤ A₆} {redR : A₁ ⥤ A₃} {redB : A₀ ⥤ A₂}
    (α : rc ⋙ qR ≅ qB ⋙ dr) (βR : qR ⋙ tr ⟶ redR ⋙ tqR)
    (γ : rc ⋙ redR ≅ redB ⋙ tc) (δ : tc ⋙ tqR ≅ tqB ⋙ dt)
    (βB : qB ⋙ tb ⟶ redB ⋙ tqB) (e : dr ⋙ tr ≅ tb ⋙ dt) (P : A₀) : Prop :=
  tr.map (α.inv.app P) ≫ βR.app (rc.obj P) ≫ tqR.map (γ.hom.app P) ≫
      δ.hom.app (redB.obj P) = e.hom.app (qB.obj P) ≫ dt.map (βB.app P)
```

## New

```lean
theorem derivedReductionTowerComparison (J : GrothendieckTopology C) (A : Type u)
    [CommRing A] [IsNoetherianRing A] (I : Ideal A) :
    ∃ e : dres (coefficientMap J A I) ⋙ (quotientPresentation J A I false).tower ≅
        (quotientPresentation J A I true).tower ⋙ tdres (coefficientMap J A I),
      ∀ P : Cx (completed J A I), P.IsAcyclicTensorKFlat →
        (∀ q : ℤ, SheafOfModules.IsFlat (P.X q)) →
        DerivedTowerComparisonFormula (resFactors (coefficientMap J A I))
          (quotientPresentation J A I false).comparison (reductionTowerComparisonComplex J A I)
          (tresFactors (coefficientMap J A I))
          (quotientPresentation J A I true).comparison e P := by
  sorry
```

## Users

A complete Lean-source search and `tools/downstream.py` both find only the declaration
itself. No consumer needs adaptation; in particular no source-library declaration is
changed. A standalone Lean conversion check assigns the new statement directly to the original
statement, with no rewriting. It compiled in 11.9 seconds.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.ConstantCompletionEquivalence | V6 | The same representative equation is recorded by a generic predicate. |

## Status

landed 20261020T230839-L-620015 2026-10-20 (merge of deliver/V6/Sheaf.Paper.ConstantCompletionEquivalence)
