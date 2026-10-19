# integralTowerFiniteComplex, integralTowerComplex, integralTowerResolutionIso

## Reason

The legacy and unrestricted interfaces compute the same termwise scalar reductions.
Comparing their independently expanded complex records repeatedly unfolds the completed
coefficient limit and sheafification constructions, causing the proof file to exceed
its per-file compile limit. Reuse the canonical unrestricted complex abbreviations
instead of reconstructing their records. Their source category, target category,
differentials and maps are identical. In particular the original and unrestricted
ordinary scalar-extension witnesses are applications of the same theorem to the same
coefficient projection; proof irrelevance identifies their chosen functors.

The resolution computation now also directly reuses `unrestrictedTowerResolutionIso`.
This is the same canonical computation. Write e_X for quotientCompQhIso.app X,
f = Q(q), and g = Qh(quotient(q)). Naturality says
f ≫ e_K.inv = e_P.inv ≫ g. Since q is a quasi-isomorphism, both f and g
are invertible, giving e_K.inv ≫ inv g = inv f ≫ e_P.inv. Applying the
chosen derived functor and then composing with its K-flat counit and the target
quotient comparison gives equality of the old and new resolution formulas.
The ordinary and derived witnesses are the same specializations, so their functors
and counits agree by proof irrelevance. This refactoring therefore preserves the
canonical comparison used by the theorem; no arbitrary comparison is substituted.

All existing argument lists and universes are retained. This requires making the
unrestricted interface import public, since public abbreviation bodies use it.
No theorem statement changes. Target semantic review is reopened for this definition
refactoring, with the same complexes and no changed mathematical assumptions.

## Old

```lean
noncomputable abbrev integralTowerFiniteComplex (n : ℕ)
    (P : CochainComplex (completedIntegralModuleSheaves l E Y D hl) ℤ) :=
  ((integralReductionChangeOfRings l E Y D hl n).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj P

noncomputable abbrev integralTowerComplex (n : ℕ)
    (P : CochainComplex (completedIntegralModuleSheaves l E Y D hl) ℤ) :=
  ((completedIntegralRestrictScalars l E Y D hl n).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj (integralTowerFiniteComplex l E Y D hl n P)

noncomputable def integralTowerResolutionIso (n : ℕ)
    {P K : CochainComplex (completedIntegralModuleSheaves l E Y D hl) ℤ}
    (q : P ⟶ K)
    (hq : CochainComplex.IsKFlatResolutionIndependentCoefficients
      (J := AlgebraicGeometry.Scheme.ProEt.topology Y)
      (R := completedIntegralCommRingSheaf l E Y D hl) q) :
    (integralDerivedReduction l E Y D hl n).obj (DerivedCategory.Q.obj K) ≅
      DerivedCategory.Q.obj (integralTowerFiniteComplex l E Y D hl n P) :=
  (integralDerivedReduction l E Y D hl n).mapIso
      ((DerivedCategory.quotientCompQhIso _).app K).symm ≪≫
    integralDerivedReductionResolutionIso l E Y D hl n q hq ≪≫
    DerivedCategory.Qh.mapIso
      (((integralReductionChangeOfRings l E Y D hl n).mapHomotopyCategoryFactors
        (ComplexShape.up ℤ)).app P) ≪≫
    (DerivedCategory.quotientCompQhIso
      (SheafOfModules.{max u (t + 1)} (integralCoefficientSheaf l E Y n))).app
        (integralTowerFiniteComplex l E Y D hl n P)
```

## New

```lean
noncomputable abbrev integralTowerFiniteComplex (n : ℕ)
    (P : CochainComplex (completedIntegralModuleSheaves l E Y D hl) ℤ) :=
  unrestrictedTowerFiniteComplex l E Y n P

noncomputable abbrev integralTowerComplex (n : ℕ)
    (P : CochainComplex (completedIntegralModuleSheaves l E Y D hl) ℤ) :=
  unrestrictedTowerComplex l E Y n P

noncomputable def integralTowerResolutionIso (n : ℕ)
    {P K : CochainComplex (completedIntegralModuleSheaves l E Y D hl) ℤ}
    (q : P ⟶ K)
    (hq : CochainComplex.IsKFlatResolutionIndependentCoefficients
      (J := AlgebraicGeometry.Scheme.ProEt.topology Y)
      (R := completedIntegralCommRingSheaf l E Y D hl) q) :
    (integralDerivedReduction l E Y D hl n).obj (DerivedCategory.Q.obj K) ≅
      DerivedCategory.Q.obj (integralTowerFiniteComplex l E Y D hl n P) :=
  unrestrictedTowerResolutionIso l E Y n q hq
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.IntegralReductionTowerWellDefined | W5 | Reuse canonical complex records in the two existing theorems. |
| Sheaf.Paper.IntegralReductionTower | unclaimed | Same complexes and canonical maps; no source change. |

The remaining importers do not mention these abbreviations directly. No consumer's
statement changes its meaning, and no forced adaptation is required.

## Status

landed 20261019T192853-L-1878430 2026-10-19 (merge of deliver/W5/Sheaf.Paper.IntegralReductionTowerWellDefined)
