# cechComparisonSystem_comparison_connecting

## Reason
The former theorem quantified over an arbitrary degreewise family of natural transformations and asserted a connecting identity that does not follow from its hypotheses. The corrected interface accepts a `CechComparisonSystem`, whose `connecting` field carries exactly the required compatibility law. The dependent existence caller is adapted because it can no longer derive that field from an arbitrary comparison family via the corrected projection theorem.

## Old
```lean
theorem cechComparisonSystem_comparison_connecting
    {X : Scheme.{u}} {ι : Type u} (U : ι → X.Opens) (hcover : iSup U = ⊤)
    (comparison : ∀ q, TopCat.Sheaf.cechCohomologyFunctor U q ⟶
      Sheaf.functorH (Opens.grothendieckTopology X) q)
    (q : ℕ) (T : ShortComplex
      (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}))
    (hT : T.ShortExact)
    (hg : ∀ (k : ℕ) (y : Fin (k + 1) → ι),
      Function.Surjective (T.g.hom.app (op (⨅ l, U (y l))))) :
    TopCat.Sheaf.cechδ U hT hg q ≫ (comparison (q + 1)).app T.X₁ =
      (comparison q).app T.X₃ ≫ Sheaf.functorHδ hT q
```

## New
```lean
theorem cechComparisonSystem_comparison_connecting
    {X : Scheme.{u}} {ι : Type u} (U : ι → X.Opens) (hcover : iSup U = ⊤)
    (c : CechComparisonSystem U hcover)
    (q : ℕ) (T : ShortComplex
      (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}))
    (hT : T.ShortExact)
    (hg : ∀ (k : ℕ) (y : Fin (k + 1) → ι),
      Function.Surjective (T.g.hom.app (op (⨅ l, U (y l))))) :
    TopCat.Sheaf.cechδ U hT hg q ≫ (c.comparison (q + 1)).app T.X₁ =
      (c.comparison q).app T.X₃ ≫ Sheaf.functorHδ hT q
```

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.Cohomology.CechComparisonSystemExistence | B3 | Forced adaptation: its old proof applied the removed arbitrary-family interface; the construction remains a named sorry until a compatible system existence proof is supplied. |

## Status

landed 20261012T213848-L-1208054 2026-10-12 (merge of deliver/F2/Sheaf.AlgebraicGeometry.Cohomology.CechComparisonSystemConnecting)

## Forced adaptations

The original `CechComparisonSystemExistence.lean` fails against the corrected
Connecting module because its call passes `comparison` where the new theorem requires
`c : CechComparisonSystem U hcover`. Removing that construction and the now-unused
import is the complete forced adaptation; the public existence signature is unchanged.
