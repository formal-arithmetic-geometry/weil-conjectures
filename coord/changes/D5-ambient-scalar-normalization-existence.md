# WeilConjectures.ambientQuotientScalarModel_normalization_exists

## Reason

The old theorem was false: it asserted the prescribed tensor-generator normalization
for every realization isomorphism. Take the rank-one constant integral coefficient
object on a nonempty point scheme in residue characteristic different from l and
E = L = Q_l. A normalized realization, if available, can be multiplied by -1.
The generator formula uniquely fixes the strict scalar tower comparison q, while
the resulting Roos equation changes sign on a nonzero completed rank-one object.
Thus both realizations cannot satisfy it. This is a mathematical counterexample,
not a claimed Lean-certified refutation. The earlier J5 scalar-presentation change
record already notes that arbitrary-realization normalization is disputed.

The corrected theorem chooses the realization and its normalization together,
exactly as the scalar-model existence caller requires. The proof constructs this
choice by descent; no hypothesis, definition of normalization, coefficient functor,
unit route or Challenge declaration changes. No new hole or axiom is introduced.

The proof reuses the existing fixedCalculusModels, coherentQuotientModelComparison,
ordinaryQuotientScalarTowerComparison and the descent argument of
PrimitiveQuotientScalarModelExistence. In particular, fixedCalculusModels removes
the need to construct a new calculus or impose scheme-characteristic invertibility.
The complete primitive proof is adapted to the supplied arbitrary scheme and its
calculus; the primitive module and all adopted source files remain untouched.

## Old

```lean
theorem ambientQuotientScalarModel_normalization_exists (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    (ι : E →ₐ[ℚ_[l]] L) (X : Scheme.{t})
    (S : CoefficientDerivedSystemCalculus l E X)
    (ρ : IntegralComparisonRoosModel l L X)
    (realization : integralScalarExtensionOfUniverses l E L ι X ≅
      S.reduction ⋙ integralComparisonDerivedSequenceScalar l E L ι X ⋙
        coefficientSequenceLimit l L X) :
    IsIntegralComparisonScalarNormalized l E L ι X S ρ realization
```

## New

```lean
theorem ambientQuotientScalarModel_normalization_exists (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    (ι : E →ₐ[ℚ_[l]] L) (X : Scheme.{t})
    (S : CoefficientDerivedSystemCalculus l E X)
    (ρ : IntegralComparisonRoosModel l L X) :
    ∃ realization : integralScalarExtensionOfUniverses l E L ι X ≅
        S.reduction ⋙ integralComparisonDerivedSequenceScalar l E L ι X ⋙
          coefficientSequenceLimit l L X,
      IsIntegralComparisonScalarNormalized l E L ι X S ρ realization
```

## Users

The downstream name scan finds only the theorem itself and the following sole
consumer. The consumer is also the sole direct importer. Its statement and
visibility are identical; only its proof and a private import change. Its original
application expects the removed realization argument, so the repair replaces that
application by destructuring the existential and packaging its two fields. Its DAG
proof now cites only the jointly normalized existence result. The separate
AmbientQuotientScalarRealizationExistence item is held by D6 and is not edited.
Its only current import and only DAG parent edge are removed by this delivery.
All remaining transitive importers use the unchanged model-existence interface.
No target-meaning review is reopened: all target statements and their definitions
are unchanged; this repairs a false auxiliary theorem used to construct proof data.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.AmbientQuotientScalarNormalizationExistence | D5 | Correct the false universal claim to jointly normalized existence and give the complete descent proof. |
| Sheaf.Paper.AmbientQuotientScalarModelExistence | unclaimed on the server at inspection | Preserve its signature; consume the chosen normalized realization and remove the obsolete private realization-existence import. |

## Status

landed 20261027T233856-L-4128331 2026-10-27 (merge of deliver/D5/Sheaf.Paper.AmbientQuotientScalarNormalizationExistence)
