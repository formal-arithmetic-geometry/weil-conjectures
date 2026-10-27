# WeilConjectures.ConstructibleExceptionalCoefficients.exists_raw_localized_identity_comparison

## Reason

The previous helper quantified over an arbitrary RawLocalizedAdjunction. Its fields do not
normalize the counit against the given integral adjunction or normalize the left shift.
Even for an identity functor pair on a nonzero characteristic-zero category, negating the
unit and counit produces a different adjunction with the same functors. Identity comparison
components cannot obey the counit equation for both choices. The helper was already marked
STATEMENT-DISPUTED. Zheng, Constructions 6.1 and 6.2, localizes the supplied operations and
adjunction maps; it does not assert normalization for arbitrary adjunction structures.

The corrected helper assumes the localized counit formula and the canonical left comparison's
shift compatibility. Both are proved for the actual localization construction in this delivery.
The original existential parent theorem, its functors, and all endpoint shifts stay unchanged.
The helper's right comparison shift condition is proved by the mate formula, not assumed.

## Old

```lean
theorem exists_raw_localized_identity_comparison
    (A : Operation.{u, v} l Ω X Y (.integral E))
    [A.F.Additive] [A.G.Additive]
    [A.F.Linear (Padic.coefficientExtensionIntegers l E.carrier)]
    [A.G.Linear (Padic.coefficientExtensionIntegers l E.carrier)]
    (hX : sfIntegralConstructible l E.carrier X = finiteTorConstructibleIntegral l E.carrier X)
    (hY : sfIntegralConstructible l E.carrier Y = finiteTorConstructibleIntegral l E.carrier Y)
    (R : RawLocalizedAdjunction l Ω E X Y A hX hY) :
    ∃ (q : CounitFieldComparison.{u, v} l Ω A (R.operation l Ω E)
        (rationalization.{u, v} l Ω E X) (rationalization.{u, v} l Ω E Y)),
      (∀ K, HEq (q.q.hom.app K)
        (𝟙 ((rationalization.{u, v} l Ω E Y).obj (A.F.obj K)))) ∧
      (∀ M, HEq (q.b.hom.app M)
        (𝟙 ((rationalization.{u, v} l Ω E X).obj (A.G.obj M)))) ∧
      q.shiftX = integralRationalizationShift l Ω E X ∧
      q.shiftY = integralRationalizationShift l Ω E Y
```

## New

```lean
theorem exists_raw_localized_identity_comparison
    (A : Operation.{u, v} l Ω X Y (.integral E))
    [A.F.Additive] [A.G.Additive]
    [A.F.Linear (Padic.coefficientExtensionIntegers l E.carrier)]
    [A.G.Linear (Padic.coefficientExtensionIntegers l E.carrier)]
    (hX : sfIntegralConstructible l E.carrier X = finiteTorConstructibleIntegral l E.carrier X)
    (hY : sfIntegralConstructible l E.carrier Y = finiteTorConstructibleIntegral l E.carrier Y)
    (R : RawLocalizedAdjunction l Ω E X Y A hX hY)
    (hc : ∀ M, (rawRationalComparison l Ω E A.F hX).hom.app (A.G.obj M) ≫
      (rawRationalFunctor l Ω E X Y A.F hX).map
        ((rawRationalComparison l Ω E A.G hY).hom.app M) ≫
      R.adjunction.counit.app ((rationalization.{u, v} l Ω E Y).obj M) =
        (rationalization.{u, v} l Ω E Y).map (A.adjunction.counit.app M))
    (hq : letI := integralRationalizationShift l Ω E X
          letI := integralRationalizationShift l Ω E Y
          letI := A.leftShift
          letI := R.leftShift
          NatTrans.CommShift (rawRationalComparison l Ω E A.F hX).hom ℤ) :
    ∃ (q : CounitFieldComparison.{u, v} l Ω A (R.operation l Ω E)
        (rationalization.{u, v} l Ω E X) (rationalization.{u, v} l Ω E Y)),
      (∀ K, HEq (q.q.hom.app K)
        (𝟙 ((rationalization.{u, v} l Ω E Y).obj (A.F.obj K)))) ∧
      (∀ M, HEq (q.b.hom.app M)
        (𝟙 ((rationalization.{u, v} l Ω E X).obj (A.G.obj M)))) ∧
      q.shiftX = integralRationalizationShift l Ω E X ∧
      q.shiftY = integralRationalizationShift l Ω E Y
```

The new `rawRationalComparison` has literal identity components on the two composites;
its object and arrow components are fixed by the tensor construction. It makes no choice
of adjunction or functor data.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.ExceptionalIntegralAdjunctionLocalization | C4 | The only caller proves both normalization hypotheses using Adjunction.localization. |
| Sheaf.Paper.ExceptionalScalarMateLocalization | unclaimed in inspected snapshot | Sole direct importer; uses RawLocalizedAdjunction and CounitFieldComparison, whose types and definitions are unchanged; no use of the repaired helper. |

No target statement uses the changed helper or the new comparison definition. Existing
public definitions and instance signatures are unchanged. The direct importer is compiled
against this repair before delivery.

## Status

landed 20261027T180508-L-3867217 2026-10-27 (merge of deliver/C4/Sheaf.Paper.ExceptionalIntegralAdjunctionLocalization)
