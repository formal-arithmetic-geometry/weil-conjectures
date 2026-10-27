# WeilConjectures.IntegralExceptionalMapping.totalHom

## Reason

Name the explicit total mapping class of an actual normalized system morphism,
so the middle enriched transpose can be separated from the proved outer
reconstruction cancellations. The construction uses real functors and maps.

## Old

No previous declaration; no existing definition or signature changes.

## New

```lean
def totalHom {l : ℕ} [Fact l.Prime] {E : Type u} [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] {W : Scheme.{u}}
    (S : CoefficientDerivedSystemCalculus l E W)
    (P N : coefficientSequenceDerived l E W)
    (hN : IsNormalizedCoefficientSequence l E W N)
    [IsIso (S.adjunction.counit.app P)] (b : P ⟶ N) :
    (DerivedCategory.homologyFunctor AddCommGrpCat.{u+1} 0).obj
      (coefficientMappingLimit.{u+1}.obj
        ((coefficientSequenceGlobalHom l E W).obj (op P, N))) :=
  (DerivedCategory.homologyFunctor AddCommGrpCat.{u+1} 0).map
    ((S.gamma l E W ((coefficientSequenceLimit l E W).obj P) N hN).hom ≫
      coefficientMappingLimit.{u+1}.map
        ((coefficientSequenceGlobalHom l E W).map
          (Prod.mkHom (inv (S.adjunction.counit.app P)).op (𝟙 N))))
    ((coefficientIntegralHomEquiv l E W _ _).symm
      ((coefficientSequenceLimit l E W).map b))
```

The accompanying systemTotalEnrichedTranspose theorem records its compatibility
with the specified system adjunction. No data are obtained from that theorem.

## Users

The definition is new and has no existing consumers in the shared source tree.

| module | group holding it | effect |
|---|---|---|
| Sheaf.SixFunctors.SystemTotalEnrichedTranspose | X5, new module in this delivery | Explicit construction and system transpose statement. |
| Sheaf.SixFunctors.IntegralExceptionalDescendedCounit | X5 | Private proof import; original statements and definitions unchanged. |

No forced adaptations and no target-statement or target-definition changes.

## Status

landed 20261026T003157-L-151331 2026-10-26 (merge of deliver/X5/Sheaf.SixFunctors.IntegralExceptionalDescendedCounit)
