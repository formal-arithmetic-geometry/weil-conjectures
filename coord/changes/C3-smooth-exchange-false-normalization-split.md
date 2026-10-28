# WeilConjectures.SmoothExchangeScalarCompatibility.normalizedExchangeData

## Reason

Withdraw the false normalization split, and reopen the original theorem with exactly
its former statement and unchanged `Conclusion`. The split asserts `Data D C f d S`
for every supplied `System S`. `Data` includes `FiniteRightNormalized`, whereas
`RingSystem.finiteRight` is an arbitrary natural isomorphism. No other field of
`RingSystem`, `FieldSystem`, `CommonSystem`, or `RefinementSystem` constrains it.
Thus the split asserts a normalization not entailed by the supplied system.

For the identity on Spec(k), with geometric characteristic 2 and coefficient prime 3,
negating a finite-right realization changes the transpose identity on the nonzero
finite coefficient unit, while leaving every other system field unchanged. The two
realizations cannot both be the specified Hom transpose. A Lean probe checks that
replacing `finiteRight` by any natural isomorphism with its endpoints preserves the
entire system, without changing its operations or other fields. This is a false
auxiliary assertion, not a reason to weaken the original exchange statement.

The replacement probe compiled in 12.3 seconds, with no sorry or warning. With the
same Arrow section variables as the item, its complete assertion and proof are:

```lean
private theorem replaceFiniteRight
    (ρ : ∀ (c : Compactification f)
      (E : ConstructibleExceptionalCoefficients.FieldStage C.l) (n : ℕ+),
      (S.ring.operation c (.finite E n)).G ⋙
          ConstructibleExceptionalCoefficients.RingStage.inclusion C.l C.Qbar X (.finite E n) ≅
        ConstructibleExceptionalCoefficients.RingStage.inclusion C.l C.Qbar Y (.finite E n) ⋙
          @ProEtale.sfFiniteExceptional (Padic.coefficientExtensionRing C.l E.carrier n) _
            (Padic.finite_coefficientExtensionRing C.l E.carrier n n.pos) X Y f c) :
    ∃ S' : ConstructibleExceptionalCoefficients.System C.l C.Qbar D C.different (f := f),
      S'.ring.operation = S.ring.operation ∧ HEq S'.ring.finiteRight ρ := by
  exact ⟨{
    ring := { S.ring with finiteRight := ρ }
    fields := {
      rationalizationComparison := S.fields.rationalizationComparison
      rationalization_normalized := S.fields.rationalization_normalized
      rationalComparison := S.fields.rationalComparison
      rational_normalized := S.fields.rational_normalized
      rationalCocycle := S.fields.rationalCocycle
      rationalIdentityLeft := S.fields.rationalIdentityLeft
      rationalIdentityRight := S.fields.rationalIdentityRight }
    common := {
      commonComparison := S.common.commonComparison
      common_normalized := S.common.common_normalized
      commonCocycleLeft := S.common.commonCocycleLeft
      commonCocycleRight := S.common.commonCocycleRight }
    refinements := {
      refinement := S.refinements.refinement
      refinement_normalized := S.refinements.refinement_normalized
      refinementRational := S.refinements.refinementRational
      refinementCommon := S.refinements.refinementCommon
      refinementIdentity := S.refinements.refinementIdentity
      refinementComposition := S.refinements.refinementComposition } }, rfl, HEq.rfl⟩
```

The new direct scalar lemmas avoid that extra condition altogether. The forward
square is `rationalIso_scalar`, its inverse follows by cancellation, and the
exceptional unit/tower equations are fields of the supplied system. None selects
data from mere existence or adds a new sorry.

## Old

```lean
theorem normalizedExchangeData
    (sq : u ≫ f = f' ≫ v)
    [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated f'] [LocallyOfFiniteType f'] [QuasiCompact f']
    [SmoothOfRelativeDimension d f']
    (S : ConstructibleExceptionalCoefficients.System C.l C.Qbar D C.different (f := f))
    (S' : ConstructibleExceptionalCoefficients.System C.l C.Qbar D C.different (f := f')) :
    ∃ (I : AdicPurityScalarNaturality.Data D C f d S)
      (I' : AdicPurityScalarNaturality.Data D C f' d S')
      (R : RationalPurityExchangeEndpoints.LocalizedFamily D C f d S I)
      (R' : RationalPurityExchangeEndpoints.LocalizedFamily D C f' d S' I')
      (hEnds : RationalPurityExchangeEndpoints.EndpointEquations
        D C u f f' v d S S' I I' R R')
      (hCanonical : ∀ (E : AdicPurityScalarNaturality.Field D C)
        (K : RCat D C E Y),
        (R.gamma E).app K = gamma D C f S d E K)
      (hCanonical' : ∀ (E : AdicPurityScalarNaturality.Field D C)
        (K : RCat D C E Y'),
        (R'.gamma E).app K = gamma D C f' S' d E K)
      (m : ∀ E : AdicPurityScalarNaturality.Field D C,
        RationalPurityExchangeEndpoints.endpointA D C u f d S E false ≅
          RationalPurityExchangeEndpoints.endpointB D C f' v d S' E false)
      ,
      (∀ (E : AdicPurityScalarNaturality.Field D C)
        (K : RCat D C E Y),
        (m E).app K = middle D C u f f' v sq d E K)
      ∧ (∀ (E L : AdicPurityScalarNaturality.Field D C) (h : E ≤ L),
        whiskerRight (m E).hom (T D C E L h X') ≫
            (RationalPurityExchangeEndpoints.comparisonB
              D C f' v d S' I' R' E L h false).hom =
          (RationalPurityExchangeEndpoints.comparisonA
            D C u f d S I R E L h false).hom ≫
            whiskerLeft (T D C E L h Y) (m L).hom)
      ∧ (∀ E : AdicPurityScalarNaturality.Field D C,
        ShiftCompatibility
          (RationalPurityExchangeEndpoints.endpointA D C u f d S E false)
          (RationalPurityExchangeEndpoints.endpointB D C f' v d S' E false)
          (RationalPurityExchangeEndpoints.shiftA D C u f d S I R E false)
          (RationalPurityExchangeEndpoints.shiftB D C f' v d S' I' R' E false)
          (m E)) := by
  sorry
```

The parent `smoothExchangeScalarCompatibility` was proved by applying this split and
the private `assembleExchange` paste. Its statement was:

```lean
theorem smoothExchangeScalarCompatibility (cartesian : IsPullback u f' f v) :
    ∃ g : TwistedPullbackScalars.Geometry D C f f' d,
      Conclusion D C u f f' v d cartesian.w g
```

Public import: `Sheaf.Paper.RationalPurityExchangeEndpoints`.

## New

`normalizedExchangeData` is removed. Its DAG node is retained with `lean: null` and a
withdrawal explanation. The parent theorem has the identical statement displayed
above and a whole-proof `sorry`; this is an honest reopening, not a claimed proof.
Its existing `STATEMENT-DISPUTED` explanation is retained.

Removed the now unused private `assembleExchange`, `pasteScalar`, and `pasteShift`.
Replaced the endpoint public import by `Sheaf.Paper.RationalScalarComparisonData`,
which supplies the scalar coordinate declarations still used by the unchanged
public statements and definitions.

Added `gamma_scalar`, `gamma_scalar_inv`, `b_unit`, and `b_tower`, all proved
without sorry. These names are attached to the parent's Lean record. The existing
`gamma`, `middleFunctor`, `middle`, `exchange`, `betaA`, `betaB`, `aShift`, `bShift`,
`Conclusion`, and target statements are unchanged.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.Paper.SmoothExchangeScalarCompatibility` | C3 | Removes the sole caller of the false split and reopens the exact original theorem. |

Source search finds no other Lean importer of this module and no other caller of
`normalizedExchangeData`. The split node has only the parent node as a citer and is
not a unit statement or unit proof step; the parent dependency is removed in this
packet. No unrelated or adopted source-library module changes. Targets that depend
on these definitions need no semantic rereview: every existing definition and target
statement remains identical. The removed public re-export has no current consumer.

## Status

landed 20261028T055623-L-778619 2026-10-28 (merge of deliver/C3/Sheaf.Paper.SmoothExchangeScalarCompatibility)
