# boundedConstructibleBaseChange

## Reason

Direct concrete expansion of the unit–square–counit implementation repeatedly exhausted the
kernel heartbeat budget (including the 50,000-heartbeat diagnostic probe) and exceeded the
60-second file limit with the default budget. The generic calculation itself compiles.
Represent the same map by its adjoint so its adjunct uses an equivalence inverse law.
Keep the original `@[no_expose]` setting: exposing the body caused ProperApp to time out,
while its unchanged baseline compiled. Supply ordinary proved equations as the public API,
rather than a reflexivity/definitional-equation lemma requiring body exposure. This is a
representation change, not a different base-change transformation.

The adapted source module MorphismDefs is unclaimed. No module held by another group is edited.
The new generic construction and all its properties are proved; no sorry is added.

## Old

```lean
@[no_expose]
noncomputable def boundedConstructibleBaseChange (sq : CommSq g' f' f g) :
    boundedConstructibleLowerStar Λ ℓ k f ⋙ boundedConstructibleUpperStar Λ ℓ k g ⟶
      boundedConstructibleUpperStar Λ ℓ k g' ⋙ boundedConstructibleLowerStar Λ ℓ k f' :=
  boundedConstructibleBaseChangeUnitStep Λ ℓ k f g f' ≫
    (boundedConstructibleBaseChangeSquareStep Λ ℓ k sq).hom ≫
      boundedConstructibleBaseChangeCounitStep Λ ℓ k f f' g'
```

## New

```lean
@[no_expose]
noncomputable def boundedConstructibleBaseChange (sq : CommSq g' f' f g) :
    boundedConstructibleLowerStar Λ ℓ k f ⋙ boundedConstructibleUpperStar Λ ℓ k g ⟶
      boundedConstructibleUpperStar Λ ℓ k g' ⋙ boundedConstructibleLowerStar Λ ℓ k f' :=
  Adjunction.squareExchange
    (boundedConstructibleUpperStarLowerStarAdjunction Λ ℓ k f)
    (boundedConstructibleUpperStarLowerStarAdjunction Λ ℓ k f')
    (boundedConstructibleUpperStar Λ ℓ k g)
    (boundedConstructibleUpperStar Λ ℓ k g')
    (boundedConstructiblePullbackSquareComparison Λ ℓ k sq)
```

The source module adds a public import of `Sheaf.CategoryTheory.AdjunctionSquareExchange` and
the proved theorems `boundedConstructibleBaseChange_eq_squareExchange`,
`boundedConstructibleBaseChange_adjunct` and
`boundedConstructibleBaseChange_eq_unit_square_counit`. The latter states
literal equality of the new transformation with the old defining composite. The generic module
constructs the exchange by `homEquiv`, proves naturality, its adjunct formula, and equality with
the three-step construction. Existing signatures, universes, public visibility and hypotheses stay identical.
The implementation-exposure attribute `@[no_expose]` is preserved. The equation identifying
exchange with the new constructor is a propositional consequence of the two proved equalities
with the original composite. This avoids exporting a reflexivity/definitional-equation lemma,
which Lean disallows for hidden definitions. The adjunct lemma uses this public equation and
keeps concrete bounded functors locally irreducible during matching. Those local attributes
are not exported on the functors.

## Users

`tools/downstream.py ... --uses boundedConstructibleBaseChange` reports the following 15
textual users (56 modules transitively downstream at the time of checking). The equality theorem
shows their statements retain exactly the same meaning, including the fixed target statements.
The definition change should receive the usual target-definition review, with this equality as
the evidence of semantic preservation.

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.Paper.CondensedQbarBaseChangeCompatibility` | unclaimed | Same transformation by proved equality; no source adaptation required |
| `Sheaf.Paper.CondensedQbarExchangeEquality` | A3 | Same transformation by proved equality; no source adaptation required |
| `Sheaf.Paper.ContinuousExchangeIntegralModel` | unclaimed | Same transformation by proved equality; no source adaptation required |
| `Sheaf.Paper.ContinuousIntegralExchangeEquality` | unclaimed | Same transformation by proved equality; no source adaptation required |
| `Sheaf.Paper.ContinuousIntegralExchangeSourceAdjunct` | E4 | Proof completed; signature unchanged |
| `Sheaf.Paper.ContinuousIntegralExchangeSquare` | unclaimed | Same transformation by proved equality; no source adaptation required |
| `Sheaf.Paper.ContinuousIntegralExchangeTargetAdjunct` | F1 | Same transformation by proved equality; no source adaptation required |
| `Sheaf.Paper.FiniteDiscreteExchangeComparison` | unclaimed | Same transformation by proved equality; no source adaptation required |
| `Sheaf.Paper.IntegralExchangeReduction` | unclaimed | Same transformation by proved equality; no source adaptation required |
| `Sheaf.Paper.IntegralFiniteExchangeComparison` | unclaimed | Same transformation by proved equality; no source adaptation required |
| `Sheaf.Paper.IntegralResidueExchange` | C2 | Same transformation by proved equality; no source adaptation required |
| `Sheaf.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperApp` | unclaimed | Same transformation by proved equality; no source adaptation required |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriekDefs` | unclaimed | Same transformation by proved equality; no source adaptation required |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.MorphismDefs` | unclaimed | Definition presentation and equality API changed; signature unchanged |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.Proper` | unclaimed | Same transformation by proved equality; no source adaptation required |

No forced adaptations. The import-direction check permits MorphismDefs to import the generic
Sheaf module; the latter imports only Mathlib adjunctions and the independent SquareTransport
module.

## Status

landed 20261016T040743-L-2515722 2026-10-16 (merge of deliver/E4/Sheaf.Paper.ContinuousIntegralExchangeSourceAdjunct)
