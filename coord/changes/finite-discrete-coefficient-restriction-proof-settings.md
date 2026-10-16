# finiteDiscreteCoefficientRestrictionForgetIso_linear: local proof elaboration

## Reason

The static interface checker records additions of `open` and `attribute` commands,
including explicitly local attributes. This record documents the proof elaboration commands
added in `Sheaf.Paper.FiniteDiscreteCoefficientRestriction`. No existing public statement,
definition body, universe, visibility or public import changes. All added helpers are private
and proved. No consumer requires adaptation and no target changes meaning.

## Old

The original theorem signature, retained verbatim, is:

```lean
theorem finiteDiscreteCoefficientRestrictionForgetIso_linear
    {S T : Scheme.{u}} (h : S ⟶ T) (N : FiniteDiscreteProEtaleSheaves B S) :
    let M := (lowerStar (Profinite.continuousMapRingObj B) h).obj
      ((finiteDiscreteCoefficientEquivalence B eR G hG S).functor.obj N)
    let P := (finiteDiscreteCoefficientEquivalence B eR G hG T).functor.obj
      ((ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} B)) h).obj N)
    let e := (finiteDiscreteCoefficientRestrictionForgetIso B eR G hG h).app N
    Mod.act M.X ≫ e.hom = (condensedRingObj (Profinite.continuousMapRingObj B) T) ◁
      e.hom ≫ Mod.act P.X
```

The original file had no local semireducibility registration for
`finiteDiscreteCoefficientEquivalence`, no opening of
`CategoryTheory.ConstantInternalModuleSheafEncoding`, and no `proEtMonoidalW` helper.

## New

The same theorem signature now has a complete proof. The new elaboration commands are:

```lean
attribute [local semireducible] finiteDiscreteCoefficientEquivalence
open CategoryTheory.ConstantInternalModuleSheafEncoding
attribute [local instance] proEtMonoidalW
```

`proEtMonoidalW` is a private proved theorem, registered only locally. The namespace opening
and both local registrations affect elaboration of this file only. The proof-only import
`import all Sheaf.Paper.FiniteDiscreteRestrictionEncoding` accesses its existing private
inverse-encoding direct-image construction. None of these proof dependencies is reexported.
The public restriction isomorphism still uses the same additive comparison and the same
linearity theorem, whose proof is the only existing declaration body changed.

## Users

The server's `tools/downstream.py --uses finiteDiscreteCoefficientRestrictionForgetIso_linear`
finds references only inside the item itself. Its full downstream query lists the transitive
consumers below. Holder information
was read from the server's claim files. Every existing public interface and all definitions
used in consumer statements retain their meaning. No consumer is adapted in this delivery. The unchanged direct consumer
`Sheaf.Paper.FiniteDiscreteCoefficientRestrictionCoherence` compiled against the sandbox
item without errors or warnings via `lcompile.py --all` (15.7 seconds for the item and
10.9 seconds for the consumer). The consumer source was kept only in a scratch test tree;
it is not included as an adapted module.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.CoefficientExchangeFromComparisons | C3 | Signatures and meaning unchanged; no adaptation. |
| Sheaf.Paper.FiniteDiscreteCoefficientCoherentPullbacks | unclaimed | Signatures and meaning unchanged; no adaptation. |
| Sheaf.Paper.FiniteDiscreteCoefficientExchange | unclaimed | Signatures and meaning unchanged; no adaptation. |
| Sheaf.Paper.FiniteDiscreteCoefficientPullbackIso | unclaimed | Signatures and meaning unchanged; no adaptation. |
| Sheaf.Paper.FiniteDiscreteCoefficientRestrictionCoherence | unclaimed | Signatures and meaning unchanged; no adaptation. |
| Sheaf.Paper.FiniteDiscreteCoefficientSquareCoherence | B3 | Signatures and meaning unchanged; no adaptation. |
| Sheaf.Paper.FiniteDiscreteDerivedCoefficientData | unclaimed | Signatures and meaning unchanged; no adaptation. |
| Sheaf.Paper.FiniteDiscreteExchangeComparison | unclaimed | Signatures and meaning unchanged; no adaptation. |
| Sheaf.Paper.FiniteDiscreteExchangeRealization | unclaimed | Signatures and meaning unchanged; no adaptation. |
| Sheaf.Paper.IntegralExchangeReduction | unclaimed | Signatures and meaning unchanged; no adaptation. |
| Sheaf.Paper.IntegralFiniteExchangeComparison | unclaimed | Signatures and meaning unchanged; no adaptation. |
| Sheaf.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperApp | unclaimed | Signatures and meaning unchanged; no adaptation. |
| TargetsCheck | unclaimed | Signatures and meaning unchanged; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.CompactSupport | unclaimed | Signatures and meaning unchanged; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.Proper | unclaimed | Signatures and meaning unchanged; no adaptation. |

## Status

landed 20261016T171805-L-1680750 2026-10-16 (merge of deliver/D2/Sheaf.Paper.FiniteDiscreteCoefficientRestriction)
