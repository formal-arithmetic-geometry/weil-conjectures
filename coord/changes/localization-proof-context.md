# AlgebraicGeometry.Scheme.proEtale_ringed_localization_sequence

## Reason

The proof adds private helpers in the Scheme and SheafOfModules namespaces and
opens their required local proof contexts. The interface checker conservatively
records namespace/open/set_option commands even though these module-local commands
do not change the exported theorem type or any definition. This record documents
that command-only difference. No existing statement, universe, binder, visibility,
public import or definition changes; no target statement is affected.

## Old

The original theorem signature is:

```lean
theorem proEtale_ringed_localization_sequence {X Z : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] (U : X.ProEt) [IsOpenImmersion U.hom] [QuasiCompact U.hom]
    (hU : Set.range U.hom = (Set.range i)ᶜ)
    (A : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (ai : proEtaleModuleInverseImage i A ⊣
      (SheafOfModules.pushforward.{u + 1} (F := proEtaleBaseChange i)
      (J := ProEt.topology X) (K := ProEt.topology Z)
      (S := ((sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj A)) (R := ((sheafCompose (ProEt.topology Z)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        ((proEtaleSheafInverseImage i CommRingCat.{u + 1}).obj A)))
      ⟨Functor.whiskerRight
        ((proEtaleSheafAdjunction i CommRingCat.{u + 1}).unit.app A).hom
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})⟩))
    (aj : (SheafOfModules.extensionByZeroPresheaf.{u + 1} ((sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj A) U ⋙
      PresheafOfModules.sheafification (𝟙 ((sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj A).obj)) ⊣
      SheafOfModules.overFunctor.{u + 1} ((sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj A) U) :
    ∀ M, Mono (aj.counit.app M) ∧ Epi (ai.unit.app M) ∧
      (ComposableArrows.mk₂ (aj.counit.app M) (ai.unit.app M)).Exact
```

The original namespace/proof context commands are:

```lean
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
end AlgebraicGeometry.Scheme
```

## New

The theorem signature is identical, verbatim:

```lean
theorem proEtale_ringed_localization_sequence {X Z : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] (U : X.ProEt) [IsOpenImmersion U.hom] [QuasiCompact U.hom]
    (hU : Set.range U.hom = (Set.range i)ᶜ)
    (A : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (ai : proEtaleModuleInverseImage i A ⊣
      (SheafOfModules.pushforward.{u + 1} (F := proEtaleBaseChange i)
      (J := ProEt.topology X) (K := ProEt.topology Z)
      (S := ((sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj A)) (R := ((sheafCompose (ProEt.topology Z)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        ((proEtaleSheafInverseImage i CommRingCat.{u + 1}).obj A)))
      ⟨Functor.whiskerRight
        ((proEtaleSheafAdjunction i CommRingCat.{u + 1}).unit.app A).hom
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})⟩))
    (aj : (SheafOfModules.extensionByZeroPresheaf.{u + 1} ((sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj A) U ⋙
      PresheafOfModules.sheafification (𝟙 ((sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj A).obj)) ⊣
      SheafOfModules.overFunctor.{u + 1} ((sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj A) U) :
    ∀ M, Mono (aj.counit.app M) ∧ Epi (ai.unit.app M) ∧
      (ComposableArrows.mk₂ (aj.counit.app M) (ai.unit.app M)).Exact
```

The delivered proof contexts (including scoped theorem options) are:

```lean
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
end AlgebraicGeometry.Scheme
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
end AlgebraicGeometry.Scheme
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
end AlgebraicGeometry.Scheme
open CategoryTheory CategoryTheory.Limits Opposite
namespace SheafOfModules
set_option linter.style.haveILetI false in
end SheafOfModules
namespace AlgebraicGeometry.Scheme
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
end AlgebraicGeometry.Scheme
```

The two added public theorems live in new modules and have their own DAG nodes.
No existing definition or public theorem signature changes, and no forced
adaptation is necessary. The open-counit proof now uses Mathlib's adjoint-triple
criterion and `SheafOfModules.overPushforwardOverAdj`; no private copy of the
parent module's extension-adjunction construction remains.

## Users

`tools/downstream.py` reports the following downstream modules. Its textual
`--uses` check finds only this module and `ProEtaleRingedOpenClosed` mentioning the
completed theorem; all others depend transitively. Holders below are the claim
files at the time of this check.

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.AlgebraicGeometry.ProEtaleRingedLocalizationSequence` | H1 | proof completed; signature identical |
| `Sheaf.AlgebraicGeometry.NoetherianStratumDetection` | unclaimed | unchanged; imported theorem and definitions retain identical signatures |
| `Sheaf.AlgebraicGeometry.ProEtaleOpenClosedDetection` | unclaimed | unchanged; imported theorem and definitions retain identical signatures |
| `Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed` | unclaimed | unchanged; imported theorem and definitions retain identical signatures |
| `Sheaf.Paper.CondensedCoefficientComparisons` | unclaimed | unchanged; imported theorem and definitions retain identical signatures |
| `Sheaf.Paper.CondensedFinitePresentationDescent` | unclaimed | unchanged; imported theorem and definitions retain identical signatures |
| `Sheaf.Paper.CondensedFlatCoefficientCalculus` | G2 | unchanged; imported theorem and definitions retain identical signatures |
| `Sheaf.Paper.CondensedQbarBaseChangeCompatibility` | unclaimed | unchanged; imported theorem and definitions retain identical signatures |
| `Sheaf.Paper.CondensedQbarComparisons` | unclaimed | unchanged; imported theorem and definitions retain identical signatures |
| `Sheaf.Paper.CondensedQbarExchangeEquality` | A3 | unchanged; imported theorem and definitions retain identical signatures |
| `Sheaf.Paper.CondensedStratumModelAssembly` | A4 | unchanged; imported theorem and definitions retain identical signatures |
| `Sheaf.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperApp` | unclaimed | unchanged; imported theorem and definitions retain identical signatures |
| `TargetsCheck` | unclaimed | unchanged; imported theorem and definitions retain identical signatures |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.CompactSupport` | unclaimed | unchanged; imported theorem and definitions retain identical signatures |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.Proper` | unclaimed | unchanged; imported theorem and definitions retain identical signatures |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit` | unclaimed | unchanged; imported theorem and definitions retain identical signatures |

## Status

landed 20261015T224820-L-2950274 2026-10-15 (merge of deliver/H1/Sheaf.AlgebraicGeometry.ProEtaleRingedLocalizationSequence)
