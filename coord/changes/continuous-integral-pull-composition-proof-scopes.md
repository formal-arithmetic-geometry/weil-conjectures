# ContinuousIntegralPullComposition proof scopes

## Reason

The static interface detector records new `variable`, `open`, `universe`, and local
attribute commands as a scope-command change. These commands support proved private
helpers for the existing composition-coherence theorem. This record documents that
conservative classification; there is no existing definition or theorem signature change.
The K-injective preservation instance is registered only locally within `section Underived`.
No target meaning or target statement changes.

## Old

The original module had the following proof setup, verbatim:

```lean
@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing
open Scheme
variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E]
  [NormedAlgebra ℚ_[ℓ] E] (k : Type u) [Field k]
  [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
```

The sole theorem `integralConstructiblePullIso_comp` ended with `:= by sorry`.
There was no local K-injective preservation helper.

## New

The same public section, scheme namespace, coefficient variables, theorem signature,
and public import remain. Generic private helper sections introduce functor and adjunction
variables, then close before the original theorem. Their `include` and `omit` commands affect
only the following private lemmas. `set_option backward.defeqAttrib.useBackward true`
selects elaboration behavior within this file. Two single-declaration heartbeat settings
allow repeated exactness instance inference and do not change the 60-second compile limit.

The added K-injective helper and registration are, verbatim:

```lean
private lemma lowerStar_preservesKInjectives
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {S T : Scheme.{u}} (h : S ⟶ T) :
    (h)_*⟦Λ⟧.PreservesKInjectiveComplexes :=
  (upperStarLowerStarAdjunction Λ h).preservesKInjectiveComplexes

attribute [local instance] lowerStar_preservesKInjectives
```

This registration is inside `section Underived`, ending before the bounded-category
helper and the original public theorem. It creates no global instance registration.
All new declarations are private and proved; the one private comparison definition is
an explicit composite of existing canonical isomorphisms. The original theorem now has
a complete proof, with its statement unchanged.

## Users

`tools/downstream.py Sheaf.Paper.ContinuousIntegralPullComposition --uses
integralConstructiblePullIso_comp` found eight downstream modules. Only
`Sheaf.Paper.ContinuousIntegralExchangeTargetAdjunct` mentions the existing theorem.
No user requires adaptation because the statement, visibility, and public imports are unchanged.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.ContinuousIntegralExchangeTargetAdjunct | unclaimed | No adaptation: every existing declaration and public import is unchanged. |
| Sheaf.Paper.ContinuousExchangeIntegralModel | unclaimed | No adaptation: every existing declaration and public import is unchanged. |
| Sheaf.Paper.ContinuousIntegralExchangeEquality | unclaimed | No adaptation: every existing declaration and public import is unchanged. |
| Sheaf.Paper.ContinuousIntegralExchangeSquare | unclaimed | No adaptation: every existing declaration and public import is unchanged. |
| Sheaf.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperApp | unclaimed | No adaptation: every existing declaration and public import is unchanged. |
| TargetsCheck | unclaimed | No adaptation: every existing declaration and public import is unchanged. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.CompactSupport | unclaimed | No adaptation: every existing declaration and public import is unchanged. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.Proper | unclaimed | No adaptation: every existing declaration and public import is unchanged. |

The delivery item itself is held by C2. It changes only its proof and private proof setup.
The unchanged direct consumer was compiled against the new module in 29.4 seconds.
The theorem axiom check reports only `propext`, `Classical.choice`, and `Quot.sound`.

## Status

landed 20261016T064221-L-582079 2026-10-16 (merge of deliver/C2/Sheaf.Paper.ContinuousIntegralPullComposition)
