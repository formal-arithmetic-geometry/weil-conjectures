# AlgebraicGeometry.ProEtale.IntegralQuotient comparison wrappers

## Reason

The original presentations repeatedly force kernel reduction between the internal and native derived-functor aliases. The assigned file exceeds the 60-second compile limit at ExchangeRealized transport. Reuse the published generic rectangle interfaces, whose normalization calculations identify exactly the same maps. No target signature changes.

## Old

```lean
def ambient (sq : ChosenCartesianSquare h f' f g) :
    F Λ f ⋙ L Λ g ⟶ L Λ h ⋙ F Λ f' := by
  unfold F L CondensedRing.moduleObjectDerivedPushforward
    CondensedRing.moduleObjectDerivedPullback
  exact CondensedRing.condensedAmbientExchange Λ sq
```

```lean
def sectionExchange (sq : ChosenCartesianSquare h f' f g) :
    ModuleRingedComparison.derivedPushforward Λ f ⋙
        ModuleRingedComparison.derivedPullback Λ g ⟶
      ModuleRingedComparison.derivedPullback Λ h ⋙
        ModuleRingedComparison.derivedPushforward Λ f' :=
  (mateEquiv (ModuleRingedComparison.derivedAdjunction Λ f)
    (ModuleRingedComparison.derivedAdjunction Λ f')
    (TwoSquare.mk _ _ _ _ (sectionSquare Λ sq).hom)).natTrans
```

```lean
def pullSection {U V : Scheme.{u}} (u : U ⟶ V) :
    L Λ u ⋙ ModuleRingedComparison.derivedFunctor Λ U ≅
      ModuleRingedComparison.derivedFunctor Λ V ⋙ ModuleRingedComparison.derivedPullback Λ u := by
  unfold L CondensedRing.moduleObjectDerivedPullback
  exact ModuleRingedComparison.derivedPullComparison Λ u
```

```lean
def pushSection {U V : Scheme.{u}} (u : U ⟶ V) :
    F Λ u ⋙ ModuleRingedComparison.derivedFunctor Λ V ≅
      ModuleRingedComparison.derivedFunctor Λ U ⋙
        ModuleRingedComparison.derivedPushforward Λ u := by
  unfold F CondensedRing.moduleObjectDerivedPushforward
  exact ModuleRingedComparison.derivedPushComparison Λ u
```

```lean
def ExchangeRealized (sq : ChosenCartesianSquare h f' f g) : Prop :=
  ∀ K : DerivedCategory (Modules Λ X),
    (pullSection Λ g).hom.app ((F Λ f).obj K) ≫
        (ModuleRingedComparison.derivedPullback Λ g).map
          ((pushSection Λ f).hom.app K) ≫
        (sectionExchange Λ sq).app
          ((ModuleRingedComparison.derivedFunctor Λ X).obj K) =
      (ModuleRingedComparison.derivedFunctor Λ Y').map ((ambient Λ sq).app K) ≫
        (pushSection Λ f').hom.app ((L Λ h).obj K) ≫
        (ModuleRingedComparison.derivedPushforward Λ f').map
          ((pullSection Λ h).hom.app K)
```

## New

```lean
def ambient (sq : ChosenCartesianSquare h f' f g) :
    F Λ f ⋙ L Λ g ⟶ L Λ h ⋙ F Λ f' :=
  (mateEquiv (adj Λ f) (adj Λ f')
    (TwoSquare.mk _ _ _ _ (scalarPullbackSquare Λ sq).hom)).natTrans
```

```lean
def sectionExchange (sq : ChosenCartesianSquare h f' f g) :
    ModuleRingedComparison.derivedPushforward Λ f ⋙
        ModuleRingedComparison.derivedPullback Λ g ⟶
      ModuleRingedComparison.derivedPullback Λ h ⋙
        ModuleRingedComparison.derivedPushforward Λ f' :=
  (mateEquiv (ModuleRingedComparison.derivedAdjunction Λ f)
    (ModuleRingedComparison.derivedAdjunction Λ f')
    (TwoSquare.mk _ _ _ _ (sectionSquare Λ sq).hom)).natTrans
```

(sectionExchange is unchanged from Old.)

```lean
def pullSection {U V : Scheme.{u}} (u : U ⟶ V) :
    L Λ u ⋙ ModuleRingedComparison.derivedFunctor Λ U ≅
      ModuleRingedComparison.derivedFunctor Λ V ⋙ ModuleRingedComparison.derivedPullback Λ u :=
  scalarSectionPullComparison Λ u
```

```lean
def pushSection {U V : Scheme.{u}} (u : U ⟶ V) :
    F Λ u ⋙ ModuleRingedComparison.derivedFunctor Λ V ≅
      ModuleRingedComparison.derivedFunctor Λ U ⋙
        ModuleRingedComparison.derivedPushforward Λ u :=
  scalarSectionPushComparison Λ u
```

```lean
def ExchangeRealized (sq : ChosenCartesianSquare h f' f g) : Prop :=
  ∀ K : DerivedCategory (Modules Λ X),
    mateRouteLeft (ModuleRingedComparison.derivedFunctor Λ Y')
        (ambient Λ sq) (pushSection Λ f').hom (pullSection Λ h).hom K =
      mateRouteRight (ModuleRingedComparison.derivedPullback Λ g)
        (pullSection Λ g).hom (pushSection Λ f).hom (sectionExchange Λ sq) K
```

The ambient wrapper is the same mate as before: adj unfolds to
derivedUpperStarLowerStarAdjunction and scalarPullbackSquare to the composite of the
leftDerivedUpperStarComp compositors and the square's eqToIso, i.e. the body of
condensedAmbientExchange; it is also definitionally scalarAmbientExchange (proved by
`delta; rfl` in ambient_eq_scalar). The pull wrapper is the same derivedPullComparison
(def-sfb-internal-section-scalar-pullback-comparison-data). The push wrapper is the
owned scalarSectionPushComparison (def-sfb-scalar-section-push-comparison-data): its hom
equals the old derivedPushComparison hom by scalarSectionPushMate_eq and its inverse is
literally the old inverse, so as an isomorphism it equals the old wrapper.
ExchangeRealized states the former three-factor equality through the categorical
composites mateRouteLeft and mateRouteRight (cb.map r ≫ eb ≫ rgb.map la and
lc ≫ T₂.map e ≫ t), with the sides reversed, on the same wrappers. Equality symmetry
gives equivalence with the former predicate, without any hypothesis or conclusion change.
The statement's definitions are owned by the def nodes now listed in the item's
stmt_deps: def-sfb-internal-derived-scalar-comparisons (adj, D, L, F, rho,
PullNormalized), def-sfb-scalar-pullback-square-data (scalarPullbackSquare),
def-sfb-internal-section-scalar-pullback-comparison-data and
def-sfb-scalar-section-push-comparison-data. (Reviewer correction: the delivered bodies
used scalarAmbientExchange and sectionRectangleExchange, defined only in the theorem
module of lem-sfb-scalar-geometric-exchange-rectangle; they are now inlined.)

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.IntegralQuotientExchangeComparison | D7 | Assigned module; proof uses the canonical wrappers. |

The read-only `tools/downstream.py Sheaf.Paper.IntegralQuotientExchangeComparison
--uses ambient sectionExchange pullSection pushSection ExchangeRealized` reports
zero downstream modules and only this module as a textual user of each name.
DAG parents retain this node and its Lean attachment. No declaration is withdrawn.
The target semantic review remains required for the equivalent definition presentations.
The generic rectangle is a public import because the definitions now use its public API.

## Status

landed 20261025T162207-L-354963 2026-10-25 (merge of deliver/D7/Sheaf.Paper.IntegralQuotientExchangeComparison)
