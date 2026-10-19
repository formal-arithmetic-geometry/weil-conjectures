# compactSupportAction constructions

## Reason

The retained concrete-to-abstract bridge attempted to identify composites after specializing
`derivedPlusFormalism (ModuleCat A)`. Profiling found deterministic timeouts in that conversion,
including a kernel timeout on the redundant `action_pbId` bridge; the full file exceeded 60 s.
Construct exchange, action and the coefficient isomorphism once for an abstract compact-support
formalism, prove coherence there, and specialize the constructions themselves. This preserves
the canonical maps while avoiding comparisons between expanded derived resolutions.

All three existing definitions keep their signatures. The exchange remains the exchange for
`c.ofIsPullback sq` followed by `shriekIso`; the action remains identity-pullback inverse,
exchange, and the image of theta. The coefficient isomorphism remains `sqIso.app` followed by
`mapIso theta`. The three new generic definitions contain exactly these constructions; they
choose no witnesses and introduce no proof holes. The private `action_eq`, `exchange_eq`
and `coefficient_eq` lemmas are the equation API used for explicit rewriting. This last
change avoids the remaining kernel conversion timeout: the complete diagnostic copy now
compiles in 6.1 s even at 10000 heartbeats, without raising the project's standard limits.

## Old

```lean
noncomputable def compactSupportActionExchange
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {g : Y' ⟶ Y} {g' : X' ⟶ X} [IsSeparated f] [LocallyOfFiniteType f]
    [QuasiCompact f] [QuasiCompact f']
    (sq : IsPullback g' f' f g) (c : Compactification f) (d : Compactification f') :
    (derivedPlusFormalism (ModuleCat.{u + 1} A)).shriek c ⋙
        (derivedPlusFormalism (ModuleCat.{u + 1} A)).pb g ⟶
      (derivedPlusFormalism (ModuleCat.{u + 1} A)).pb g' ⋙
        (derivedPlusFormalism (ModuleCat.{u + 1} A)).shriek d :=
  rightDerivedLowerShriekOfCompactificationPlusBaseChangeMap A sq c ≫
    Functor.whiskerLeft ((derivedPlusFormalism (ModuleCat.{u + 1} A)).pb g')
      ((derivedPlusFormalism (ModuleCat.{u + 1} A)).shriekIso (c.ofIsPullback sq) d).hom
```

```lean
noncomputable def compactSupportAction
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} [IsSeparated f] [LocallyOfFiniteType f]
    [QuasiCompact f]
    (c : Compactification f) {a : X ⟶ X} (sq : IsPullback a f f (𝟙 Y))
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (theta : ((derivedPlusFormalism (ModuleCat.{u + 1} A)).pb a).obj K ≅ K) :
    ((derivedPlusFormalism (ModuleCat.{u + 1} A)).shriek c).obj K ⟶
      ((derivedPlusFormalism (ModuleCat.{u + 1} A)).shriek c).obj K :=
  (upperStarIdDerivedPlus (ModuleCat.{u + 1} A) Y).inv.app _ ≫
    (compactSupportActionExchange A sq c c).app K ≫
    ((derivedPlusFormalism (ModuleCat.{u + 1} A)).shriek c).map theta.hom
```

```lean
noncomputable def compactSupportActionPullbackCoefficient
    (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (a : X ≅ X) (ha : a.hom ≫ f = f)
    {T : Scheme.{u}} (u : T ⟶ Y)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (theta : ((derivedPlusFormalism (ModuleCat.{u + 1} A)).pb a.hom).obj K ≅ K) :
    ((derivedPlusFormalism (ModuleCat.{u + 1} A)).pb
        (compactSupportActionPullback f a ha u).hom).obj
          (((derivedPlusFormalism (ModuleCat.{u + 1} A)).pb (pullback.fst f u)).obj K) ≅
      ((derivedPlusFormalism (ModuleCat.{u + 1} A)).pb (pullback.fst f u)).obj K :=
  ((derivedPlusFormalism (ModuleCat.{u + 1} A)).sqIso
      (compactSupportActionPullback f a ha u).hom (pullback.fst f u)
      (pullback.fst f u) a.hom (by simp [compactSupportActionPullback, pullback.map])).app K ≪≫
    ((derivedPlusFormalism (ModuleCat.{u + 1} A)).pb (pullback.fst f u)).mapIso theta
```

## New

```lean
noncomputable def compactSupportActionExchange
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {g : Y' ⟶ Y} {g' : X' ⟶ X} [IsSeparated f] [LocallyOfFiniteType f]
    [QuasiCompact f] [QuasiCompact f']
    (sq : IsPullback g' f' f g) (c : Compactification f) (d : Compactification f') :
    (derivedPlusFormalism (ModuleCat.{u + 1} A)).shriek c ⋙
        (derivedPlusFormalism (ModuleCat.{u + 1} A)).pb g ⟶
      (derivedPlusFormalism (ModuleCat.{u + 1} A)).pb g' ⋙
        (derivedPlusFormalism (ModuleCat.{u + 1} A)).shriek d :=
  compactSupportFormalExchange (derivedPlusFormalism (ModuleCat.{u + 1} A)) sq c d
```

```lean
noncomputable def compactSupportAction
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} [IsSeparated f] [LocallyOfFiniteType f]
    [QuasiCompact f]
    (c : Compactification f) {a : X ⟶ X} (sq : IsPullback a f f (𝟙 Y))
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (theta : ((derivedPlusFormalism (ModuleCat.{u + 1} A)).pb a).obj K ≅ K) :
    ((derivedPlusFormalism (ModuleCat.{u + 1} A)).shriek c).obj K ⟶
      ((derivedPlusFormalism (ModuleCat.{u + 1} A)).shriek c).obj K :=
  compactSupportFormalAction (derivedPlusFormalism (ModuleCat.{u + 1} A))
    c sq K theta.hom
```

```lean
noncomputable def compactSupportActionPullbackCoefficient
    (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (a : X ≅ X) (ha : a.hom ≫ f = f)
    {T : Scheme.{u}} (u : T ⟶ Y)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (theta : ((derivedPlusFormalism (ModuleCat.{u + 1} A)).pb a.hom).obj K ≅ K) :
    ((derivedPlusFormalism (ModuleCat.{u + 1} A)).pb
        (compactSupportActionPullback f a ha u).hom).obj
          (((derivedPlusFormalism (ModuleCat.{u + 1} A)).pb (pullback.fst f u)).obj K) ≅
      ((derivedPlusFormalism (ModuleCat.{u + 1} A)).pb (pullback.fst f u)).obj K :=
  compactSupportFormalCoefficientIso (derivedPlusFormalism (ModuleCat.{u + 1} A))
    (pullback.fst f u) a.hom (compactSupportActionPullback f a ha u).hom
    (by simp [compactSupportActionPullback, pullback.map]) K theta
```

## Users

`tools/downstream.py Sheaf.AlgebraicGeometry.CompactSupportActionBaseChange --uses
compactSupportAction` reports only this module as a direct user. A source search for each of
the three exact definition names throughout `lean/Sheaf` likewise finds only this module.
There are 700 transitive module importers; their statements are preserved because the
existing signatures and the canonical constructions are unchanged. No target signature
changes. The generic factorizations are definitionally the old constructions, so no target
meaning changes or forced consumer adaptations arise.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.CompactSupportActionBaseChange | D4 | Prove the three existing theorem holes; factor three constructions through their generic forms. |

## Status

landed 20261019T034253-L-415887 2026-10-19 (merge of deliver/D4/Sheaf.AlgebraicGeometry.CompactSupportActionBaseChange)
