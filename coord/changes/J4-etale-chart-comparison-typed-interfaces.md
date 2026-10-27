# Canonical comparison definitions

## Reason

Give the canonical tensor arrows explicit morphism types and remove transports along
reflexive object equalities. Share the three exact degree-zero comparisons as named
natural isomorphisms, and use the source-library composite-square construction by name.
All maps remain the same canonical maps; no target statement changes.

## Old

```lean
def nuTensorRaw (R : Type (u + 1)) [CommRing R] [Finite R] (T : Scheme.{u})
    (K M : DerivedCategory (Et R T)) :=
  ((Functor.leftDerivedTensorComparison
    (comparisonUpperStar (ModuleCat.{u + 1} R) T)).app K).app M
```

```lean
def etTensorRaw (R : Type (u + 1)) [CommRing R] [Finite R]
    {T T' : Scheme.{u}} (v : T' ⟶ T) (K M : DerivedCategory (Et R T)) :=
  ((Functor.leftDerivedTensorComparison
    (Etale.upperStar (ModuleCat.{u + 1} R) v)).app K).app M
```

```lean
def proTensorRaw (R : Type (u + 1)) [CommRing R] [Finite R]
    {T T' : Scheme.{u}} (v : T' ⟶ T) (K M : DerivedCategory (Pro R T)) :=
  ((Functor.leftDerivedTensorComparison
    (AlgebraicGeometry.ProEtale.upperStar (ModuleCat.{u + 1} R) v)).app K).app M
```

```lean
def nuTensor (R : Type (u + 1)) [CommRing R] [Finite R] (T : Scheme.{u})
    (K M : DerivedCategory (Et R T)) :
    (nu R T).obj (K ⊗ M) ⟶ (nu R T).obj K ⊗ (nu R T).obj M :=
  eqToHom (nuTensor_source R T K M).symm ≫ nuTensorRaw R T K M ≫
    eqToHom (nuTensor_target R T K M)
```

```lean
def etTensor (R : Type (u + 1)) [CommRing R] [Finite R]
    {T T' : Scheme.{u}} (v : T' ⟶ T)
    (K M : DerivedCategory (Et R T)) :
    (etPull R v).obj (K ⊗ M) ⟶ (etPull R v).obj K ⊗ (etPull R v).obj M :=
  eqToHom (etTensor_source R v K M).symm ≫ etTensorRaw R v K M ≫
    eqToHom (etTensor_target R v K M)
```

```lean
def proTensor (R : Type (u + 1)) [CommRing R] [Finite R]
    {T T' : Scheme.{u}} (v : T' ⟶ T)
    (K M : DerivedCategory (Pro R T)) :
    (proPull R v).obj (K ⊗ M) ⟶ (proPull R v).obj K ⊗ (proPull R v).obj M :=
  eqToHom (proTensor_source R v K M).symm ≫ proTensorRaw R v K M ≫
    eqToHom (proTensor_target R v K M)
```

```lean
def schemeIso (R : Type (u + 1)) [CommRing R] {T T' : Scheme.{u}} (v : T' ⟶ T) :
    etPull R v ⋙ nu R T' ≅ nu R T ⋙ proPull R v :=
  (Functor.leftDerivedFunctorCompIso
    (Etale.upperStar (ModuleCat.{u + 1} R) v)
    (comparisonUpperStar (ModuleCat.{u + 1} R) T')).symm ≪≫
  Functor.leftDerivedFunctorNatIso
    (Etale.upperStar (ModuleCat.{u + 1} R) v ⋙
      comparisonUpperStar (ModuleCat.{u + 1} R) T')
    (schemeSheafIso R v) ≪≫
  Functor.leftDerivedFunctorCompIso
    (comparisonUpperStar (ModuleCat.{u + 1} R) T)
    (AlgebraicGeometry.ProEtale.upperStar (ModuleCat.{u + 1} R) v)
```

```lean
def twistLineIso (R : Type (u + 1)) [CommRing R] [Finite R]
    (N : ℕ) (hN : 0 < N) (hR : (N : R) = 0) (T : Scheme.{u})
    (hT : IsUnit (N : Γ(T, ⊤))) (c : ℕ) :
    (nu R T).obj ((DerivedCategory.singleFunctor (Et R T) 0).obj
        (Scheme.finiteEtaleTateTwist T N R hR c)) ≅
      (DerivedCategory.singleFunctor (Pro R T) 0).obj (proTwist R N hN hR T c) :=
  (Functor.singleFunctorCompLeftDerivedFunctorIso
    (comparisonUpperStar (ModuleCat.{u + 1} R) T)).app _ ≪≫
  (DerivedCategory.singleFunctor (Pro R T) 0).mapIso (twistSheafIso R N hN hR T hT c)
```

```lean
def twistIso (R : Type (u + 1)) [CommRing R] [Finite R]
    (N : ℕ) (hN : 0 < N) (hR : (N : R) = 0) (T : Scheme.{u})
    (hT : IsUnit (N : Γ(T, ⊤))) (c : ℕ) (L : DerivedCategory (Et R T)) :=
  asIso (nuTensor R T L ((DerivedCategory.singleFunctor (Et R T) 0).obj
    (Scheme.finiteEtaleTateTwist T N R hR c))) ≪≫
  (Iso.refl ((nu R T).obj L) ⊗ᵢ twistLineIso R N hN hR T hT c)
```

```lean
def etTwistPullback (R : Type (u + 1)) [CommRing R] [Finite R]
    (N : ℕ) (hN : 0 < N) (hR : (N : R) = 0)
    {T T' : Scheme.{u}} (v : T' ⟶ T)
    (hT : IsUnit (N : Γ(T, ⊤))) (hT' : IsUnit (N : Γ(T', ⊤)))
    (c : ℕ) (L : DerivedCategory (Et R T)) :=
  asIso (etTensor R v L ((DerivedCategory.singleFunctor (Et R T) 0).obj
    (Scheme.finiteEtaleTateTwist T N R hR c))) ≪≫
  (Iso.refl _ ⊗ᵢ
    ((Functor.singleFunctorCompLeftDerivedFunctorIso
      (Etale.upperStar (ModuleCat.{u + 1} R) v)).app _ ≪≫
    (DerivedCategory.singleFunctor (Et R T') 0).mapIso
      (etTwistSheafPullback R N hN hR v hT hT' c)))
```

```lean
def proTwistPullback (R : Type (u + 1)) [CommRing R] [Finite R]
    (N : ℕ) (hN : 0 < N) (hR : (N : R) = 0)
    {T T' : Scheme.{u}} (v : T' ⟶ T)
    (hT : IsUnit (N : Γ(T, ⊤))) (hT' : IsUnit (N : Γ(T', ⊤)))
    (c : ℕ) (L : DerivedCategory (Pro R T)) :=
  asIso (proTensor R v L ((DerivedCategory.singleFunctor (Pro R T) 0).obj
    (proTwist R N hN hR T c))) ≪≫
  (Iso.refl _ ⊗ᵢ
    ((Functor.singleFunctorCompLeftDerivedFunctorIso
      (AlgebraicGeometry.ProEtale.upperStar (ModuleCat.{u + 1} R) v)).app _ ≪≫
    (DerivedCategory.singleFunctor (Pro R T') 0).mapIso
      (proTwistSheafPullback R N hN hR v hT hT' c)))
```

## New

```lean
def nuTensorRaw (R : Type (u + 1)) [CommRing R] [Finite R] (T : Scheme.{u})
    (K M : DerivedCategory (Et R T)) :
    (nu R T).obj (K ⊗ M) ⟶ (nu R T).obj K ⊗ (nu R T).obj M :=
  ((Functor.leftDerivedTensorComparison
    (comparisonUpperStar (ModuleCat.{u + 1} R) T)).app K).app M
```

```lean
def etTensorRaw (R : Type (u + 1)) [CommRing R] [Finite R]
    {T T' : Scheme.{u}} (v : T' ⟶ T) (K M : DerivedCategory (Et R T)) :
    (etPull R v).obj (K ⊗ M) ⟶ (etPull R v).obj K ⊗ (etPull R v).obj M :=
  ((Functor.leftDerivedTensorComparison
    (Etale.upperStar (ModuleCat.{u + 1} R) v)).app K).app M
```

```lean
def proTensorRaw (R : Type (u + 1)) [CommRing R] [Finite R]
    {T T' : Scheme.{u}} (v : T' ⟶ T) (K M : DerivedCategory (Pro R T)) :
    (proPull R v).obj (K ⊗ M) ⟶ (proPull R v).obj K ⊗ (proPull R v).obj M :=
  ((Functor.leftDerivedTensorComparison
    (AlgebraicGeometry.ProEtale.upperStar (ModuleCat.{u + 1} R) v)).app K).app M
```

```lean
def nuTensor (R : Type (u + 1)) [CommRing R] [Finite R] (T : Scheme.{u})
    (K M : DerivedCategory (Et R T)) :
    (nu R T).obj (K ⊗ M) ⟶ (nu R T).obj K ⊗ (nu R T).obj M :=
  nuTensorRaw R T K M
```

```lean
def etTensor (R : Type (u + 1)) [CommRing R] [Finite R]
    {T T' : Scheme.{u}} (v : T' ⟶ T)
    (K M : DerivedCategory (Et R T)) :
    (etPull R v).obj (K ⊗ M) ⟶ (etPull R v).obj K ⊗ (etPull R v).obj M :=
  etTensorRaw R v K M
```

```lean
def proTensor (R : Type (u + 1)) [CommRing R] [Finite R]
    {T T' : Scheme.{u}} (v : T' ⟶ T)
    (K M : DerivedCategory (Pro R T)) :
    (proPull R v).obj (K ⊗ M) ⟶ (proPull R v).obj K ⊗ (proPull R v).obj M :=
  proTensorRaw R v K M
```

```lean
def schemeIso (R : Type (u + 1)) [CommRing R] {T T' : Scheme.{u}} (v : T' ⟶ T) :
    etPull R v ⋙ nu R T' ≅ nu R T ⋙ proPull R v :=
  Functor.leftDerivedFunctorCompNatIso
    (comparisonUpperStar (ModuleCat.{u + 1} R) T)
    (AlgebraicGeometry.ProEtale.upperStar (ModuleCat.{u + 1} R) v)
    (Etale.upperStar (ModuleCat.{u + 1} R) v)
    (comparisonUpperStar (ModuleCat.{u + 1} R) T') (schemeSheafIso R v)
```

```lean
def twistLineIso (R : Type (u + 1)) [CommRing R] [Finite R]
    (N : ℕ) (hN : 0 < N) (hR : (N : R) = 0) (T : Scheme.{u})
    (hT : IsUnit (N : Γ(T, ⊤))) (c : ℕ) :
    (nu R T).obj ((DerivedCategory.singleFunctor (Et R T) 0).obj
        (Scheme.finiteEtaleTateTwist T N R hR c)) ≅
      (DerivedCategory.singleFunctor (Pro R T) 0).obj (proTwist R N hN hR T c) :=
  (nuSingle R T).app (Scheme.finiteEtaleTateTwist T N R hR c) ≪≫
    (DerivedCategory.singleFunctor (Pro R T) 0).mapIso (twistSheafIso R N hN hR T hT c)
```

```lean
def twistIso (R : Type (u + 1)) [CommRing R] [Finite R]
    (N : ℕ) (hN : 0 < N) (hR : (N : R) = 0) (T : Scheme.{u})
    (hT : IsUnit (N : Γ(T, ⊤))) (c : ℕ) (L : DerivedCategory (Et R T)) :
    (nu R T).obj (L ⊗ (DerivedCategory.singleFunctor (Et R T) 0).obj
      (Scheme.finiteEtaleTateTwist T N R hR c)) ≅
    (nu R T).obj L ⊗ (DerivedCategory.singleFunctor (Pro R T) 0).obj
      (proTwist R N hN hR T c) :=
  asIso (nuTensor R T L ((DerivedCategory.singleFunctor (Et R T) 0).obj
    (Scheme.finiteEtaleTateTwist T N R hR c))) ≪≫
  (Iso.refl ((nu R T).obj L) ⊗ᵢ twistLineIso R N hN hR T hT c)
```

```lean
def etTwistPullback (R : Type (u + 1)) [CommRing R] [Finite R]
    (N : ℕ) (hN : 0 < N) (hR : (N : R) = 0)
    {T T' : Scheme.{u}} (v : T' ⟶ T)
    (hT : IsUnit (N : Γ(T, ⊤))) (hT' : IsUnit (N : Γ(T', ⊤)))
    (c : ℕ) (L : DerivedCategory (Et R T)) :
    (etPull R v).obj (L ⊗ (DerivedCategory.singleFunctor (Et R T) 0).obj
      (Scheme.finiteEtaleTateTwist T N R hR c)) ≅
    (etPull R v).obj L ⊗ (DerivedCategory.singleFunctor (Et R T') 0).obj
      (Scheme.finiteEtaleTateTwist T' N R hR c) :=
  asIso (etTensor R v L ((DerivedCategory.singleFunctor (Et R T) 0).obj
    (Scheme.finiteEtaleTateTwist T N R hR c))) ≪≫
  (Iso.refl ((etPull R v).obj L) ⊗ᵢ
    ((etSingle R v).app (Scheme.finiteEtaleTateTwist T N R hR c) ≪≫
      (DerivedCategory.singleFunctor (Et R T') 0).mapIso
        (etTwistSheafPullback R N hN hR v hT hT' c)))
```

```lean
def proTwistPullback (R : Type (u + 1)) [CommRing R] [Finite R]
    (N : ℕ) (hN : 0 < N) (hR : (N : R) = 0)
    {T T' : Scheme.{u}} (v : T' ⟶ T)
    (hT : IsUnit (N : Γ(T, ⊤))) (hT' : IsUnit (N : Γ(T', ⊤)))
    (c : ℕ) (L : DerivedCategory (Pro R T)) :
    (proPull R v).obj (L ⊗ (DerivedCategory.singleFunctor (Pro R T) 0).obj
      (proTwist R N hN hR T c)) ≅
    (proPull R v).obj L ⊗ (DerivedCategory.singleFunctor (Pro R T') 0).obj
      (proTwist R N hN hR T' c) :=
  asIso (proTensor R v L ((DerivedCategory.singleFunctor (Pro R T) 0).obj
    (proTwist R N hN hR T c))) ≪≫
  (Iso.refl ((proPull R v).obj L) ⊗ᵢ
    ((proSingle R v).app (proTwist R N hN hR T c) ≪≫
      (DerivedCategory.singleFunctor (Pro R T') 0).mapIso
        (proTwistSheafPullback R N hN hR v hT hT' c)))
```

```lean
def nuSingle (R : Type (u + 1)) [CommRing R] (T : Scheme.{u}) :
    DerivedCategory.singleFunctor (Et R T) 0 ⋙ nu R T ≅
      comparisonUpperStar (ModuleCat.{u + 1} R) T ⋙
        DerivedCategory.singleFunctor (Pro R T) 0 :=
  Functor.singleFunctorCompLeftDerivedFunctorIso
    (comparisonUpperStar (ModuleCat.{u + 1} R) T)
```

```lean
def etSingle (R : Type (u + 1)) [CommRing R] {T T' : Scheme.{u}} (v : T' ⟶ T) :
    DerivedCategory.singleFunctor (Et R T) 0 ⋙ etPull R v ≅
      Etale.upperStar (ModuleCat.{u + 1} R) v ⋙ DerivedCategory.singleFunctor (Et R T') 0 :=
  Functor.singleFunctorCompLeftDerivedFunctorIso (Etale.upperStar (ModuleCat.{u + 1} R) v)
```

```lean
def proSingle (R : Type (u + 1)) [CommRing R] {T T' : Scheme.{u}} (v : T' ⟶ T) :
    DerivedCategory.singleFunctor (Pro R T) 0 ⋙ proPull R v ≅
      AlgebraicGeometry.ProEtale.upperStar (ModuleCat.{u + 1} R) v ⋙
        DerivedCategory.singleFunctor (Pro R T') 0 :=
  Functor.singleFunctorCompLeftDerivedFunctorIso
    (AlgebraicGeometry.ProEtale.upperStar (ModuleCat.{u + 1} R) v)
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.EtaleChartComparisonIsos | J4 | Internal uses retain the same maps and propositions. |

The downstream query was repeated for all eleven changed definitions and the three new
comparison caches; it lists no external consumer modules. The local consumer checks
cover every changed definition. The three new natural isomorphisms are the existing
`singleFunctorCompLeftDerivedFunctorIso` constructions with explicit functor types.
Tensor source and target equalities are proved by reflexivity, so removing their
identity transports does not change the specified morphism. The named composite
square unfolds to the former three-isomorphism expression.

## Status

landed 20261024T190125-L-3948416 2026-10-24 (merge of deliver/J4/Sheaf.AlgebraicGeometry.EtaleChartComparisonIsos)
