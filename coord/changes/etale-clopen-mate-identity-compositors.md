# AlgebraicGeometry.Etale.ClopenMateNormalization: identity compositor reduction

## Reason

Return repair (head 8421668e1): the four duplicate private helpers are removed.
`Sheaf.CategoryTheory.DerivedComplexUnitCompatibility` constructs the complex unit
explicitly and packages the existing four private compatibility proofs as a proved
conjunction. That module alone uses a proof-only `import all` of the comparison
module; the item imports the compiled interface normally. The comparison module is
unchanged. The new conjunction and unit have a node and contain no holes. The explicit unit
uses `no_expose`, matching the retained construction and avoiding generated unfoldings.

Consumer validation found that site transport unfolds `derivedMatePlus` and
strict-tower evaluation converts `normalizedComparison` to the original second
coherence choice. The derived mate remains exposed. `normalizedComparison` retains its original
second coherence-choice body. The bundle is irreducible and exports a proved
derived-field equation, used internally in the item proof. No consumer is adapted.

The geometric support-inclusion proof explicitly obtains its cancellation
epimorphism from an isomorphism. The direct-image compositor receives its explicit
composite and reflexivity proof. No instance is exported.


Kernel profiling identified expensive conversions through identity associators in
`alpha`, and through `mapHomologicalComplexCompIso (Iso.refl _)` in the chain arrows.
The associator components and the latter chain maps are identities. Removing them
retains the prescribed cartesian comparison, clopen projection, open-extension
compositor and inverse-image transport. The resulting maps agree with the original
ones by the identity and functor-map-identity laws.

The two derived mate definitions now explicitly name their natural-transformation
result types and project `.natTrans` from `mateEquiv`. Previously their inferred result
was `TwoSquare`, which is definitionally this same natural-transformation type.
This prevents unnecessary conversion through the square wrapper in concrete uses.
Their binders and mathematical values are unchanged.

The new generic composite API is `Sheaf.CategoryTheory.ClopenMateComposite`.
`alpha` is now an application of that construction; its component equation follows
from the generic API. It stores the same components directly in a `NatTrans` structure.

`Sheaf.AlgebraicGeometry.ProperOpenInterchangeData` similarly stores the same two
families selected by `properOpenInterchangeCoherence`, together with its exact
normalization proof. `supportComparison` projects the ordinary field; the normalization proof
identifies the original `normalizedComparison` with the derived field by the
proved projection equation. Unfolding the bundled constructor gives precisely the previous selections;
its irreducibility prevents repeated dependent-choice unfolding. A proved
`properOpenInterchangeData_derived` equation exposes the same original second
coherence choice for consumers.
The two normalization accessors are proved theorems with explicit equation types.
Their proofs extract the first and second conjuncts, but their public types retain
only those equations. This avoids carrying the entire remaining coherence
conjunction as implicit arguments in every accessor use.

The exact-functor D+/D compatibility isomorphisms are identities. Removing those
identity factors from `sourceCompatibility` and `targetCompatibility` preserves their
canonical isomorphisms by the functor-map-identity and isomorphism identity laws.
This avoids normalizing the same concrete compatibility expression repeatedly.

The exact-localized square constructors are now named generic definitions in the
item module: `clopenLocalizedSquare` and `clopenLocalizedSquarePlus`. The existing
`derivedAlpha` and `derivedAlphaPlus` apply these constructions directly to `alpha`;
unfolding the generic definitions gives their original localization terms verbatim.
This repairs the costly conversion between duplicated generic and concrete terms.

The theorem statements are unchanged. The two new construction modules are plain (non-public) imports: only the
`no_expose` bodies of `alpha` and `supportComparison` and the private proofs use them
(reviewer correction, cc review of 77b588f5); all original public imports remain. No adopted source-library
file is modified. The internal construction definitions use `no_expose` where consumers do not need
their bodies. `derivedMatePlus` remains exposed to preserve consumer unfolding.
`normalizedComparison` retains its original exposed choice definition. The bundle
constructor has an explicit projection equation used in the item proof.
The target signatures are unchanged; the mathematical meaning of their intermediate
maps is preserved by the identity laws above, for independent review.

## Old

```lean
def alpha {V W S T : Scheme.{u}} (k : V ⟶ W) (r : V ⟶ S)
    (p : W ⟶ T) (i : S ⟶ T) [IsOpenImmersion k] [IsOpenImmersion i]
    [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i) :
    openImmersionLowerShriek (ModuleCat.{u + 1} Λ) i ⋙
        upperStar (ModuleCat.{u + 1} Λ) p ⟶
      upperStar (ModuleCat.{u + 1} Λ) r ⋙
        openImmersionLowerShriek (ModuleCat.{u + 1} Λ) k :=
  let s := pullback.lift k r h
  letI := (lift_clopen k r p i h).1
  letI := (lift_clopen k r p i h).2
  let q := pullback.snd p i
  let b := pullback.fst p i
  (@asIso _ _ _ _ _ (isIso_openImmersionLowerShriekBaseChangeMap
    (ModuleCat.{u + 1} Λ) (IsPullback.of_hasPullback p i).flip)).inv ≫
  Functor.whiskerRight (Functor.whiskerLeft (upperStar (ModuleCat.{u + 1} Λ) q)
    (projection Λ s)) (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) b) ≫
  Functor.whiskerRight
    (Functor.associator (upperStar (ModuleCat.{u + 1} Λ) q)
      (upperStar (ModuleCat.{u + 1} Λ) s)
      (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) s)).inv
    (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) b) ≫
  (Functor.associator (upperStar (ModuleCat.{u + 1} Λ) q ⋙
    upperStar (ModuleCat.{u + 1} Λ) s)
    (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) s)
    (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) b)).hom ≫
  Functor.whiskerLeft (upperStar (ModuleCat.{u + 1} Λ) q ⋙
    upperStar (ModuleCat.{u + 1} Λ) s)
    ((openImmersionLowerShriekComp (ModuleCat.{u + 1} Λ) s b).inv ≫
      (openCongr Λ (pullback.lift_fst k r h)).hom) ≫
  Functor.whiskerRight
    ((upperStarComp (ModuleCat.{u + 1} Λ) s q).inv ≫
      (eqToIso (congrArg (upperStar (ModuleCat.{u + 1} Λ))
        (pullback.lift_snd k r h))).hom)
    (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) k)
```

```lean
def derivedMate {V W S T : Scheme.{u}} (k : V ⟶ W) (r : V ⟶ S)
    (p : W ⟶ T) (i : S ⟶ T) [IsOpenImmersion k] [IsOpenImmersion i]
    [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i) :=
  mateEquiv (mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) r)
    (mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) p)
    (derivedAlpha Λ k r p i h)
```

```lean
def derivedMatePlus {V W S T : Scheme.{u}} (k : V ⟶ W) (r : V ⟶ S)
    (p : W ⟶ T) (i : S ⟶ T) [IsOpenImmersion k] [IsOpenImmersion i]
    [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i) :=
  mateEquiv (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) r).derivedPlus
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) p).derivedPlus
    (derivedAlphaPlus Λ k r p i h)
```

```lean
def resolutionArrow [Finite Λ] {V W S T : Scheme.{u}}
    (k : V ⟶ W) (r : V ⟶ S) (p : W ⟶ T) (i : S ⟶ T)
    [IsOpenImmersion k] [IsOpenImmersion i] [IsProper r] [IsProper p]
    (h : k ≫ p = r ≫ i)
    (J : CochainComplex (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ℤ)
    (I : CochainComplex (Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ℤ)
    (t : ((openImmersionLowerShriek (ModuleCat.{u + 1} Λ) k).mapHomologicalComplex
      (.up ℤ)).obj J ⟶ I) :
    ((openImmersionLowerShriek (ModuleCat.{u + 1} Λ) i).mapHomologicalComplex (.up ℤ)).obj
        (((lowerStar (ModuleCat.{u + 1} Λ) r).mapHomologicalComplex (.up ℤ)).obj J) ⟶
      ((lowerStar (ModuleCat.{u + 1} Λ) p).mapHomologicalComplex (.up ℤ)).obj I :=
  (Functor.mapHomologicalComplexCompIso (Iso.refl
    (lowerStar (ModuleCat.{u + 1} Λ) r ⋙
      openImmersionLowerShriek (ModuleCat.{u + 1} Λ) i)) (.up ℤ)).inv.app J ≫
  (NatTrans.mapHomologicalComplex (supportComparison Λ k r p i h).hom (.up ℤ)).app J ≫
  (Functor.mapHomologicalComplexCompIso (Iso.refl
    (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) k ⋙
      lowerStar (ModuleCat.{u + 1} Λ) p)) (.up ℤ)).hom.app J ≫
  ((lowerStar (ModuleCat.{u + 1} Λ) p).mapHomologicalComplex (.up ℤ)).map t
```

```lean
def transposeArrow {V W S T : Scheme.{u}}
    (k : V ⟶ W) (r : V ⟶ S) (p : W ⟶ T) (i : S ⟶ T)
    [IsOpenImmersion k] [IsOpenImmersion i] [IsProper r] [IsProper p]
    (h : k ≫ p = r ≫ i)
    (J : CochainComplex (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ℤ)
    (I : CochainComplex (Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ℤ)
    (t : ((openImmersionLowerShriek (ModuleCat.{u + 1} Λ) k).mapHomologicalComplex
      (.up ℤ)).obj J ⟶ I) :
    ((upperStar (ModuleCat.{u + 1} Λ) p).mapHomologicalComplex (.up ℤ)).obj
        (((openImmersionLowerShriek (ModuleCat.{u + 1} Λ) i).mapHomologicalComplex (.up ℤ)).obj
          (((lowerStar (ModuleCat.{u + 1} Λ) r).mapHomologicalComplex (.up ℤ)).obj J)) ⟶ I :=
  (Functor.mapHomologicalComplexCompIso (Iso.refl
    (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) i ⋙
      upperStar (ModuleCat.{u + 1} Λ) p)) (.up ℤ)).inv.app
      (((lowerStar (ModuleCat.{u + 1} Λ) r).mapHomologicalComplex (.up ℤ)).obj J) ≫
  (NatTrans.mapHomologicalComplex (alpha Λ k r p i h) (.up ℤ)).app
    (((lowerStar (ModuleCat.{u + 1} Λ) r).mapHomologicalComplex (.up ℤ)).obj J) ≫
  (Functor.mapHomologicalComplexCompIso (Iso.refl
    (upperStar (ModuleCat.{u + 1} Λ) r ⋙
      openImmersionLowerShriek (ModuleCat.{u + 1} Λ) k)) (.up ℤ)).hom.app
      (((lowerStar (ModuleCat.{u + 1} Λ) r).mapHomologicalComplex (.up ℤ)).obj J) ≫
  ((openImmersionLowerShriek (ModuleCat.{u + 1} Λ) k).mapHomologicalComplex (.up ℤ)).map
    (((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) r).mapHomologicalComplex
      (.up ℤ)).counit.app J) ≫ t
```

```lean
def supportComparison [Finite Λ] {V W S T : Scheme.{u}}
    (k : V ⟶ W) (r : V ⟶ S) (p : W ⟶ T) (i : S ⟶ T)
    [IsOpenImmersion k] [IsOpenImmersion i] [IsProper r] [IsProper p]
    (h : k ≫ p = r ≫ i) :
    lowerStar (ModuleCat.{u + 1} Λ) r ⋙
        openImmersionLowerShriek (ModuleCat.{u + 1} Λ) i ≅
      openImmersionLowerShriek (ModuleCat.{u + 1} Λ) k ⋙
        lowerStar (ModuleCat.{u + 1} Λ) p :=
  (properOpenInterchangeCoherence Λ).choose k i r p h
```

```lean
def normalizedComparison [Finite Λ] {V W S T : Scheme.{u}}
    (k : V ⟶ W) (r : V ⟶ S) (p : W ⟶ T) (i : S ⟶ T)
    [IsOpenImmersion k] [IsOpenImmersion i] [IsProper r] [IsProper p]
    (h : k ≫ p = r ≫ i) :
    (lowerStar (ModuleCat.{u + 1} Λ) r).rightDerivedFunctorPlus ⋙
        (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) i).mapDerivedCategoryPlus ≅
      (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) k).mapDerivedCategoryPlus ⋙
        (lowerStar (ModuleCat.{u + 1} Λ) p).rightDerivedFunctorPlus :=
  (properOpenInterchangeCoherence Λ).choose_spec.choose k i r p h
```

```lean
def mate {V W S T : Scheme.{u}} (k : V ⟶ W) (r : V ⟶ S)
    (p : W ⟶ T) (i : S ⟶ T) [IsOpenImmersion k] [IsOpenImmersion i]
    [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i) :
    lowerStar (ModuleCat.{u + 1} Λ) r ⋙
        openImmersionLowerShriek (ModuleCat.{u + 1} Λ) i ⟶
      openImmersionLowerShriek (ModuleCat.{u + 1} Λ) k ⋙
        lowerStar (ModuleCat.{u + 1} Λ) p :=
  mateEquiv (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) r)
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) p) (alpha Λ k r p i h)
```

```lean
def derivedAlpha {V W S T : Scheme.{u}} (k : V ⟶ W) (r : V ⟶ S)
    (p : W ⟶ T) (i : S ⟶ T) [IsOpenImmersion k] [IsOpenImmersion i]
    [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i) :
    (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) i).mapDerivedCategory ⋙
        (upperStar (ModuleCat.{u + 1} Λ) p).mapDerivedCategory ⟶
      (upperStar (ModuleCat.{u + 1} Λ) r).mapDerivedCategory ⋙
        (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) k).mapDerivedCategory :=
  (Functor.mapDerivedCategoryCompIso
    (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) i)
    (upperStar (ModuleCat.{u + 1} Λ) p)).inv ≫
  Localization.liftNatTrans DerivedCategory.Q
    (HomologicalComplex.quasiIso
      (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (.up ℤ))
    _ _ _ _
    (Functor.whiskerRight
      (NatTrans.mapHomologicalComplex (alpha Λ k r p i h) (.up ℤ)) DerivedCategory.Q) ≫
  (Functor.mapDerivedCategoryCompIso (upperStar (ModuleCat.{u + 1} Λ) r)
    (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) k)).hom
```

```lean
def derivedAlphaPlus {V W S T : Scheme.{u}} (k : V ⟶ W) (r : V ⟶ S)
    (p : W ⟶ T) (i : S ⟶ T) [IsOpenImmersion k] [IsOpenImmersion i]
    [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i) :
    (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) i).mapDerivedCategoryPlus ⋙
        (upperStar (ModuleCat.{u + 1} Λ) p).mapDerivedCategoryPlus ⟶
      (upperStar (ModuleCat.{u + 1} Λ) r).mapDerivedCategoryPlus ⋙
        (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) k).mapDerivedCategoryPlus :=
  letI : Localization.Lifting DerivedCategory.Plus.Qh
      (HomotopyCategory.Plus.quasiIso
        (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
      (((openImmersionLowerShriek (ModuleCat.{u + 1} Λ) i) ⋙
        upperStar (ModuleCat.{u + 1} Λ) p).mapHomotopyCategoryPlus ⋙
          DerivedCategory.Plus.Qh)
      (((openImmersionLowerShriek (ModuleCat.{u + 1} Λ) i) ⋙
        upperStar (ModuleCat.{u + 1} Λ) p).mapDerivedCategoryPlus) :=
    ⟨((openImmersionLowerShriek (ModuleCat.{u + 1} Λ) i) ⋙
      upperStar (ModuleCat.{u + 1} Λ) p).mapDerivedCategoryPlusFactorsh⟩
  letI : Localization.Lifting DerivedCategory.Plus.Qh
      (HomotopyCategory.Plus.quasiIso
        (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
      (((upperStar (ModuleCat.{u + 1} Λ) r) ⋙
        openImmersionLowerShriek (ModuleCat.{u + 1} Λ) k).mapHomotopyCategoryPlus ⋙
          DerivedCategory.Plus.Qh)
      (((upperStar (ModuleCat.{u + 1} Λ) r) ⋙
        openImmersionLowerShriek (ModuleCat.{u + 1} Λ) k).mapDerivedCategoryPlus) :=
    ⟨((upperStar (ModuleCat.{u + 1} Λ) r) ⋙
      openImmersionLowerShriek (ModuleCat.{u + 1} Λ) k).mapDerivedCategoryPlusFactorsh⟩
  (Functor.mapDerivedCategoryPlusCompIso
    (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) i)
    (upperStar (ModuleCat.{u + 1} Λ) p)).inv ≫
  Localization.liftNatTrans DerivedCategory.Plus.Qh
    (HomotopyCategory.Plus.quasiIso
      (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    _ _ _ _
    (Functor.whiskerRight
      (NatTrans.mapHomotopyCategoryPlus (alpha Λ k r p i h)) DerivedCategory.Plus.Qh) ≫
  (Functor.mapDerivedCategoryPlusCompIso (upperStar (ModuleCat.{u + 1} Λ) r)
    (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) k)).hom
```

```lean
def sourceCompatibility {V S T : Scheme.{u}} (r : V ⟶ S) (i : S ⟶ T)
    [IsOpenImmersion i]
    (L : DerivedCategory.Plus (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :=
  ((openImmersionLowerShriek (ModuleCat.{u + 1} Λ) i).mapDerivedCategoryPlusCompatibility.app
    ((lowerStar (ModuleCat.{u + 1} Λ) r).rightDerivedFunctorPlus.obj L)) ≪≫
  (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) i).mapDerivedCategory.mapIso
    ((lowerStar (ModuleCat.{u + 1} Λ) r).rightDerivedFunctorPlusCompatibility.app L)
```

```lean
def targetCompatibility {V W T : Scheme.{u}} (k : V ⟶ W) (p : W ⟶ T)
    [IsOpenImmersion k]
    (L : DerivedCategory.Plus (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :=
  ((lowerStar (ModuleCat.{u + 1} Λ) p).rightDerivedFunctorPlusCompatibility.app
    ((openImmersionLowerShriek (ModuleCat.{u + 1} Λ) k).mapDerivedCategoryPlus.obj L)) ≪≫
  (lowerStar (ModuleCat.{u + 1} Λ) p).rightDerivedFunctor.mapIso
    ((openImmersionLowerShriek (ModuleCat.{u + 1} Λ) k).mapDerivedCategoryPlusCompatibility.app L)
```

## New

```lean
@[no_expose] def alpha {V W S T : Scheme.{u}} (k : V ⟶ W) (r : V ⟶ S)
    (p : W ⟶ T) (i : S ⟶ T) [IsOpenImmersion k] [IsOpenImmersion i]
    [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i) :
    openImmersionLowerShriek (ModuleCat.{u + 1} Λ) i ⋙
        upperStar (ModuleCat.{u + 1} Λ) p ⟶
      upperStar (ModuleCat.{u + 1} Λ) r ⋙
        openImmersionLowerShriek (ModuleCat.{u + 1} Λ) k :=
  let s := pullback.lift k r h
  letI := (lift_clopen k r p i h).1
  letI := (lift_clopen k r p i h).2
  let q := pullback.snd p i
  let b := pullback.fst p i
  CategoryTheory.clopenMateComposite
    (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) i)
    (upperStar (ModuleCat.{u + 1} Λ) p)
    (upperStar (ModuleCat.{u + 1} Λ) q)
    (upperStar (ModuleCat.{u + 1} Λ) s)
    (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) s)
    (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) b)
    (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) k)
    (upperStar (ModuleCat.{u + 1} Λ) r)
    (@asIso _ _ _ _ _ (isIso_openImmersionLowerShriekBaseChangeMap
      (ModuleCat.{u + 1} Λ) (IsPullback.of_hasPullback p i).flip)).inv
    (projection Λ s)
    ((openImmersionLowerShriekComp (ModuleCat.{u + 1} Λ) s b).inv ≫
      (openCongr Λ (pullback.lift_fst k r h)).hom)
    ((upperStarComp (ModuleCat.{u + 1} Λ) s q).inv ≫
      (eqToIso (congrArg (upperStar (ModuleCat.{u + 1} Λ))
        (pullback.lift_snd k r h))).hom)
```

```lean
@[no_expose] def mate {V W S T : Scheme.{u}} (k : V ⟶ W) (r : V ⟶ S)
    (p : W ⟶ T) (i : S ⟶ T) [IsOpenImmersion k] [IsOpenImmersion i]
    [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i) :
    lowerStar (ModuleCat.{u + 1} Λ) r ⋙
        openImmersionLowerShriek (ModuleCat.{u + 1} Λ) i ⟶
      openImmersionLowerShriek (ModuleCat.{u + 1} Λ) k ⋙
        lowerStar (ModuleCat.{u + 1} Λ) p :=
  mateEquiv (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) r)
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) p) (alpha Λ k r p i h)
```

```lean
@[no_expose, irreducible] def clopenLocalizedSquare (σ : G ⋙ L' ⟶ L ⋙ G') :
    G.mapDerivedCategory ⋙ L'.mapDerivedCategory ⟶
      L.mapDerivedCategory ⋙ G'.mapDerivedCategory :=
  (Functor.mapDerivedCategoryCompIso G L').inv ≫
    Localization.liftNatTrans DerivedCategory.Q
      (HomologicalComplex.quasiIso C₂ (.up ℤ)) _ _ _ _
      (Functor.whiskerRight (NatTrans.mapHomologicalComplex σ (.up ℤ)) DerivedCategory.Q) ≫
    (Functor.mapDerivedCategoryCompIso L G').hom
```

```lean
@[no_expose, irreducible] def clopenLocalizedSquarePlus (σ : G ⋙ L' ⟶ L ⋙ G') :
    G.mapDerivedCategoryPlus ⋙ L'.mapDerivedCategoryPlus ⟶
      L.mapDerivedCategoryPlus ⋙ G'.mapDerivedCategoryPlus :=
  letI : Localization.Lifting DerivedCategory.Plus.Qh
      (HomotopyCategory.Plus.quasiIso C₂)
      ((G ⋙ L').mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh)
      (G ⋙ L').mapDerivedCategoryPlus := ⟨(G ⋙ L').mapDerivedCategoryPlusFactorsh⟩
  letI : Localization.Lifting DerivedCategory.Plus.Qh
      (HomotopyCategory.Plus.quasiIso C₂)
      ((L ⋙ G').mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh)
      (L ⋙ G').mapDerivedCategoryPlus := ⟨(L ⋙ G').mapDerivedCategoryPlusFactorsh⟩
  (Functor.mapDerivedCategoryPlusCompIso G L').inv ≫
    Localization.liftNatTrans DerivedCategory.Plus.Qh
      (HomotopyCategory.Plus.quasiIso C₂) _ _ _ _
      (Functor.whiskerRight (NatTrans.mapHomotopyCategoryPlus σ) DerivedCategory.Plus.Qh) ≫
    (Functor.mapDerivedCategoryPlusCompIso L G').hom
```

```lean
@[no_expose] def derivedAlpha {V W S T : Scheme.{u}} (k : V ⟶ W) (r : V ⟶ S)
    (p : W ⟶ T) (i : S ⟶ T) [IsOpenImmersion k] [IsOpenImmersion i]
    [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i) :
    (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) i).mapDerivedCategory ⋙
        (upperStar (ModuleCat.{u + 1} Λ) p).mapDerivedCategory ⟶
      (upperStar (ModuleCat.{u + 1} Λ) r).mapDerivedCategory ⋙
        (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) k).mapDerivedCategory :=
  clopenLocalizedSquare (alpha Λ k r p i h)
```

```lean
@[no_expose] def derivedAlphaPlus {V W S T : Scheme.{u}} (k : V ⟶ W) (r : V ⟶ S)
    (p : W ⟶ T) (i : S ⟶ T) [IsOpenImmersion k] [IsOpenImmersion i]
    [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i) :
    (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) i).mapDerivedCategoryPlus ⋙
        (upperStar (ModuleCat.{u + 1} Λ) p).mapDerivedCategoryPlus ⟶
      (upperStar (ModuleCat.{u + 1} Λ) r).mapDerivedCategoryPlus ⋙
        (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) k).mapDerivedCategoryPlus :=
  clopenLocalizedSquarePlus (alpha Λ k r p i h)
```

```lean
@[no_expose] def derivedMate {V W S T : Scheme.{u}} (k : V ⟶ W) (r : V ⟶ S)
    (p : W ⟶ T) (i : S ⟶ T) [IsOpenImmersion k] [IsOpenImmersion i]
    [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i) :
    (lowerStar (ModuleCat.{u + 1} Λ) r).rightDerivedFunctor ⋙
        (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) i).mapDerivedCategory ⟶
      (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) k).mapDerivedCategory ⋙
        (lowerStar (ModuleCat.{u + 1} Λ) p).rightDerivedFunctor :=
  (mateEquiv (mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) r)
    (mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) p)
    (derivedAlpha Λ k r p i h)).natTrans
```

```lean
def derivedMatePlus {V W S T : Scheme.{u}} (k : V ⟶ W) (r : V ⟶ S)
    (p : W ⟶ T) (i : S ⟶ T) [IsOpenImmersion k] [IsOpenImmersion i]
    [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i) :
    (lowerStar (ModuleCat.{u + 1} Λ) r).rightDerivedFunctorPlus ⋙
        (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) i).mapDerivedCategoryPlus ⟶
      (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) k).mapDerivedCategoryPlus ⋙
        (lowerStar (ModuleCat.{u + 1} Λ) p).rightDerivedFunctorPlus :=
  (mateEquiv (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) r).derivedPlus
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) p).derivedPlus
    (derivedAlphaPlus Λ k r p i h)).natTrans
```

```lean
@[no_expose] def resolutionArrow [Finite Λ] {V W S T : Scheme.{u}}
    (k : V ⟶ W) (r : V ⟶ S) (p : W ⟶ T) (i : S ⟶ T)
    [IsOpenImmersion k] [IsOpenImmersion i] [IsProper r] [IsProper p]
    (h : k ≫ p = r ≫ i)
    (J : CochainComplex (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ℤ)
    (I : CochainComplex (Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ℤ)
    (t : ((openImmersionLowerShriek (ModuleCat.{u + 1} Λ) k).mapHomologicalComplex
      (.up ℤ)).obj J ⟶ I) :
    ((openImmersionLowerShriek (ModuleCat.{u + 1} Λ) i).mapHomologicalComplex (.up ℤ)).obj
        (((lowerStar (ModuleCat.{u + 1} Λ) r).mapHomologicalComplex (.up ℤ)).obj J) ⟶
      ((lowerStar (ModuleCat.{u + 1} Λ) p).mapHomologicalComplex (.up ℤ)).obj I :=
  (NatTrans.mapHomologicalComplex (supportComparison Λ k r p i h).hom (.up ℤ)).app J ≫
  ((lowerStar (ModuleCat.{u + 1} Λ) p).mapHomologicalComplex (.up ℤ)).map t
```

```lean
@[no_expose] def transposeArrow {V W S T : Scheme.{u}}
    (k : V ⟶ W) (r : V ⟶ S) (p : W ⟶ T) (i : S ⟶ T)
    [IsOpenImmersion k] [IsOpenImmersion i] [IsProper r] [IsProper p]
    (h : k ≫ p = r ≫ i)
    (J : CochainComplex (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ℤ)
    (I : CochainComplex (Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ℤ)
    (t : ((openImmersionLowerShriek (ModuleCat.{u + 1} Λ) k).mapHomologicalComplex
      (.up ℤ)).obj J ⟶ I) :
    ((upperStar (ModuleCat.{u + 1} Λ) p).mapHomologicalComplex (.up ℤ)).obj
        (((openImmersionLowerShriek (ModuleCat.{u + 1} Λ) i).mapHomologicalComplex (.up ℤ)).obj
          (((lowerStar (ModuleCat.{u + 1} Λ) r).mapHomologicalComplex (.up ℤ)).obj J)) ⟶ I :=
  (NatTrans.mapHomologicalComplex (alpha Λ k r p i h) (.up ℤ)).app
    (((lowerStar (ModuleCat.{u + 1} Λ) r).mapHomologicalComplex (.up ℤ)).obj J) ≫
  ((openImmersionLowerShriek (ModuleCat.{u + 1} Λ) k).mapHomologicalComplex (.up ℤ)).map
    (((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) r).mapHomologicalComplex
      (.up ℤ)).counit.app J) ≫ t
```

```lean
@[no_expose] def supportComparison [Finite Λ] {V W S T : Scheme.{u}}
    (k : V ⟶ W) (r : V ⟶ S) (p : W ⟶ T) (i : S ⟶ T)
    [IsOpenImmersion k] [IsOpenImmersion i] [IsProper r] [IsProper p]
    (h : k ≫ p = r ≫ i) :
    lowerStar (ModuleCat.{u + 1} Λ) r ⋙
        openImmersionLowerShriek (ModuleCat.{u + 1} Λ) i ≅
      openImmersionLowerShriek (ModuleCat.{u + 1} Λ) k ⋙
        lowerStar (ModuleCat.{u + 1} Λ) p :=
  (properOpenInterchangeData Λ).underived k i r p h
```

```lean
def normalizedComparison [Finite Λ] {V W S T : Scheme.{u}}
    (k : V ⟶ W) (r : V ⟶ S) (p : W ⟶ T) (i : S ⟶ T)
    [IsOpenImmersion k] [IsOpenImmersion i] [IsProper r] [IsProper p]
    (h : k ≫ p = r ≫ i) :
    (lowerStar (ModuleCat.{u + 1} Λ) r).rightDerivedFunctorPlus ⋙
        (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) i).mapDerivedCategoryPlus ≅
      (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) k).mapDerivedCategoryPlus ⋙
        (lowerStar (ModuleCat.{u + 1} Λ) p).rightDerivedFunctorPlus :=
  (properOpenInterchangeCoherence Λ).choose_spec.choose k i r p h
```

```lean
def sourceCompatibility {V S T : Scheme.{u}} (r : V ⟶ S) (i : S ⟶ T)
    [IsOpenImmersion i]
    (L : DerivedCategory.Plus (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :=
  (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) i).mapDerivedCategory.mapIso
    ((lowerStar (ModuleCat.{u + 1} Λ) r).rightDerivedFunctorPlusCompatibility.app L)
```

```lean
def targetCompatibility {V W T : Scheme.{u}} (k : V ⟶ W) (p : W ⟶ T)
    [IsOpenImmersion k]
    (L : DerivedCategory.Plus (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :=
  ((lowerStar (ModuleCat.{u + 1} Λ) p).rightDerivedFunctorPlusCompatibility.app
    ((openImmersionLowerShriek (ModuleCat.{u + 1} Λ) k).mapDerivedCategoryPlus.obj L))
```

## Users

| module | group holding it | effect |
|---|---|---|
| `Sheaf.AlgebraicGeometry.EtaleClopenMateNormalization` | B5 | Proofs use the simplified maps; signatures have the same types. |
| `Sheaf.AlgebraicGeometry.FiniteClopenMateSiteTransport` | unclaimed | Uses `derivedMatePlus`; its type and value agree definitionally with the original square. No adaptation required. |
| `Sheaf.AlgebraicGeometry.FiniteClopenAlphaSiteTransport` | unclaimed | Uses the unchanged exact-localized alpha interface; no adaptation required. |
| `Sheaf.AlgebraicGeometry.SingleLevelFiniteProperOpenTransport` | unclaimed | Uses the same uniquely normalized comparison; no adaptation required. |
| `Sheaf.AlgebraicGeometry.StrictTowerProperOpenCalculus` | unclaimed | Retains conversion to the original coherence choice; no adaptation required. |
| `Sheaf.Paper.SystemCompatibleCompositorNormalization` | unclaimed | Imports the item transitively; no use of the changed construction bodies. No adaptation required. |

Current `tools/downstream.py` reports 541 transitive importers. A qualified-name
source search finds the four actual declaration consumers listed above; other
textual hits for `alpha` denote unrelated declarations. The table also includes the
retained transitive system-compositor check. The public names and result types
stay unchanged, and these original sources are checked against the repaired item.
The original strict-tower proof requires conversion to the original second
coherence choice. Attempts to unfold the bundled constructor were expensive;
keeping `normalizedComparison`'s original body preserves that conversion. The
item instead uses the proved bundle equation internally. No consumer is edited.
The final validation results are recorded in report.md.

The bundle projection API is proved by unfolding its explicit constructor:

```lean
theorem properOpenInterchangeData_derived (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] :
    ((properOpenInterchangeData Λ).derived : ProperOpenDerivedFamily Λ) =
      ((properOpenInterchangeCoherence Λ).choose_spec.choose : ProperOpenDerivedFamily Λ) := by
  unfold properOpenInterchangeData
  rfl
```

The new definition modules each carry a node, and contain no `sorry`. Their exact
implementations appear in the packet. The bundles add no mathematical assumptions.

## Status

landed 20261024T184610-L-3075477 2026-10-24 (merge of deliver/B5/Sheaf.AlgebraicGeometry.EtaleClopenMateNormalization)
