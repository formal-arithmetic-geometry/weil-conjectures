# Etale.ClopenMateNormalization component API

## Reason

The site-transport proof needs the canonical factorization of the existing exact
localized square and the components of the prescribed alpha. The definitions
`clopenLocalizedSquarePlus`, `alpha`, and `derivedAlphaPlus` have hidden bodies
(`@[no_expose]`); the existing factorization lemma is private. Add proved public
wrappers so consumers can use these constructions without unfolding hidden data.
The module is unclaimed at inspection. No existing declaration, attribute,
instance, import, signature, definition body, or proof is changed.

## Old

No public declarations named `clopenLocalizedSquarePlus_factorization`,
`alpha_app`, or `derivedAlphaPlus_eq`. The original private factorization
signature, verbatim, in `AlgebraicGeometry.Etale.ClopenMateNormalization`:

```lean
private theorem clopenLocalizedSquarePlus_fac (σ : G ⋙ L' ⟶ L ⋙ G')
    (K : HomotopyCategory.Plus C₂) :
    (clopenLocalizedSquarePlus σ).app (DerivedCategory.Plus.Qh.obj K) ≫
        G'.mapDerivedCategoryPlus.map (L.mapDerivedCategoryPlusFactorsh.hom.app K) ≫
        G'.mapDerivedCategoryPlusFactorsh.hom.app (L.mapHomotopyCategoryPlus.obj K) =
      L'.mapDerivedCategoryPlus.map (G.mapDerivedCategoryPlusFactorsh.hom.app K) ≫
        L'.mapDerivedCategoryPlusFactorsh.hom.app (G.mapHomotopyCategoryPlus.obj K) ≫
        DerivedCategory.Plus.Qh.map ((NatTrans.mapHomotopyCategoryPlus σ).app K)
```

## New

Three proved theorem wrappers, in the existing namespace:

```lean
theorem clopenLocalizedSquarePlus_factorization (σ : G ⋙ L' ⟶ L ⋙ G')
    (K : HomotopyCategory.Plus C₂) :
    (clopenLocalizedSquarePlus σ).app (DerivedCategory.Plus.Qh.obj K) ≫
        G'.mapDerivedCategoryPlus.map (L.mapDerivedCategoryPlusFactorsh.hom.app K) ≫
        G'.mapDerivedCategoryPlusFactorsh.hom.app (L.mapHomotopyCategoryPlus.obj K) =
      L'.mapDerivedCategoryPlus.map (G.mapDerivedCategoryPlusFactorsh.hom.app K) ≫
        L'.mapDerivedCategoryPlusFactorsh.hom.app (G.mapHomotopyCategoryPlus.obj K) ≫
        DerivedCategory.Plus.Qh.map ((NatTrans.mapHomotopyCategoryPlus σ).app K) := by
  exact clopenLocalizedSquarePlus_fac σ K

theorem alpha_app {V W S T : Scheme.{u}} (k : V ⟶ W) (r : V ⟶ S)
    (p : W ⟶ T) (i : S ⟶ T) [IsOpenImmersion k] [IsOpenImmersion i]
    [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i)
    (F : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    (alpha Λ k r p i h).app F =
      let s := pullback.lift k r h
      letI := (lift_clopen k r p i h).1
      letI := (lift_clopen k r p i h).2
      let q := pullback.snd p i
      let b := pullback.fst p i
      (@asIso _ _ _ _ _ (isIso_openImmersionLowerShriekBaseChangeMap
        (ModuleCat.{u + 1} Λ) (IsPullback.of_hasPullback p i).flip)).inv.app F ≫
      (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) b).map
        ((projection Λ s).app ((upperStar (ModuleCat.{u + 1} Λ) q).obj F)) ≫
      ((openImmersionLowerShriekComp (ModuleCat.{u + 1} Λ) s b).inv ≫
        (openCongr Λ (pullback.lift_fst k r h)).hom).app
          ((upperStar (ModuleCat.{u + 1} Λ) s).obj
            ((upperStar (ModuleCat.{u + 1} Λ) q).obj F)) ≫
      (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) k).map
        (((upperStarComp (ModuleCat.{u + 1} Λ) s q).inv ≫
          (eqToIso (congrArg (upperStar (ModuleCat.{u + 1} Λ))
            (pullback.lift_snd k r h))).hom).app F) := by
  let s := pullback.lift k r h
  let := (lift_clopen k r p i h).1
  let := (lift_clopen k r p i h).2
  let q := pullback.snd p i
  let b := pullback.fst p i
  exact CategoryTheory.clopenMateComposite_app
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
        (pullback.lift_snd k r h))).hom) F

theorem derivedAlphaPlus_eq {V W S T : Scheme.{u}} (k : V ⟶ W) (r : V ⟶ S)
    (p : W ⟶ T) (i : S ⟶ T) [IsOpenImmersion k] [IsOpenImmersion i]
    [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i) :
    derivedAlphaPlus Λ k r p i h = clopenLocalizedSquarePlus (alpha Λ k r p i h) := by
  rfl
```

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.PurityWitnessedMateNormalization | unclaimed at inspection | Existing API unchanged; checked as an original direct importer. |
| Sheaf.AlgebraicGeometry.FiniteClopenMateSiteTransport | unclaimed at inspection | Existing API unchanged; checked as an original direct importer. |
| Sheaf.Paper.FiniteRefinementAmbientNormalization | unclaimed at inspection | Existing API unchanged; checked as an original direct importer. |
| Sheaf.Paper.FiniteCompactSupportEvaluationRefinement | unclaimed at inspection | Existing API unchanged; checked as an original direct importer. |
| Sheaf.AlgebraicGeometry.SingleLevelFiniteProperOpenTransport | unclaimed at inspection | Existing API unchanged; checked as an original direct importer. |
| Sheaf.AlgebraicGeometry.FiniteCoefficientClopenAlpha | unclaimed at inspection | Existing API unchanged; checked as an original direct importer. |
| Sheaf.AlgebraicGeometry.FiniteClopenAlphaSiteTransport | M6 | Uses the new proved API. |
| Sheaf.AlgebraicGeometry.FiniteClopenBetaSiteTransport | M6 | New factor statement; existing API unchanged. |
| Sheaf.AlgebraicGeometry.FiniteClopenTailSiteTransport | M6 | New factor statement; existing API unchanged. |

The only added public signatures mention already public objects from existing
public imports. No target definition changes, so no target statement review is
reopened. Three existing DAG records merely attach their additional proved API
lemmas. All six original direct consumers compiled successfully against the added API
(`lcompile.py`, result `c033a2b30cf45431753c9326`). Their unchanged sandbox
copies were removed afterwards. Direct consumers require no source adaptation.

## Status

landed 20261027T050621-L-245698 2026-10-27 (merge of deliver/M6/Sheaf.AlgebraicGeometry.FiniteClopenAlphaSiteTransport)
