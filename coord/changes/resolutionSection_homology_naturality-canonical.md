# AlgebraicGeometry.Etale.resolutionSection_homology_naturality

## Reason

The old signature quantifies over arbitrary additive equivalences. The node instead
intends the canonical section/Ext comparisons. An independent sign change preserves
being an additive equivalence but destroys a nonzero restriction/transfer identity.
Specify the maps on representing Ext cocycles, using actual `InjectiveResolution.extMk`
and the already defined `etaleOpenObjectCohomologyMap`. This normalization contains
no restriction or transfer identity. The corrected theorem proves the same six
compatibilities for normalized comparisons, from two smaller naturality lemmas.
The single-scheme construction is stated separately. This is an interface repair and
a decomposition, not a proof of the false universal statement.

The existential statement of the sole caller, and all five Challenge statements, stay
verbatim unchanged. No target definition is changed. The blueprint unit route stays.

## Old

```lean
theorem resolutionSection_homology_naturality
    {X Y : Scheme.{u}} (g : Y ⟶ X)
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (I : InjectiveResolution G)
    (J : InjectiveResolution ((upperStar AddCommGrpCat.{u + 1} g).obj G))
    (α : I.cocomplex ⟶
      ((lowerStar AddCommGrpCat.{u + 1} g).mapHomologicalComplex (.up ℕ)).obj J.cocomplex)
    (hα : I.ι.f 0 ≫ α.f 0 =
      (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} g).unit.app G ≫
        (lowerStar AddCommGrpCat.{u + 1} g).map (J.ι.f 0))
    (eX : ∀ q : ℕ,
      (((etaleSectionFunctor (Scheme.Etale.mk (𝟙 X))).mapHomologicalComplex (.up ℕ)).obj
        I.cocomplex).homology q ≃+ Sheaf.H G q)
    (eOX : ∀ (W : X.Opens) (q : ℕ),
      (((etaleSectionFunctor (Scheme.Etale.mk W.ι)).mapHomologicalComplex (.up ℕ)).obj
        I.cocomplex).homology q ≃+
          Sheaf.H ((upperStar AddCommGrpCat.{u + 1} W.ι).obj G) q)
    (eY : ∀ q : ℕ,
      (((etaleSectionFunctor (Scheme.Etale.mk (𝟙 Y))).mapHomologicalComplex (.up ℕ)).obj
        J.cocomplex).homology q ≃+
          Sheaf.H ((upperStar AddCommGrpCat.{u + 1} g).obj G) q)
    (eOY : ∀ (W : Y.Opens) (q : ℕ),
      (((etaleSectionFunctor (Scheme.Etale.mk W.ι)).mapHomologicalComplex (.up ℕ)).obj
        J.cocomplex).homology q ≃+
          Sheaf.H ((upperStar AddCommGrpCat.{u + 1} W.ι).obj
            ((upperStar AddCommGrpCat.{u + 1} g).obj G)) q)
    : (∀ W q x, eOX W q (HomologicalComplex.homologyMap (etaleSectionMap
      (MorphismProperty.Over.homMk W.ι (Category.comp_id _) :
        Scheme.Etale.mk W.ι ⟶ Scheme.Etale.mk (𝟙 X)) I.cocomplex) q x) =
      cohomologyMap W.ι G q (eX q x)) ∧
    (∀ (A B : X.Opens) (h : A ≤ B) q x,
      eOX A q (HomologicalComplex.homologyMap (etaleSectionMap
        (MorphismProperty.Over.homMk (X.homOfLE h) (X.homOfLE_ι _) :
          Scheme.Etale.mk A.ι ⟶ Scheme.Etale.mk B.ι) I.cocomplex) q x) =
        openCohomologyRestriction h G q (eOX B q x)) ∧
    (∀ W q x, eOY W q (HomologicalComplex.homologyMap (etaleSectionMap
      (MorphismProperty.Over.homMk W.ι (Category.comp_id _) :
        Scheme.Etale.mk W.ι ⟶ Scheme.Etale.mk (𝟙 Y)) J.cocomplex) q x) =
      cohomologyMap W.ι ((upperStar AddCommGrpCat.{u + 1} g).obj G) q (eY q x)) ∧
    (∀ (A B : Y.Opens) (h : A ≤ B) q x,
      eOY A q (HomologicalComplex.homologyMap (etaleSectionMap
        (MorphismProperty.Over.homMk (Y.homOfLE h) (Y.homOfLE_ι _) :
          Scheme.Etale.mk A.ι ⟶ Scheme.Etale.mk B.ι) J.cocomplex) q x) =
        openCohomologyRestriction h ((upperStar AddCommGrpCat.{u + 1} g).obj G) q
          (eOY B q x)) ∧
    (∀ q x, eY q (HomologicalComplex.homologyMap
      (globalResolutionSectionTransfer g I.cocomplex J.cocomplex α) q x) =
      cohomologyMap g G q (eX q x)) ∧
    (∀ W q x, eOY (g ⁻¹ᵁ W) q (HomologicalComplex.homologyMap
      (openResolutionSectionTransfer g I.cocomplex J.cocomplex α W) q x) =
      openCohomologyPullback g W G q (eOX W q x))
```

## New

```lean
theorem resolutionSection_homology_naturality
    {X Y : Scheme.{u}} (g : Y ⟶ X)
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (I : InjectiveResolution G)
    (J : InjectiveResolution ((upperStar AddCommGrpCat.{u + 1} g).obj G))
    (α : I.cocomplex ⟶
      ((lowerStar AddCommGrpCat.{u + 1} g).mapHomologicalComplex (.up ℕ)).obj J.cocomplex)
    (hα : I.ι.f 0 ≫ α.f 0 =
      (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} g).unit.app G ≫
        (lowerStar AddCommGrpCat.{u + 1} g).map (J.ι.f 0))
    (cX : ResolutionSectionCanonicalComparison G I)
    (cY : ResolutionSectionCanonicalComparison
      ((upperStar AddCommGrpCat.{u + 1} g).obj G) J)
    : (∀ W q x, cX.openEquiv W q (HomologicalComplex.homologyMap (etaleSectionMap
      (MorphismProperty.Over.homMk W.ι (Category.comp_id _) :
        Scheme.Etale.mk W.ι ⟶ Scheme.Etale.mk (𝟙 X)) I.cocomplex) q x) =
      cohomologyMap W.ι G q (cX.globalEquiv q x)) ∧
    (∀ (A B : X.Opens) (h : A ≤ B) q x,
      cX.openEquiv A q (HomologicalComplex.homologyMap (etaleSectionMap
        (MorphismProperty.Over.homMk (X.homOfLE h) (X.homOfLE_ι _) :
          Scheme.Etale.mk A.ι ⟶ Scheme.Etale.mk B.ι) I.cocomplex) q x) =
        openCohomologyRestriction h G q (cX.openEquiv B q x)) ∧
    (∀ W q x, cY.openEquiv W q (HomologicalComplex.homologyMap (etaleSectionMap
      (MorphismProperty.Over.homMk W.ι (Category.comp_id _) :
        Scheme.Etale.mk W.ι ⟶ Scheme.Etale.mk (𝟙 Y)) J.cocomplex) q x) =
      cohomologyMap W.ι ((upperStar AddCommGrpCat.{u + 1} g).obj G) q (cY.globalEquiv q x)) ∧
    (∀ (A B : Y.Opens) (h : A ≤ B) q x,
      cY.openEquiv A q (HomologicalComplex.homologyMap (etaleSectionMap
        (MorphismProperty.Over.homMk (Y.homOfLE h) (Y.homOfLE_ι _) :
          Scheme.Etale.mk A.ι ⟶ Scheme.Etale.mk B.ι) J.cocomplex) q x) =
        openCohomologyRestriction h ((upperStar AddCommGrpCat.{u + 1} g).obj G) q
          (cY.openEquiv B q x)) ∧
    (∀ q x, cY.globalEquiv q (HomologicalComplex.homologyMap
      (globalResolutionSectionTransfer g I.cocomplex J.cocomplex α) q x) =
      cohomologyMap g G q (cX.globalEquiv q x)) ∧
    (∀ W q x, cY.openEquiv (g ⁻¹ᵁ W) q (HomologicalComplex.homologyMap
      (openResolutionSectionTransfer g I.cocomplex J.cocomplex α W) q x) =
      openCohomologyPullback g W G q (cX.openEquiv W q x))
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.EtaleResolutionSectionHomology | unclaimed | Forced proof/import adaptation; its existential signature and visibility are identical. Obtain normalized families for I and J before applying naturality. |

`tools/downstream.py Sheaf.AlgebraicGeometry.EtaleResolutionSectionHomologyNaturality
--uses resolutionSection_homology_naturality` found 163 transitive downstream modules.
Only `Sheaf.AlgebraicGeometry.EtaleResolutionSectionHomology` mentions the declaration
outside its defining module. Other downstream modules use the unchanged existential
interface and require no adaptation.

The forced module changes the proof-only import
`EtaleResolutionSectionHomologyData` to `EtaleResolutionSectionCanonicalData`, and
replaces its six-line witness/application proof by the six-line normalized
witness/application proof. The original against the changed dependencies fails at
the application to `eX`: its degreewise additive equivalence type is not
`ResolutionSectionCanonicalComparison G I`. The adapted module compiles.

## Status

landed 20261012T194154-L-469615 2026-10-12 (merge of deliver/W3/Sheaf.AlgebraicGeometry.EtaleResolutionSectionHomologyNaturality)
