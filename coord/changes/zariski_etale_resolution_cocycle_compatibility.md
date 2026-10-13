# zariski_etale_resolution_cocycle_compatibility

## Reason

The original universal assertion about arbitrary additive equivalences is false: negating
one equivalence changes one side of the asserted equality on a nonzero integer class.
The returned existential repair duplicated the unchanged parent homology theorem word for word.
This repair follows the return's instruction to generalize the component in place: prove
naturality for actual cycle classes under any chain map of abelian-group complexes.
It neither chooses nor constrains arbitrary additive equivalences. The unchanged parent
constructs normalized equivalences via the single-site normalization lemma and uses the
compatibility result to finish the comparison. No target or target-used definition changes.

Source: Stacks Project Section 01FT, equation-cohomology-object-site; Tag 06XR (1),
lemma-compute-ext-resolutions. The source passages were read in the earlier delivery.

## Old

```lean
theorem zariski_etale_resolution_cocycle_compatibility {X : Scheme.{u + 1}} (i : X.Opens ⥤ X.Etale) (hi : i.IsContinuous (Opens.grothendieckTopology X.carrier) X.smallEtaleTopology) [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u + 1}] [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u + 1}] [HasExt (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u + 1})] [HasExt (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})] (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (I : InjectiveResolution F) (R : InjectiveResolution ((i.sheafPushforwardContinuous AddCommGrpCat.{u + 1} (Opens.grothendieckTopology X.carrier) X.smallEtaleTopology).obj F)) (b : R.cocomplex ⟶ ((i.sheafPushforwardContinuous AddCommGrpCat.{u + 1} (Opens.grothendieckTopology X.carrier) X.smallEtaleTopology).mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex) (q : ℕ) (V : X.Opens) : ∀ (e₁ : Sheaf.H' ((i.sheafPushforwardContinuous AddCommGrpCat.{u + 1} (Opens.grothendieckTopology X.carrier) X.smallEtaleTopology).obj F) q V ≃+ ↑(HomologicalComplex.homology (((sheafToPresheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u + 1} ⋙ (evaluation X.Opensᵒᵖ AddCommGrpCat.{u + 1}).obj (op V)).mapHomologicalComplex (ComplexShape.up ℕ)).obj R.cocomplex) q)) (e₂ : Sheaf.H' F q (i.obj V) ≃+ ↑(HomologicalComplex.homology (((sheafToPresheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u + 1} ⋙ (evaluation X.Opensᵒᵖ AddCommGrpCat.{u + 1}).obj (op V)).mapHomologicalComplex (ComplexShape.up ℕ)).obj (((i.sheafPushforwardContinuous AddCommGrpCat.{u + 1} (Opens.grothendieckTopology X.carrier) X.smallEtaleTopology).mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex)) q)), ∀ (a : (presheafToSheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u + 1}).obj (yoneda.obj V ⋙ AddCommGrpCat.free) ⟶ R.cocomplex.X q) (ha : a ≫ R.cocomplex.d q (q + 1) = 0) (c : (presheafToSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj (yoneda.obj (i.obj V) ⋙ AddCommGrpCat.free) ⟶ I.cocomplex.X q) (hc : c ≫ I.cocomplex.d q (q + 1) = 0), (b.f q).hom.app (op V) ((a.hom.app (op V)).hom (((toSheafify (Opens.grothendieckTopology X.carrier) (yoneda.obj V ⋙ AddCommGrpCat.free)).app (op V)).hom (FreeAbelianGroup.of (𝟙 V)))) = ((c.hom.app (op (i.obj V))).hom (((toSheafify X.smallEtaleTopology (yoneda.obj (i.obj V) ⋙ AddCommGrpCat.free)).app (op (i.obj V))).hom (FreeAbelianGroup.of (𝟙 (i.obj V))))) → e₂ (I.extMk c (q + 1) rfl hc) = (HomologicalComplex.homologyMap (((sheafToPresheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u + 1} ⋙ (evaluation X.Opensᵒᵖ AddCommGrpCat.{u + 1}).obj (op V)).mapHomologicalComplex (ComplexShape.up ℕ)).map b) q).hom (e₁ (R.extMk a (q + 1) rfl ha))
```

## New

```lean
theorem zariski_etale_resolution_cocycle_compatibility {K L : CochainComplex AddCommGrpCat.{u + 1} ℕ} (f : K ⟶ L) (q : ℕ) (x : K.X q) (hx : (K.d q (q + 1)).hom x = 0) (y : L.X q) (hy : (L.d q (q + 1)).hom y = 0) (h : (f.f q).hom x = y) : (HomologicalComplex.homologyMap f q).hom (sectionCycleClass K q x hx) = sectionCycleClass L q y hy
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.ZariskiEtaleResolutionCocycleCompatibility | X2 | Generalized to actual cycle-class naturality; completely proved. |
| Sheaf.Paper.ZariskiEtaleResolutionCocycleHomology | unclaimed | Forced proof adaptation; signature and visibility unchanged. |

Only the homology module mentions the changed declaration. Its original proof passes site,
resolution, and equivalence arguments to the old signature. Against the new signature,
its `i` argument is a functor rather than a chain map, so the original fails to compile.
The adapted proof obtains normalized equivalences on each site, rewrites their Ext formulas,
and applies compatibility to the evaluated chain map and actual cycles. This is necessary
because compatibility is now strictly the naturality step, rather than a duplicate of the
parent existential theorem.
The normalization declarations are available through compatibility's public import;
all existing imports and public signatures are retained. No private
helper is added to the adapted module. The exact counterfactual error is recorded by deliver3.
The normalization module's public import in compatibility supplies the actual cycle-class
construction occurring in its signature. This import adds no data chosen from an existence
hole. The node of compatibility records the new generalized statement and naturality proof;
the homology node records normalization followed by this naturality. Unit realizations stay.

## Status

landed 20261013T022435-L-3223337 2026-10-13 (merge of deliver/X2/Sheaf.Paper.ZariskiEtaleResolutionCocycleCompatibility)
