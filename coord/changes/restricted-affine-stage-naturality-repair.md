# AlgebraicGeometry.Etale.restricted_affine_stage_naturality

## Reason

Reviewer X-dba85 correctly rejected naturality for arbitrary comparison isomorphisms.
The attempted repair with unconstrained `rCanonical` and `r = rCanonical` is vacuous:
choose `rCanonical := r`. In addition, arbitrary `psi` is unrelated to `phi`.
The source and node advertise the actual restricted single complexes. The corrected
helper fixes the diagram, complexes and transitions to the existing explicit definitions;
the cohomology comparisons are then identities, and unfolding proves the equation.

The original existential proof applied the false helper to arbitrary witnesses of
`exists_restricted_affine_coefficient_system`. That theorem supplies no stage comparison
and does not identify its transitions with the explicit ones. Retaining that proof would
retain the invalid inference. Its original statement and full source/proof docstring stay
byte-for-byte unchanged, but its proof is reopened as the named theorem's single `sorry`.
Attempts to verify a direct reconstruction exceeded the existing 60-second file limit;
no unverified reconstruction is delivered. This repairs the false statement and records
an unresolved proof, with zero net holes closed minus added. It is not a proof of the
old false statement or a completion of the existential theorem.

No definition or target statement changes. Challenge does not name the corrected helper.

## Old

```lean
theorem restricted_affine_stage_naturality {S : Scheme.{v}} {I : Type v} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I] (D : Iᵒᵖ ⥤ Over S) (c : Cone D) (hc : IsLimit ((Over.forget S).mapCone c)) (F : ∀ i : I, Sheaf (D.obj (op i)).left.smallEtaleTopology AddCommGrpCat.{v + 1}) (φ : ∀ {i j : I} (f : i ⟶ j), (((D.map f.op).left)^*[AddCommGrpCat.{v + 1}]).obj (F i) ⟶ F j) (hφid : ∀ i : I, HEq (φ (𝟙 i)) ((upperStarId AddCommGrpCat.{v + 1} (D.obj (op i)).left).hom.app (F i))) (hφcomp : ∀ {i j k : I} (f : i ⟶ j) (g : j ⟶ k), HEq (φ (f ≫ g)) ((upperStarComp AddCommGrpCat.{v + 1} (D.map g.op).left (D.map f.op).left).hom.app (F i) ≫ (((D.map g.op).left)^*[AddCommGrpCat.{v + 1}]).map (φ f) ≫ φ g)) (H : I ⥤ Sheaf c.pt.left.smallEtaleTopology AddCommGrpCat.{v + 1}) (eH : ∀ i : I, H.obj i ≅ (((c.π.app (op i)).left)^*[AddCommGrpCat.{v + 1}]).obj (F i)) (hH : ∀ {i j : I} (f : i ⟶ j), H.map f = (eH i).hom ≫ (upperStarComp AddCommGrpCat.{v + 1} (c.π.app (op j)).left (D.map f.op).left (c.π.app (op i)).left (congrArg (fun t => t.left) (c.w f.op)).symm).hom.app (F i) ≫ (((c.π.app (op j)).left)^*[AddCommGrpCat.{v + 1}]).map (φ f) ≫ (eH j).inv) [HasColimit H] (p : ℕ) (U : S.Etale) [IsAffine U.left] (D' : Iᵒᵖ ⥤ Scheme.{v}) (c' : Cone D') (K : ∀ i : Iᵒᵖ, CochainComplex (Sheaf (D'.obj i).smallEtaleTopology AddCommGrpCat.{v + 1}) ℤ) (ψ : ∀ {i j : Iᵒᵖ} (f : j ⟶ i), ((upperStar AddCommGrpCat.{v + 1} (D'.map f)).mapHomologicalComplex (ComplexShape.up ℤ)).obj (K i) ⟶ K j) (G : (Iᵒᵖ)ᵒᵖ ⥤ CochainComplex (Sheaf c'.pt.smallEtaleTopology AddCommGrpCat.{v + 1}) ℤ) (eG : ∀ i : Iᵒᵖ, G.obj (op i) ≅ ((upperStar AddCommGrpCat.{v + 1} (c'.π.app i)).mapHomologicalComplex (ComplexShape.up ℤ)).obj (K i)) (L : Cocone G) (r : ∀ i : Iᵒᵖ, rawAffineRestrictedCohomology (D.obj (op i.unop)).hom p (F i.unop) U ≅ (cohomology AddCommGrpCat.{v + 1} (D'.obj i) (p : ℤ)).obj (DerivedCategory.Q.obj (K i))) : ∀ {i j : I} (f : i ⟶ j), (r (op i)).hom ≫ rawAffineComplexPullback (p : ℤ) (D'.map f.op) (K (op i)) ≫ (cohomology AddCommGrpCat.{v + 1} (D'.obj (op j)) (p : ℤ)).map (DerivedCategory.Q.map (ψ f.op)) = rawAffineRestrictedCohomologyMap (D.map f.op).left (D.obj (op i)).hom (D.obj (op j)).hom (Over.w (D.map f.op)) p (F i) (F j) (φ f) U ≫ (r (op j)).hom
```

The existential theorem's old proof body was:

```lean
:= by
  obtain ⟨D', c', hc', compact, qs, affine, K, ψ, hid, hcomp, hbelow,
    G, eG, hG, L, hL, hbelowL, r, rL, hr⟩ :=
    exists_restricted_affine_coefficient_system D c hc F φ hφid hφcomp H eH hH p U
  refine ⟨D', c', hc', compact, qs, affine, K, ψ, hid, hcomp, hbelow,
    G, eG, hG, L, hL, hbelowL, r, rL, hr, ?_⟩
  exact restricted_affine_stage_naturality D c hc F φ hφid hφcomp H eH hH p U
    D' c' K ψ G eG L r

```

## New

```lean
theorem restricted_affine_stage_naturality {S : Scheme.{v}} {I : Type v} [Preorder I] (D : Iᵒᵖ ⥤ Over S) (F : ∀ i : I, Sheaf (D.obj (op i)).left.smallEtaleTopology AddCommGrpCat.{v + 1}) (φ : ∀ {i j : I} (f : i ⟶ j), (((D.map f.op).left)^*[AddCommGrpCat.{v + 1}]).obj (F i) ⟶ F j) (p : ℕ) (U : S.Etale) : ∀ {i j : Iᵒᵖ} (f : j ⟶ i), rawAffineComplexPullback (p : ℤ) ((restrictedAffineDiagram D U).map f) (restrictedAffineK D F U i) ≫ (cohomology AddCommGrpCat.{v + 1} ((restrictedAffineDiagram D U).obj j) (p : ℤ)).map (DerivedCategory.Q.map (restrictedAffineSingleTransition D F φ U f)) = rawAffineRestrictedCohomologyMap (D.map f).left (D.obj i).hom (D.obj j).hom (Over.w (D.map f)) p (F i.unop) (F j.unop) (φ f.unop) U
```

Its proof unfolds `restrictedAffineSingleTransition` and
`rawAffineRestrictedCohomologyMap`, then uses reflexivity.
The existential theorem has its identical signature and proof `:= by sorry`.

The public RawAffineRestrictedCohomology import remains available transitively through
the new public RestrictedAffineSingleMaps import, which the corrected helper signature
requires. The old proof-only RestrictedAffineCoefficientSystem import is removed.
The unused proof-only transition-law, cone-naturality and cone-leg imports are removed;
the reopened main theorem does not apply their declarations. Local transparency controls
do not change any definition or exported interface. No forced adaptations are needed.

## Users

`tools/downstream.py Sheaf.AlgebraicGeometry.RestrictedAffineNaturalCoefficientSystem --uses restricted_affine_stage_naturality`
found 167 downstream modules and only the held module uses the helper. All downstream
statements and definitions were checked for textual uses of the helper: none. The public
RawAffineRestrictedCohomology declarations remain available through the new public import.
The changed helper is not used in any target statement or downstream definition.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.RestrictedAffineNaturalCoefficientSystem | U1 | Helper corrected and proved; main existential signature unchanged; invalid proof reopened. |
| Sheaf.AlgebraicGeometry.AbelianRawCoconeComplexPresentation | unclaimed | No helper use; no definition or existential signature changed; no adaptation. |
| Sheaf.AlgebraicGeometry.AffineClosedEtaleNeighborhoodComparison | unclaimed | No helper use; no definition or existential signature changed; no adaptation. |
| Sheaf.AlgebraicGeometry.AffineClosedInjectiveAcyclic | unclaimed | No helper use; no definition or existential signature changed; no adaptation. |
| Sheaf.AlgebraicGeometry.BoundedAbelianClosedEffacement | unclaimed | No helper use; no definition or existential signature changed; no adaptation. |
| Sheaf.AlgebraicGeometry.ConstructibleModuleClosedEffacement | unclaimed | No helper use; no definition or existential signature changed; no adaptation. |
| Sheaf.AlgebraicGeometry.ConstructibleModuleFinitePushforwardEmbedding | unclaimed | No helper use; no definition or existential signature changed; no adaptation. |
| Sheaf.AlgebraicGeometry.ConstructibleModuleFinitePushforwardNoetherian | unclaimed | No helper use; no definition or existential signature changed; no adaptation. |
| Sheaf.AlgebraicGeometry.ConstructibleModuleIntegralMapFactorization | unclaimed | No helper use; no definition or existential signature changed; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.AlgebraicallyClosedCohomologyInvariant | unclaimed | No helper use; no definition or existential signature changed; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstantInvariance | unclaimed | No helper use; no definition or existential signature changed; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstructiblePrimeDevissage | unclaimed | No helper use; no definition or existential signature changed; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstructibleShortExactAssertions | unclaimed | No helper use; no definition or existential signature changed; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenAssertions | unclaimed | No helper use; no definition or existential signature changed; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenBaseChange | unclaimed | No helper use; no definition or existential signature changed; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenBaseChangeComparison | unclaimed | No helper use; no definition or existential signature changed; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenClosedTerm | unclaimed | No helper use; no definition or existential signature changed; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenCohomologyFiniteness | unclaimed | No helper use; no definition or existential signature changed; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenFinitenessComparison | unclaimed | No helper use; no definition or existential signature changed; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomology | unclaimed | No helper use; no definition or existential signature changed; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomologyHigh | unclaimed | No helper use; no definition or existential signature changed; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenIntegralCohomologyFiniteness | unclaimed | No helper use; no definition or existential signature changed; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenLowBaseChange | unclaimed | No helper use; no definition or existential signature changed; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimaryFiniteness | unclaimed | No helper use; no definition or existential signature changed; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimeAssertions | unclaimed | No helper use; no definition or existential signature changed; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenRestrictionComparison | unclaimed | No helper use; no definition or existential signature changed; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenVanishingComparison | unclaimed | No helper use; no definition or existential signature changed; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.EtaleCohomologicalDimension | unclaimed | No helper use; no definition or existential signature changed; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransfer | unclaimed | No helper use; no definition or existential signature changed; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransferCore | unclaimed | No helper use; no definition or existential signature changed; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.FiniteSupportPrimeGlobalSections | unclaimed | No helper use; no definition or existential signature changed; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecond | unclaimed | No helper use; no definition or existential signature changed; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecondReduction | unclaimed | No helper use; no definition or existential signature changed; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.GenericPrimeFiltrationStep | unclaimed | No helper use; no definition or existential signature changed; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.GenericVanishingKernelColimit | unclaimed | No helper use; no definition or existential signature changed; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.NormalizationAssertionsTransfer | unclaimed | No helper use; no definition or existential signature changed; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.OpenCurveGmDirectImageCohomology | unclaimed | No helper use; no definition or existential signature changed; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.OpenLowerShriekConstantFiltrationSteps | unclaimed | No helper use; no definition or existential signature changed; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PrimeCoefficientCurveAssertions | unclaimed | No helper use; no definition or existential signature changed; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ProperCohomology | unclaimed | No helper use; no definition or existential signature changed; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ProperConstantBaseChangeHigher | unclaimed | No helper use; no definition or existential signature changed; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekAssertions | unclaimed | No helper use; no definition or existential signature changed; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekReduction | unclaimed | No helper use; no definition or existential signature changed; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.SmoothConstantLowerShriekLocalization | unclaimed | No helper use; no definition or existential signature changed; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleGrothendieckSpectralSequence | unclaimed | No helper use; no definition or existential signature changed; no adaptation. |
| Sheaf.AlgebraicGeometry.HenselianBoundedAbelianComparisonStep | unclaimed | No helper use; no definition or existential signature changed; no adaptation. |
| Sheaf.AlgebraicGeometry.HenselianBoundedAbelianSurjectivity | unclaimed | No helper use; no definition or existential signature changed; no adaptation. |
| Sheaf.AlgebraicGeometry.HigherDirectImageAffineComputationVanishing | unclaimed | No helper use; no definition or existential signature changed; no adaptation. |
| Sheaf.AlgebraicGeometry.HigherDirectImageAffineSectionVanishing | unclaimed | No helper use; no definition or existential signature changed; no adaptation. |
| Sheaf.AlgebraicGeometry.HigherDirectImageLimitClassVanishing | unclaimed | No helper use; no definition or existential signature changed; no adaptation. |
| Sheaf.AlgebraicGeometry.HigherDirectImageLimitSystem | unclaimed | No helper use; no definition or existential signature changed; no adaptation. |
| Sheaf.AlgebraicGeometry.HigherDirectImageLocalSectionVanishing | unclaimed | No helper use; no definition or existential signature changed; no adaptation. |
| Sheaf.AlgebraicGeometry.HigherDirectImageRawAffineColimitComparisonInjective | unclaimed | No helper use; no definition or existential signature changed; no adaptation. |
| Sheaf.AlgebraicGeometry.HigherDirectImageRawAffineRestrictionVanishing | unclaimed | No helper use; no definition or existential signature changed; no adaptation. |
| Sheaf.AlgebraicGeometry.HigherDirectImageRawLocalClassVanishing | unclaimed | No helper use; no definition or existential signature changed; no adaptation. |
| Sheaf.AlgebraicGeometry.IntegralConstantModulePushforwardColimit | unclaimed | No helper use; no definition or existential signature changed; no adaptation. |
| Sheaf.AlgebraicGeometry.ProjectiveLineGeometricStalkReduction | unclaimed | No helper use; no definition or existential signature changed; no adaptation. |
| Sheaf.AlgebraicGeometry.ProjectiveLineStrictLocalModelComparison | unclaimed | No helper use; no definition or existential signature changed; no adaptation. |
| Sheaf.AlgebraicGeometry.ProjectiveSpaceBaseChangeReduction | unclaimed | No helper use; no definition or existential signature changed; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperBaseChangeCompositionStability | unclaimed | No helper use; no definition or existential signature changed; no adaptation. |
| Sheaf.AlgebraicGeometry.RestrictedAffineComplexSystemNatural | unclaimed | No helper use; no definition or existential signature changed; no adaptation. |
| Sheaf.AlgebraicGeometry.TorsionAbelianBaseChangeCancellation | unclaimed | No helper use; no definition or existential signature changed; no adaptation. |
| Sheaf.AlgebraicGeometry.TorsionAssembly | unclaimed | No helper use; no definition or existential signature changed; no adaptation. |
| Sheaf.AlgebraicGeometry.TorsionFilteredUnion | unclaimed | No helper use; no definition or existential signature changed; no adaptation. |
| Sheaf.Paper.OpenCurveEtaleLerayLowDegree | unclaimed | No helper use; no definition or existential signature changed; no adaptation. |
| TargetsCheck | unclaimed | No helper use; no definition or existential signature changed; no adaptation. |
| WeilConjectures | unclaimed | No helper use; no definition or existential signature changed; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.Affine | unclaimed | No helper use; no definition or existential signature changed; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.CohomologicalDimension | unclaimed | No helper use; no definition or existential signature changed; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.FieldExtension | unclaimed | No helper use; no definition or existential signature changed; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.GenericComparison | unclaimed | No helper use; no definition or existential signature changed; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.HighDegreeVanishing | unclaimed | No helper use; no definition or existential signature changed; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.Reductions | unclaimed | No helper use; no definition or existential signature changed; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.SmoothCalculations | unclaimed | No helper use; no definition or existential signature changed; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Degreewise | unclaimed | No helper use; no definition or existential signature changed; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius | unclaimed | No helper use; no definition or existential signature changed; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Equivariance | unclaimed | No helper use; no definition or existential signature changed; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Pairings | unclaimed | No helper use; no definition or existential signature changed; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Reciprocity | unclaimed | No helper use; no definition or existential signature changed; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Pairing | unclaimed | No helper use; no definition or existential signature changed; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect | unclaimed | No helper use; no definition or existential signature changed; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceCup | unclaimed | No helper use; no definition or existential signature changed; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceIsomorphism | unclaimed | No helper use; no definition or existential signature changed; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Transport | unclaimed | No helper use; no definition or existential signature changed; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine | unclaimed | No helper use; no definition or existential signature changed; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace | unclaimed | No helper use; no definition or existential signature changed; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Basic | unclaimed | No helper use; no definition or existential signature changed; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBaseChange | unclaimed | No helper use; no definition or existential signature changed; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass | unclaimed | No helper use; no definition or existential signature changed; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Orientation | unclaimed | No helper use; no definition or existential signature changed; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion | unclaimed | No helper use; no definition or existential signature changed; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Transport | unclaimed | No helper use; no definition or existential signature changed; no adaptation. |
| WeilConjectures.FourierTransform.AffineSpace | unclaimed | No helper use; no definition or existential signature changed; no adaptation. |
| WeilConjectures.FourierTransform.AffineSpace.KernelTransform | unclaimed | No helper use; no definition or existential signature changed; no adaptation. |
| WeilConjectures.FourierTransform.AffineSpace.Transform | unclaimed | No helper use; no definition or existential signature changed; no adaptation. |
| WeilConjectures.FourierTransform.Defs | unclaimed | No helper use; no definition or existential signature changed; no adaptation. |
| WeilConjectures.FourierTransform.Inversion | unclaimed | No helper use; no definition or existential signature changed; no adaptation. |
| WeilConjectures.FourierTransform.Perverse | unclaimed | No helper use; no definition or existential signature changed; no adaptation. |
| WeilConjectures.FourierTransform.Properties | unclaimed | No helper use; no definition or existential signature changed; no adaptation. |
| WeilConjectures.FourierTransform.Properties.BaseChange | unclaimed | No helper use; no definition or existential signature changed; no adaptation. |
| WeilConjectures.FourierTransform.Properties.BaseLinear | unclaimed | No helper use; no definition or existential signature changed; no adaptation. |
| WeilConjectures.FourierTransform.Properties.Stalk | unclaimed | No helper use; no definition or existential signature changed; no adaptation. |
| WeilConjectures.SixFunctors.ClosedImmersionStages | unclaimed | No helper use; no definition or existential signature changed; no adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine | ORCHESTRA | No helper use; no definition or existential signature changed; no adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.GeometricStalk | unclaimed | No helper use; no definition or existential signature changed; no adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.StrictHenselian | unclaimed | No helper use; no definition or existential signature changed; no adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper | unclaimed | No helper use; no definition or existential signature changed; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Adjunctions | unclaimed | No helper use; no definition or existential signature changed; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.BoundaryDuality | unclaimed | No helper use; no definition or existential signature changed; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Composition | unclaimed | No helper use; no definition or existential signature changed; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.CupProductWeil | unclaimed | No helper use; no definition or existential signature changed; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Exchange | unclaimed | No helper use; no definition or existential signature changed; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness | unclaimed | No helper use; no definition or existential signature changed; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage | unclaimed | No helper use; no definition or existential signature changed; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality | unclaimed | No helper use; no definition or existential signature changed; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | unclaimed | No helper use; no definition or existential signature changed; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform | unclaimed | No helper use; no definition or existential signature changed; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Composition | unclaimed | No helper use; no definition or existential signature changed; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Finite | unclaimed | No helper use; no definition or existential signature changed; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Tensor | unclaimed | No helper use; no definition or existential signature changed; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth | unclaimed | No helper use; no definition or existential signature changed; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Comparisons | unclaimed | No helper use; no definition or existential signature changed; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs | unclaimed | No helper use; no definition or existential signature changed; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Relative | unclaimed | No helper use; no definition or existential signature changed; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Shriek | unclaimed | No helper use; no definition or existential signature changed; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationBaseChange | unclaimed | No helper use; no definition or existential signature changed; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange | unclaimed | No helper use; no definition or existential signature changed; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift | unclaimed | No helper use; no definition or existential signature changed; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence | unclaimed | No helper use; no definition or existential signature changed; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition | unclaimed | No helper use; no definition or existential signature changed; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalism | unclaimed | No helper use; no definition or existential signature changed; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalismComparison | unclaimed | No helper use; no definition or existential signature changed; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependence | unclaimed | No helper use; no definition or existential signature changed; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded | unclaimed | No helper use; no definition or existential signature changed; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange | unclaimed | No helper use; no definition or existential signature changed; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange | unclaimed | No helper use; no definition or existential signature changed; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionRefinement | unclaimed | No helper use; no definition or existential signature changed; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionShift | unclaimed | No helper use; no definition or existential signature changed; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekTransport | unclaimed | No helper use; no definition or existential signature changed; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekLowerStarExchange | unclaimed | No helper use; no definition or existential signature changed; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Orientation | unclaimed | No helper use; no definition or existential signature changed; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.OrientationDatum | unclaimed | No helper use; no definition or existential signature changed; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Package | unclaimed | No helper use; no definition or existential signature changed; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekBaseChange | unclaimed | No helper use; no definition or existential signature changed; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekProjection | unclaimed | No helper use; no definition or existential signature changed; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability | unclaimed | No helper use; no definition or existential signature changed; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage | unclaimed | No helper use; no definition or existential signature changed; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation | unclaimed | No helper use; no definition or existential signature changed; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Matrix | unclaimed | No helper use; no definition or existential signature changed; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion | unclaimed | No helper use; no definition or existential signature changed; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek | unclaimed | No helper use; no definition or existential signature changed; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriekConstructible | unclaimed | No helper use; no definition or existential signature changed; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Supports | unclaimed | No helper use; no definition or existential signature changed; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.TensorHom | unclaimed | No helper use; no definition or existential signature changed; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso | unclaimed | No helper use; no definition or existential signature changed; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplex | unclaimed | No helper use; no definition or existential signature changed; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius | unclaimed | No helper use; no definition or existential signature changed; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Gabber | unclaimed | No helper use; no definition or existential signature changed; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | unclaimed | No helper use; no definition or existential signature changed; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.AlgClosedExtension | unclaimed | No helper use; no definition or existential signature changed; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived | unclaimed | No helper use; no definition or existential signature changed; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Induction | unclaimed | No helper use; no definition or existential signature changed; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Theorem | unclaimed | No helper use; no definition or existential signature changed; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Vanishing | unclaimed | No helper use; no definition or existential signature changed; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange | unclaimed | No helper use; no definition or existential signature changed; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Derived.ClosedImmersionUpperShriek | unclaimed | No helper use; no definition or existential signature changed; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Derived.Perfect | unclaimed | No helper use; no definition or existential signature changed; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriekComposition | unclaimed | No helper use; no definition or existential signature changed; no adaptation. |

## Status

landed 20261013T201810-L-3977531 2026-10-13 (merge of deliver/U1/Sheaf.AlgebraicGeometry.RestrictedAffineNaturalCoefficientSystem)
