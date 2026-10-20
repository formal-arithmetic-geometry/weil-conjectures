# AlgebraicGeometry.Etale.vectorIntegrationLocalTrace

## Reason

The genuine local overlap theorem must refer to the existing chart traces, while the
existence-and-uniqueness proof imports that overlap theorem. Move the concrete chart
constructions into a definition module to avoid an import cycle. This is a semantic
relocation, not a change to the coefficient, orientation, exchange map, or normalization.
It is not a split intended to shorten compilation. The canonical degree-zero and
cover-gluing results are independent mathematical lemmas.

## Old

These declarations, including the two already proved geometric theorems, occur in
`Sheaf.AlgebraicGeometry.VectorBundleIntegration`:

```lean
/-- Reuse concrete sheafification on each Zariski slice when elaborating finite-rank
module frames. This packages the existing Mathlib instance without a new assumption.
Source: blueprint order 1972, module frames (blueprint: def-amb-vector-integration). -/
instance vectorIntegrationZariskiWeakSheafify (S : Scheme.{u}) :
    ∀ V : S.Opens, HasWeakSheafify
      ((Opens.grothendieckTopology S).over V) AddCommGrpCat.{u} :=
  fun V ↦ sheafToPresheaf_isRightAdjoint ((Opens.grothendieckTopology S).over V)
    AddCommGrpCat.{u}

/-- Reuse the existing local-bijection characterization of sheafification on each slice.
Source: blueprint order 1972, module frames (blueprint: def-amb-vector-integration). -/
instance vectorIntegrationZariskiLocallyBijective (S : Scheme.{u}) :
    ∀ V : S.Opens,
      ((Opens.grothendieckTopology S).over V).WEqualsLocallyBijective AddCommGrpCat.{u} :=
  fun V ↦
    let J := (Opens.grothendieckTopology S).over V
    letI : ∀ P : (Over V)ᵒᵖ ⥤ AddCommGrpCat.{u},
        Presheaf.IsLocallyInjective J (toSheafify J P) :=
      fun P ↦ Presheaf.isLocallyInjective_toSheafify' J P
    letI : ∀ P : (Over V)ᵒᵖ ⥤ AddCommGrpCat.{u},
        Presheaf.IsLocallySurjective J (toSheafify J P) :=
      fun P ↦ Presheaf.isLocallySurjective_toSheafify' J P
    GrothendieckTopology.WEqualsLocallyBijective.mk' J AddCommGrpCat.{u}

/-- The geometric properties needed to form the ordinary compact support of the bundle.
Source: blueprint order 1972, first paragraph (blueprint: def-amb-vector-integration).
Proof: the relative spectrum is affine, hence quasi-compact and separated by
lem-weil-pbc-affine-morphism-permanence. On an affine trivializing open its coordinate
ring is the polynomial algebra on d generators. The pointwise finite-type criterion
lem-weil-pbc-lft-pointwise-criterion gives local finite type. Finite type over the
Noetherian base gives a Noetherian total space by lem-weil-pbc-finite-type-over-noetherian.
-/
theorem vectorIntegration_geometry (S : Scheme.{u}) [IsNoetherian S] (d : ℕ)
    (F : SheafOfModules.{u} S.ringCatSheaf) [F.IsFiniteLocallyFreeOfRank d] :
    IsAffineHom (VectorBundleZeroSection.π S d F) ∧
      LocallyOfFiniteType (VectorBundleZeroSection.π S d F) ∧
      IsNoetherian (VectorBundleZeroSection.scheme S d F) := by
  let : IsAffineHom (VectorBundleZeroSection.π S d F) :=
    (VectorBundleZeroSection.over S d F).property
  have hft : LocallyOfFiniteType (VectorBundleZeroSection.π S d F) := by
    obtain ⟨I, U, hU, e⟩ :=
      Scheme.Modules.IsFiniteLocallyFreeOfRank.exists_restrict_iso_free F (r := d)
    apply IsZariskiLocalAtTarget.of_iSup_eq_top (P := @LocallyOfFiniteType) U hU
    intro i
    let E := (e i).some
    let := (VectorBundleZeroSection.trivializationMap_spec S d F (U i) E).1
    rw [← (VectorBundleZeroSection.trivializationMap_spec S d F (U i) E).2.1]
    infer_instance
  let := hft
  let := LocallyOfFiniteType.isLocallyNoetherian (VectorBundleZeroSection.π S d F)
  let := QuasiCompact.compactSpace_of_compactSpace (VectorBundleZeroSection.π S d F)
  exact ⟨inferInstance, hft, ⟨⟩⟩

/-- Canonical inverse image of the ordered shifted Tate tensor: recurse using tensor
pullback, the normalized finite-line comparison, and the constant-unit comparison.
Source: blueprint order 1972, Tate identifications (blueprint: def-amb-vector-integration).
-/
def vectorIntegrationBaseCoefficientPullback (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) (t : OrdinaryFiniteTwistTransport A N hA)
    {X Y : Scheme.{u}} (f : X ⟶ Y) (hY : IsUnit (N : Γ(Y, ⊤))) (d : ℕ) :
    (ordinaryFinitePullback A f).obj (affineLinearBaseCoefficient A N hA Y d) ≅
      affineLinearBaseCoefficient A N hA X d :=
  Nat.rec (motive := fun e ↦
    (ordinaryFinitePullback A f).obj (affineLinearBaseCoefficient A N hA Y e) ≅
      affineLinearBaseCoefficient A N hA X e)
    (ordinaryFiniteUnitPullback A f)
    (fun e r ↦ ordinaryFiniteTensorPullback A f (affineLinearBaseCoefficient A N hA Y e)
        ((ordinaryFiniteLine A N hA Y)⟦(2 : ℤ)⟧) ≪≫
      ordinaryFiniteTensorRightMapIso A X r
        (ordinaryFiniteShiftedLinePullback A N hA t f hY)) d

/-- A_E(d)[2d], written as inverse image of the existing ordered shifted Tate tensor.
Each of the d factors is the concrete finite roots-of-unity Tate line shifted by two;
the zero-fold tensor is the constant complex. This uses no additional twist definition.
Source: blueprint order 1972, C_pi (blueprint: def-amb-vector-integration). -/
def vectorIntegrationCoefficient (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) (S : Scheme.{u}) [IsNoetherian S] (d : ℕ)
    (F : SheafOfModules.{u} S.ringCatSheaf) [F.IsFiniteLocallyFreeOfRank d] :
    DerivedCategoryModule A (VectorBundleZeroSection.scheme S d F) :=
  (ordinaryFinitePullback A (VectorBundleZeroSection.π S d F)).obj
    (affineLinearBaseCoefficient A N hA S d)

/-- C_pi = R pi_! A_E(d)[2d], using the canonical chosen compactification. Nagata applies
because the bundle is separated and finite type and the Noetherian base is qcqs.
Source: blueprint order 1972, C_pi (blueprint: def-amb-vector-integration). -/
def vectorIntegrationSource (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) (S : Scheme.{u}) [IsNoetherian S] (d : ℕ)
    (F : SheafOfModules.{u} S.ringCatSheaf) [F.IsFiniteLocallyFreeOfRank d] :
    DerivedCategoryModule A S :=
  letI : IsAffineHom (VectorBundleZeroSection.π S d F) :=
    (vectorIntegration_geometry S d F).1
  letI : LocallyOfFiniteType (VectorBundleZeroSection.π S d F) :=
    (vectorIntegration_geometry S d F).2.1
  (rightDerivedLowerShriek (ModuleCat.{u + 1} A) (VectorBundleZeroSection.π S d F)).obj
    (vectorIntegrationCoefficient A N hA S d F)

/-- L_pi is the degree-zero cohomology sheaf of C_pi.
Source: blueprint order 1972, L_pi (blueprint: def-amb-vector-integration). -/
def vectorIntegrationSheaf (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) (S : Scheme.{u}) [IsNoetherian S] (d : ℕ)
    (F : SheafOfModules.{u} S.ringCatSheaf) [F.IsFiniteLocallyFreeOfRank d] :
    Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} A) :=
  (_root_.DerivedCategory.homologyFunctor _ 0).obj (vectorIntegrationSource A N hA S d F)

/-- The inverse frame from the coordinate-tower affine space to the restricted bundle,
followed by the actual open inclusion into E. No coordinate isomorphism is chosen.
Source: blueprint order 1972, inverse-coordinate square
(blueprint: def-amb-vector-integration). -/
def vectorIntegrationChart (S : Scheme.{u}) [IsNoetherian S] (d : ℕ)
    (F : SheafOfModules.{u} S.ringCatSheaf) [F.IsFiniteLocallyFreeOfRank d] (V : S.Opens)
    (e : VectorBundleZeroSection.Trivialization S d F V) :
    affineTraceTower V.toScheme d ⟶ VectorBundleZeroSection.scheme S d F :=
  letI := (VectorBundleZeroSection.trivializationMap_spec S d F V e).1
  (affineTraceAffineSpaceIso V.toScheme d).hom ≫
    inv (VectorBundleZeroSection.trivializationMap S d F V e) ≫
      ((VectorBundleZeroSection.π S d F) ⁻¹ᵁ V).ι

/-- The inverse-frame square over V → S is Cartesian.
Source: blueprint order 1972, inverse-coordinate square
(blueprint: def-amb-vector-integration).
Proof: the open inverse-image square is Cartesian. The frame's concrete coordinate map
is an isomorphism over V by def-asd-vector-bundle-zero-section; the coordinate tower is
the same affine space. Paste this isomorphism square with the open inverse-image square.
-/
theorem vectorIntegrationChart_isPullback (S : Scheme.{u}) [IsNoetherian S] (d : ℕ)
    (F : SheafOfModules.{u} S.ringCatSheaf) [F.IsFiniteLocallyFreeOfRank d] (V : S.Opens)
    (e : VectorBundleZeroSection.Trivialization S d F V) :
    IsPullback (vectorIntegrationChart S d F V e) (affineTraceProjection V.toScheme d)
      (VectorBundleZeroSection.π S d F) V.ι := by
  let := (VectorBundleZeroSection.trivializationMap_spec S d F V e).1
  have hw :
      ((affineTraceAffineSpaceIso V.toScheme d).hom ≫
        inv (VectorBundleZeroSection.trivializationMap S d F V e)) ≫
          ((VectorBundleZeroSection.π S d F) ∣_ V) =
        affineTraceProjection V.toScheme d := by
    rw [← (VectorBundleZeroSection.trivializationMap_spec S d F V e).2.1]
    simp [affineTraceAffineSpaceIso, affineTraceToAffineSpace]
  have hi := IsPullback.of_horiz_isIso
    (fst := (affineTraceAffineSpaceIso V.toScheme d).hom ≫
      inv (VectorBundleZeroSection.trivializationMap S d F V e))
    (g := 𝟙 V.toScheme) (CommSq.mk (by simpa using hw))
  simpa only [vectorIntegrationChart, Category.id_comp, Category.assoc] using
    hi.paste_horiz (isPullback_morphismRestrict (VectorBundleZeroSection.π S d F) V).flip

/-- Canonical coefficient identification in the inverse-frame square. The equality of
its two composites is used between the inverse-image composition comparisons; then the
base Tate tensor is pulled back and the existing affine coefficient descent is inverted.
Source: blueprint order 1972, a_i (blueprint: def-amb-vector-integration). -/
def vectorIntegrationChartCoefficient (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) (t : OrdinaryFiniteTwistTransport A N hA)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ)
    (F : SheafOfModules.{u} S.ringCatSheaf) [F.IsFiniteLocallyFreeOfRank d] (V : S.Opens)
    (e : VectorBundleZeroSection.Trivialization S d F V) :
    (ordinaryFinitePullback A (vectorIntegrationChart S d F V e)).obj
        (vectorIntegrationCoefficient A N hA S d F) ≅
      (affineTraceRight A N hA V.toScheme d).obj (ordinaryFiniteUnit A V.toScheme) :=
  (leftDerivedUpperStarComp (ModuleCat.{u + 1} A)
    (vectorIntegrationChart S d F V e) (VectorBundleZeroSection.π S d F)).symm.app _ ≪≫
  (eqToIso (congrArg (ordinaryFinitePullback A)
    (vectorIntegrationChart_isPullback S d F V e).w)).app _ ≪≫
  (leftDerivedUpperStarComp (ModuleCat.{u + 1} A)
    (affineTraceProjection V.toScheme d) V.ι).app _ ≪≫
  (ordinaryFinitePullback A (affineTraceProjection V.toScheme d)).mapIso
    (vectorIntegrationBaseCoefficientPullback A N hA t V.ι hS d) ≪≫
  (affineLinearCoefficientDescent A N hA t V.toScheme
    (affineTracePullbackInvertible N V.ι hS) d).symm

/-- The prescribed local map a_i: exchange for the actual inverse-coordinate square,
canonical Tate identification, comparison with the ordered tower, and its actual counit.
Source: blueprint order 1972, a_i (blueprint: def-amb-vector-integration). -/
def vectorIntegrationLocalTrace (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (t : OrdinaryFiniteTwistTransport A N hA)
    (D : ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (N : Γ(T, ⊤))),
      OrdinaryFiniteP1Datum A N hA t T hT)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ)
    (F : SheafOfModules.{u} S.ringCatSheaf) [F.IsFiniteLocallyFreeOfRank d] (V : S.Opens)
    (e : VectorBundleZeroSection.Trivialization S d F V) :
    (ordinaryFinitePullback A V.ι).obj (vectorIntegrationSource A N hA S d F) ⟶
      ordinaryFiniteUnit A V.toScheme :=
  letI : IsAffineHom (VectorBundleZeroSection.π S d F) :=
    (vectorIntegration_geometry S d F).1
  letI : LocallyOfFiniteType (VectorBundleZeroSection.π S d F) :=
    (vectorIntegration_geometry S d F).2.1
  letI : TopologicalSpace.NoetherianSpace V.toScheme :=
    V.ι.isOpenEmbedding.isInducing.noetherianSpace
  letI : IsNoetherian V.toScheme :=
    { toIsLocallyNoetherian := inferInstance
      isCompact_univ := TopologicalSpace.NoetherianSpace.isCompact _ }
  (rightDerivedLowerShriekBaseChangeMap A
      (vectorIntegrationChart_isPullback S d F V e)).app
        (vectorIntegrationCoefficient A N hA S d F) ≫
    (rightDerivedLowerShriek (ModuleCat.{u + 1} A) (affineTraceProjection V.toScheme d)).map
      (vectorIntegrationChartCoefficient A N hA t S hS d F V e).hom ≫
    (affineLinearCompactComparison N hN A hA V.toScheme
      (affineTracePullbackInvertible N V.ι hS) d).inv ≫
    affineTraceCounit A N hA t D V.toScheme (affineTracePullbackInvertible N V.ι hS) d

/-- The defining local normalization on every Zariski linear trivialization. Quantifying
normalized projective-line data avoids making any such datum an extra hypothesis or a
choice in the global map: the Kummer and counit normalizations fix the actual trace.
Source: blueprint order 1972, uniqueness paragraph (blueprint: def-amb-vector-integration).
-/
def VectorIntegrationNormalization (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ)
    (F : SheafOfModules.{u} S.ringCatSheaf) [F.IsFiniteLocallyFreeOfRank d]
    (f : vectorIntegrationSource A N hA S d F ⟶ ordinaryFiniteUnit A S) : Prop :=
  ∀ (t : OrdinaryFiniteTwistTransport A N hA)
    (D : ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (N : Γ(T, ⊤))),
      OrdinaryFiniteP1Datum A N hA t T hT)
    (V : S.Opens) (e : VectorBundleZeroSection.Trivialization S d F V),
    (ordinaryFinitePullback A V.ι).map f ≫ (ordinaryFiniteUnitPullback A V.ι).hom =
      vectorIntegrationLocalTrace N hN A hA t D S hS d F V e

```

## New

The same declarations, signatures, visibility, attributes, docstrings, and bodies are
in `Sheaf.AlgebraicGeometry.VectorBundleIntegrationCharts`. The original module adds

```lean
public import Sheaf.AlgebraicGeometry.VectorBundleIntegrationCharts
```

and re-exports the existing public mathematical dependencies through that module.
Three unused proof dependencies are removed: HomCoverGluing,
IsIsoIffOfJointlySurjectiveEtaleFamily, and TruncationDescends. The first is an empty
retired module; the second has the abelian-sheaf interface rather than ModuleCat
sheaves; the third is replaced by the proved general normalized degree-zero lemma.
The original module keeps exactly the same
`existsUnique_vectorIntegrationGluing`, `vectorIntegrationGluing`, and
`vectorBundleIntegration` signatures. Their defining data bodies do not change.
The proof of `existsUnique_vectorIntegrationGluing` now uses cohomology concentration,
the normalized degree-zero identification, local trace compatibility, and a proved
cover-family sheaf-Hom gluing theorem.

The chart module also proves `vectorIntegration_cohomology_zero`. The original node retains its statement dependencies; the new chart node
records the construction dependencies and is reached through the actual proof route. This does not withdraw any parent or unit route. No original
non-theorem body changes. Every target using these constructions therefore has
identical definitions; no semantic target review is reopened by the relocation.
Independent review should verify this byte-for-byte for the moved block.

## Users

`tools/downstream.py Sheaf.AlgebraicGeometry.VectorBundleIntegration --uses`
was run for every relocated name. The current transitive importers are listed below.
Every public construction and signature is unchanged and re-exported through the
original module, so their statements keep precisely the same meaning. The direct
users were also checked by declaration-name search. The consumer compilation checks
are recorded in report.md. Only VectorPurityDirectSum needs local elaboration
annotations; those are recorded separately in F1-vector-direct-sum-folding.md.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.VectorBundleIntegration | F1 | Re-exports identical constructions and proves gluing from the separate results. |
| Sheaf.AlgebraicGeometry.VectorIntegrationMate | unclaimed | Identical public constructions, signatures and data; no adaptation. |
| Sheaf.DeligneLaumon.QbarCurveDuality | unclaimed | Identical public constructions, signatures and data; no adaptation. |
| Sheaf.EtaleCohomology.Purity.RealSheaves.TateTwistWeightShift | unclaimed | Identical public constructions, signatures and data; no adaptation. |
| Sheaf.Paper.AdicPurityExceptionalReduction | unclaimed | Identical public constructions, signatures and data; no adaptation. |
| Sheaf.Paper.AdicPurityFiniteTensor | unclaimed | Identical public constructions, signatures and data; no adaptation. |
| Sheaf.Paper.AdicPurityObjects | unclaimed | Identical public constructions, signatures and data; no adaptation. |
| Sheaf.Paper.AdicPurityRootComparisons | unclaimed | Identical public constructions, signatures and data; no adaptation. |
| Sheaf.Paper.AdicPuritySourceReduction | unclaimed | Identical public constructions, signatures and data; no adaptation. |
| Sheaf.Paper.AdicPurityTwistReduction | unclaimed | Identical public constructions, signatures and data; no adaptation. |
| Sheaf.Paper.AdicSmoothDualizingComplexes | unclaimed | Identical public constructions, signatures and data; no adaptation. |
| Sheaf.Paper.AdmissibleVerdierExchange | unclaimed | Identical public constructions, signatures and data; no adaptation. |
| Sheaf.Paper.AmbientDiagonalPurityBaseChange | unclaimed | Identical public constructions, signatures and data; no adaptation. |
| Sheaf.Paper.CohomologicalSmoothEtaleLocality | unclaimed | Identical public constructions, signatures and data; no adaptation. |
| Sheaf.Paper.CompletedStalkFrobeniusReduction | unclaimed | Identical public constructions, signatures and data; no adaptation. |
| Sheaf.Paper.DualizingObjectPurity | unclaimed | Identical public constructions, signatures and data; no adaptation. |
| Sheaf.Paper.FiniteAdjointMateCompatibility | unclaimed | Identical public constructions, signatures and data; no adaptation. |
| Sheaf.Paper.FiniteCoefficientAdjointComparisons | unclaimed | Identical public constructions, signatures and data; no adaptation. |
| Sheaf.Paper.FiniteCoefficientSmoothPurity | unclaimed | Identical public constructions, signatures and data; no adaptation. |
| Sheaf.Paper.FiniteDncNormalizationReduction | unclaimed | Identical public constructions, signatures and data; no adaptation. |
| Sheaf.Paper.FiniteFreeCoefficientExtension | claim present | Identical public constructions, signatures and data; no adaptation. |
| Sheaf.Paper.FiniteFreeCompactComposition | unclaimed | Identical public constructions, signatures and data; no adaptation. |
| Sheaf.Paper.FiniteFreeCompactScalar | unclaimed | Identical public constructions, signatures and data; no adaptation. |
| Sheaf.Paper.FiniteFreeCompactSupportComposition | unclaimed | Identical public constructions, signatures and data; no adaptation. |
| Sheaf.Paper.FiniteFreeProjectionExchange | unclaimed | Identical public constructions, signatures and data; no adaptation. |
| Sheaf.Paper.FiniteFreeProjectionExchangeDefinitions | unclaimed | Identical public constructions, signatures and data; no adaptation. |
| Sheaf.Paper.FiniteFreeScalarProjection | unclaimed | Identical public constructions, signatures and data; no adaptation. |
| Sheaf.Paper.FiniteReductionAffineOrientation | unclaimed | Identical public constructions, signatures and data; no adaptation. |
| Sheaf.Paper.FiniteReductionChartCalculus | unclaimed | Identical public constructions, signatures and data; no adaptation. |
| Sheaf.Paper.FiniteReductionComparisons | unclaimed | Identical public constructions, signatures and data; no adaptation. |
| Sheaf.Paper.FiniteReductionOfPurity | unclaimed | Identical public constructions, signatures and data; no adaptation. |
| Sheaf.Paper.FiniteReductionRootCharts | unclaimed | Identical public constructions, signatures and data; no adaptation. |
| Sheaf.Paper.FiniteRingSectionDeformation | unclaimed | Identical public constructions, signatures and data; no adaptation. |
| Sheaf.Paper.FiniteSmoothAdjunctionData | unclaimed | Identical public constructions, signatures and data; no adaptation. |
| Sheaf.Paper.FiniteSmoothAdjunctionGeneralBase | unclaimed | Identical public constructions, signatures and data; no adaptation. |
| Sheaf.Paper.FiniteSmoothCoefficientArrows | unclaimed | Identical public constructions, signatures and data; no adaptation. |
| Sheaf.Paper.FiniteSmoothGammaNormalization | unclaimed | Identical public constructions, signatures and data; no adaptation. |
| Sheaf.Paper.FiniteSmoothIntrinsicLevelProperties | unclaimed | Identical public constructions, signatures and data; no adaptation. |
| Sheaf.Paper.FiniteSmoothLevelOfOrientation | unclaimed | Identical public constructions, signatures and data; no adaptation. |
| Sheaf.Paper.FiniteSmoothPullbackExchange | unclaimed | Identical public constructions, signatures and data; no adaptation. |
| Sheaf.Paper.FiniteSmoothPurityMaps | unclaimed | Identical public constructions, signatures and data; no adaptation. |
| Sheaf.Paper.FiniteSmoothQuotientCoherence | unclaimed | Identical public constructions, signatures and data; no adaptation. |
| Sheaf.Paper.FiniteSmoothSiteRealizations | unclaimed | Identical public constructions, signatures and data; no adaptation. |
| Sheaf.Paper.FiniteSmoothTwoLevelReduction | unclaimed | Identical public constructions, signatures and data; no adaptation. |
| Sheaf.Paper.FiniteTorStability | unclaimed | Identical public constructions, signatures and data; no adaptation. |
| Sheaf.Paper.FiniteUniversalSmoothTrace | unclaimed | Identical public constructions, signatures and data; no adaptation. |
| Sheaf.Paper.FixedStalkIdentificationReduction | unclaimed | Identical public constructions, signatures and data; no adaptation. |
| Sheaf.Paper.GlobalVerdierDuality | unclaimed | Identical public constructions, signatures and data; no adaptation. |
| Sheaf.Paper.PurAdicReconstruction | unclaimed | Identical public constructions, signatures and data; no adaptation. |
| Sheaf.Paper.PurityCompositionCoherence | unclaimed | Identical public constructions, signatures and data; no adaptation. |
| Sheaf.Paper.PurityDiagonalDualizingObject | unclaimed | Identical public constructions, signatures and data; no adaptation. |
| Sheaf.Paper.RationalHomScalarTranspose | unclaimed | Identical public constructions, signatures and data; no adaptation. |
| Sheaf.Paper.RationalScalarTransposeCompatibility | unclaimed | Identical public constructions, signatures and data; no adaptation. |
| Sheaf.Paper.RationalSmoothPurityCanonical | unclaimed | Identical public constructions, signatures and data; no adaptation. |
| Sheaf.Paper.RationalTensorSymmetry | unclaimed | Identical public constructions, signatures and data; no adaptation. |
| Sheaf.Paper.RationalVerdierEvaluationAdjoints | unclaimed | Identical public constructions, signatures and data; no adaptation. |
| Sheaf.Paper.ScalarExchangeConstituents | unclaimed | Identical public constructions, signatures and data; no adaptation. |
| Sheaf.Paper.SfBidualityClass | unclaimed | Identical public constructions, signatures and data; no adaptation. |
| Sheaf.Paper.SitePerfectRationalBidual | unclaimed | Identical public constructions, signatures and data; no adaptation. |
| Sheaf.Paper.SmoothPurityMap | unclaimed | Identical public constructions, signatures and data; no adaptation. |
| Sheaf.Paper.SmoothTrace | unclaimed | Identical public constructions, signatures and data; no adaptation. |
| Sheaf.Paper.TensorAdjunctionExchange | unclaimed | Identical public constructions, signatures and data; no adaptation. |
| Sheaf.Paper.TraceFormulaTopologicalInvariance | unclaimed | Identical public constructions, signatures and data; no adaptation. |
| Sheaf.Paper.TwistFrobeniusScalar | unclaimed | Identical public constructions, signatures and data; no adaptation. |
| Sheaf.Paper.VectorBundlePurity | unclaimed | Identical public constructions, signatures and data; no adaptation. |
| Sheaf.Paper.VectorPurityBaseChange | unclaimed | Identical public constructions, signatures and data; no adaptation. |
| Sheaf.Paper.VectorPurityDirectSum | unclaimed | Identical declarations and data; local compilation annotations in F1-vector-direct-sum-folding.md. |
| Sheaf.Paper.VectorPurityFiniteReduction | unclaimed | Identical public constructions, signatures and data; no adaptation. |
| Sheaf.Paper.VectorPurityNormalization | unclaimed | Identical public constructions, signatures and data; no adaptation. |
| Sheaf.Paper.VectorPurityScalarSingle | unclaimed | Identical public constructions, signatures and data; no adaptation. |
| Sheaf.Paper.VerdierExchange | unclaimed | Identical public constructions, signatures and data; no adaptation. |
| Sheaf.SecSmoothPurity.FiniteGeneralRing | unclaimed | Identical public constructions, signatures and data; no adaptation. |
| Sheaf.SecSmoothPurity.ReductionCompatibilities | unclaimed | Identical public constructions, signatures and data; no adaptation. |
| Sheaf.SecSmoothPurity.SmoothPurityNaturality | unclaimed | Identical public constructions, signatures and data; no adaptation. |
| Sheaf.SixFunctors.CoefDualFormulaScalarTranspose | unclaimed | Identical public constructions, signatures and data; no adaptation. |
| Sheaf.SixFunctors.CoefIntegralFiniteExtension | unclaimed | Identical public constructions, signatures and data; no adaptation. |
| Sheaf.SixFunctors.CoefQbarVerdier | unclaimed | Identical public constructions, signatures and data; no adaptation. |
| Sheaf.SixFunctors.CoefVerdierWeilEquivariance | unclaimed | Identical public constructions, signatures and data; no adaptation. |
| Sheaf.SixFunctors.FiniteAdjunctionDiagramRealization | unclaimed | Identical public constructions, signatures and data; no adaptation. |
| Sheaf.SixFunctors.FiniteAdjunctionSystemData | unclaimed | Identical public constructions, signatures and data; no adaptation. |
| Sheaf.SixFunctors.FiniteExceptional | unclaimed | Identical public constructions, signatures and data; no adaptation. |
| Sheaf.SixFunctors.RationalOperations | unclaimed | Identical public constructions, signatures and data; no adaptation. |
| Sheaf.SixFunctors.RationalRetractEvaluation | unclaimed | Identical public constructions, signatures and data; no adaptation. |
| Sheaf.SixFunctors.RationalVerdier | unclaimed | Identical public constructions, signatures and data; no adaptation. |
| Sheaf.SmoothPurity.NormalizedWitness | unclaimed | Identical public constructions, signatures and data; no adaptation. |
| Sheaf.Targets.PoincareUncurry | unclaimed | Identical public constructions, signatures and data; no adaptation. |
| Sheaf.Targets.SmoothPurityQbar | unclaimed | Identical public constructions, signatures and data; no adaptation. |
| Sheaf.Targets.VectorBundlePurity | unclaimed | Identical public constructions, signatures and data; no adaptation. |

The new overlap module imports the chart module directly. Existing source-library
modules are neither changed nor removed.

## Status

landed 20261020T221141-L-4149524 2026-10-20 (merge of deliver/F1/Sheaf.AlgebraicGeometry.VectorBundleIntegration)
