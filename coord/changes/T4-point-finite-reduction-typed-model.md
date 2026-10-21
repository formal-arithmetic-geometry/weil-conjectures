# pointFiniteReductionSheafModel and the finite-reduction data interface

## Reason

The old inferred type of pointFiniteReductionSheafExistence exposes a deeply nested
existential witness with local universe instances. Expanding its choice projections
while elaborating the counit repeatedly reaches the heartbeat or 60-second file limit.
A proved Nonempty theorem now constructs a typed record of the same prescribed ordinary
functor and universal derived pair. Access uses typed projections and a named epsilon.
The theorem is proved, not a new hole. The ordinary object and map equations fix the
ordinary extension; the derived functor with its counit is determined up to the unique
counit-compatible isomorphism. No arbitrary witness of mere existence is used.

Definitions move to PointSectionsFiniteReductionData so the ordinary algebra theorem
can depend on them and the main theorem can import that algebra theorem without a cycle.
This is an interface dependency extraction; no unfinished proof is split to evade a limit.
The old public imports are publicly reexported through Data. Thin aliases become abbrevs,
and the coefficient sheaf map has an explicit source and target. The section factor is
now the component of a typed natural isomorphism with the same underlying body.

The record may choose a different representative of the universal pair than the old raw
projections. Consequently the bounded sheaf proof is rebuilt using its K-flat counit,
rather than pretending definitional equality with a separately chosen ringed functor.
The target statements remain verbatim. Because their definitions use the selected
universal pair, this record explicitly requests their semantic statement re-review.

## Old

```lean
noncomputable def pointFiniteReductionRingSheaf (k : Type u) [Field k]
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (n : ℕ) :
    Sheaf (Scheme.ProEt.topology (Spec (.of k))) CommRingCat.{u + 1} :=
  (constantSheaf.{u, u + 1, u + 1, u + 2} (Scheme.ProEt.topology (Spec (.of k)))
    CommRingCat.{u + 1}).obj
    (CommRingCat.of (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n)))

noncomputable def pointFiniteReductionSheafMap (n j : ℕ) (h : j ≤ n) :=
  (constantSheaf.{u, u + 1, u + 1, u + 2} (Scheme.ProEt.topology (Spec (.of k)))
    CommRingCat.{u + 1}).map
    (CommRingCat.ofHom (pointFiniteReductionRingMap l E n j h))

noncomputable def pointFiniteReductionSheafExtension (n j : ℕ) (h : j ≤ n) :
    pointFiniteReductionSheaves k l E n ⥤ pointFiniteReductionSheaves k l E j :=
  (pointFiniteReductionSheafExistence k l E n j h).choose

noncomputable instance pointFiniteReductionSheafExtensionAdditive (n j : ℕ) (h : j ≤ n) :
    (pointFiniteReductionSheafExtension k l E n j h).Additive :=
  (pointFiniteReductionSheafExistence k l E n j h).choose_spec.choose_spec.choose_spec.choose

noncomputable def pointFiniteReductionSheafTensor (n j : ℕ) (h : j ≤ n) :
    DerivedCategory (pointFiniteReductionSheaves k l E n) ⥤
      DerivedCategory (pointFiniteReductionSheaves k l E j) :=
  (((pointFiniteReductionSheafExistence k l E n j h).choose_spec
    ).choose_spec.choose_spec.choose_spec).2.2.choose

noncomputable def pointFiniteReductionSheafCounit (n j : ℕ) (h : j ≤ n)
    (P : CochainComplex (pointFiniteReductionSheaves k l E n) ℤ) :
    (pointFiniteReductionSheafTensor k l E n j h).obj (DerivedCategory.Q.obj P) ⟶
      DerivedCategory.Q.obj
        (((pointFiniteReductionSheafExtension k l E n j h).mapHomologicalComplex
          (.up ℤ)).obj P) :=
  (pointFiniteReductionSheafTensor k l E n j h).map
      ((DerivedCategory.quotientCompQhIso (pointFiniteReductionSheaves k l E n)).inv.app P) ≫
    ((((pointFiniteReductionSheafExistence k l E n j h).choose_spec
      ).choose_spec.choose_spec.choose_spec).2.2.choose_spec.choose).app
        ((HomotopyCategory.quotient _ (.up ℤ)).obj P) ≫
    DerivedCategory.Qh.map
      (((pointFiniteReductionSheafExtension k l E n j h).mapHomotopyCategoryFactors
        (.up ℤ)).hom.app P) ≫
    (DerivedCategory.quotientCompQhIso (pointFiniteReductionSheaves k l E j)).hom.app
      (((pointFiniteReductionSheafExtension k l E n j h).mapHomologicalComplex (.up ℤ)).obj P)

noncomputable def pointFiniteReductionSheafComplexTensor (n j : ℕ) (h : j ≤ n) :
    CochainComplex (pointFiniteReductionSheaves k l E n) ℤ ⥤
      CochainComplex (pointFiniteReductionSheaves k l E j) ℤ :=
  (pointFiniteReductionSheafExtension k l E n j h).mapHomologicalComplex (.up ℤ)

noncomputable def pointFiniteReductionSectionComplex (n : ℕ) :
    CochainComplex (pointFiniteReductionSheaves k l E n) ℤ ⥤
      CochainComplex (pointFiniteReductionModules l E n) ℤ :=
  (pointFiniteSections k (Padic.coefficientExtensionRing l E n)).mapHomologicalComplex (.up ℤ)

noncomputable def pointFiniteReductionSectionGenerator (n j : ℕ) (h : j ≤ n)
    (M : pointFiniteReductionSheaves k l E n)
    (x : (pointFiniteSections k (Padic.coefficientExtensionRing l E n)).obj M) :
    (pointFiniteSections k (Padic.coefficientExtensionRing l E j)).obj
      ((pointFiniteReductionSheafExtension k l E n j h).obj M) := by
  letI : EssentiallySmall.{u + 1} (Scheme.ProEt (Spec (.of k))) :=
    essentiallySmallSelf.{0, u, u + 1} _
  letI : HasSheafify (Scheme.ProEt.topology (Spec (.of k))) AddCommGrpCat.{u + 1} :=
    hasSheafifyEssentiallySmallSite.{u, u + 1, u + 1, u + 2, u + 1} _ _
  letI : (Scheme.ProEt.topology (Spec (.of k))).WEqualsLocallyBijective
      AddCommGrpCat.{u + 1} :=
    GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{u, u + 1, u + 1,
      u + 2, u + 1, u + 1, u + 1} _
  let y := (((PresheafOfModules.sheafificationAdjunction.{u + 1}
      (J := Scheme.ProEt.topology (Spec (.of k)))
      (R := SheafOfModules.derivedChangeRingIndependentCoefficients.{u + 1, u + 1, u}
        (Scheme.ProEt.topology (Spec (.of k))) (pointFiniteReductionRingSheaf k l E j))
      (𝟙 _)).unit.app
        (SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1}
          (pointFiniteReductionSheafMap k l E n j h) M)).app
            (op (Scheme.ProEt.mk (𝟙 (Spec (.of k))))))
      (((ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u + 1}
        ((pointFiniteReductionSheafMap k l E n j h).hom.app
          (op (Scheme.ProEt.mk (𝟙 (Spec (.of k)))))).hom).unit.app
            (M.val.obj (op (Scheme.ProEt.mk (𝟙 (Spec (.of k))))))) x)
  exact (eqToHom
    ((pointFiniteReductionSheafExistence k l E n j h).choose_spec.choose M).symm).val.app
      (op (Scheme.ProEt.mk (𝟙 (Spec (.of k))))) y

noncomputable def pointFiniteReductionSectionFactors [IsAlgClosed k] (n : ℕ)
    (P : CochainComplex (pointFiniteReductionSheaves k l E n) ℤ) :
    (pointFiniteReductionSections k l E n).obj (DerivedCategory.Q.obj P) ≅
      DerivedCategory.Q.obj ((pointFiniteReductionSectionComplex k l E n).obj P) :=
  (pointFiniteSections k (Padic.coefficientExtensionRing l E n)).mapDerivedCategoryFactors.app P
```

## New

```lean
noncomputable abbrev pointFiniteReductionRingSheaf (k : Type u) [Field k]
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (n : ℕ) :
    Sheaf (Scheme.ProEt.topology (Spec (.of k))) CommRingCat.{u + 1} :=
  (constantSheaf.{u, u + 1, u + 1, u + 2} (Scheme.ProEt.topology (Spec (.of k)))
    CommRingCat.{u + 1}).obj
    (CommRingCat.of (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n)))

noncomputable def pointFiniteReductionSheafMap (n j : ℕ) (h : j ≤ n) :
    pointFiniteReductionRingSheaf k l E n ⟶ pointFiniteReductionRingSheaf k l E j :=
  (constantSheaf.{u, u + 1, u + 1, u + 2} (Scheme.ProEt.topology (Spec (.of k)))
    CommRingCat.{u + 1}).map
    (CommRingCat.ofHom (pointFiniteReductionRingMap l E n j h))

noncomputable def pointFiniteReductionSheafExtension (n j : ℕ) (h : j ≤ n) :
    pointFiniteReductionSheaves k l E n ⥤ pointFiniteReductionSheaves k l E j :=
  (pointFiniteReductionSheafModel k l E n j h).F

noncomputable instance pointFiniteReductionSheafExtensionAdditive (n j : ℕ) (h : j ≤ n) :
    (pointFiniteReductionSheafExtension k l E n j h).Additive :=
  (pointFiniteReductionSheafModel k l E n j h).additive

noncomputable def pointFiniteReductionSheafTensor (n j : ℕ) (h : j ≤ n) :
    DerivedCategory (pointFiniteReductionSheaves k l E n) ⥤
      DerivedCategory (pointFiniteReductionSheaves k l E j) :=
  (pointFiniteReductionSheafModel k l E n j h).T

noncomputable def pointFiniteReductionSheafCounit (n j : ℕ) (h : j ≤ n)
    (P : CochainComplex (pointFiniteReductionSheaves k l E n) ℤ) :
    (pointFiniteReductionSheafTensor k l E n j h).obj (DerivedCategory.Q.obj P) ⟶
      DerivedCategory.Q.obj
        (((pointFiniteReductionSheafExtension k l E n j h).mapHomologicalComplex
          (.up ℤ)).obj P) :=
  (pointFiniteReductionSheafTensor k l E n j h).map
      ((DerivedCategory.quotientCompQhIso (pointFiniteReductionSheaves k l E n)).inv.app P) ≫
    (pointFiniteReductionSheafEpsilon k l E n j h).app
        ((HomotopyCategory.quotient _ (.up ℤ)).obj P) ≫
    DerivedCategory.Qh.map
      (((pointFiniteReductionSheafExtension k l E n j h).mapHomotopyCategoryFactors
        (.up ℤ)).hom.app P) ≫
    (DerivedCategory.quotientCompQhIso (pointFiniteReductionSheaves k l E j)).hom.app
      (((pointFiniteReductionSheafExtension k l E n j h).mapHomologicalComplex (.up ℤ)).obj P)

noncomputable abbrev pointFiniteReductionSheafComplexTensor (n j : ℕ) (h : j ≤ n) :
    CochainComplex (pointFiniteReductionSheaves k l E n) ℤ ⥤
      CochainComplex (pointFiniteReductionSheaves k l E j) ℤ :=
  (pointFiniteReductionSheafExtension k l E n j h).mapHomologicalComplex (.up ℤ)

noncomputable abbrev pointFiniteReductionSectionComplex (n : ℕ) :
    CochainComplex (pointFiniteReductionSheaves k l E n) ℤ ⥤
      CochainComplex (pointFiniteReductionModules l E n) ℤ :=
  (pointFiniteSections k (Padic.coefficientExtensionRing l E n)).mapHomologicalComplex (.up ℤ)

noncomputable def pointFiniteReductionSectionGenerator (n j : ℕ) (h : j ≤ n)
    (M : pointFiniteReductionSheaves k l E n)
    (x : (pointFiniteSections k (Padic.coefficientExtensionRing l E n)).obj M) :
    (pointFiniteSections k (Padic.coefficientExtensionRing l E j)).obj
      ((pointFiniteReductionSheafExtension k l E n j h).obj M) := by
  letI : EssentiallySmall.{u + 1} (Scheme.ProEt (Spec (.of k))) :=
    essentiallySmallSelf.{0, u, u + 1} _
  letI : HasSheafify (Scheme.ProEt.topology (Spec (.of k))) AddCommGrpCat.{u + 1} :=
    hasSheafifyEssentiallySmallSite.{u, u + 1, u + 1, u + 2, u + 1} _ _
  letI : (Scheme.ProEt.topology (Spec (.of k))).WEqualsLocallyBijective
      AddCommGrpCat.{u + 1} :=
    GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{u, u + 1, u + 1,
      u + 2, u + 1, u + 1, u + 1} _
  let y := (((PresheafOfModules.sheafificationAdjunction.{u + 1}
      (J := Scheme.ProEt.topology (Spec (.of k)))
      (R := SheafOfModules.derivedChangeRingIndependentCoefficients.{u + 1, u + 1, u}
        (Scheme.ProEt.topology (Spec (.of k))) (pointFiniteReductionRingSheaf k l E j))
      (𝟙 _)).unit.app
        (SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1}
          (pointFiniteReductionSheafMap k l E n j h) M)).app
            (op (Scheme.ProEt.mk (𝟙 (Spec (.of k))))))
      (((ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u + 1}
        ((pointFiniteReductionSheafMap k l E n j h).hom.app
          (op (Scheme.ProEt.mk (𝟙 (Spec (.of k)))))).hom).unit.app
            (M.val.obj (op (Scheme.ProEt.mk (𝟙 (Spec (.of k))))))) x)
  exact (eqToHom
    ((pointFiniteReductionSheafModel k l E n j h).objEq M).symm).val.app
      (op (Scheme.ProEt.mk (𝟙 (Spec (.of k))))) y

noncomputable abbrev pointFiniteReductionSectionFactors [IsAlgClosed k] (n : ℕ)
    (P : CochainComplex (pointFiniteReductionSheaves k l E n) ℤ) :
    (pointFiniteReductionSections k l E n).obj (DerivedCategory.Q.obj P) ≅
      DerivedCategory.Q.obj ((pointFiniteReductionSectionComplex k l E n).obj P) :=
  (pointFiniteReductionSectionFactorsNat k l E n).app P
```

The new structure PointFiniteReductionSheafModel, its proved nonemptiness theorem,
pointFiniteReductionSheafModel, pointFiniteReductionSheafEpsilon and
pointFiniteReductionSectionFactorsNat are in
lean/Sheaf/Paper/PointSectionsFiniteReductionData.lean. Its local standard sheaf-derived
instance preserves the old sheaf localization universe; the ordinary-module localization
keeps its existing small Grothendieck instance.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.PointSectionsFiniteReduction | T4 | Proofs use the typed model; parent, iso and bounded signatures unchanged. |
| Sheaf.Paper.PointSectionsFiniteReductionData | T4 | Hosts the relocated declarations and typed universal pair. |
| Sheaf.Paper.PointFiniteReductionSectionAlgebra | T4 | Uses the prescribed object/map equations and public coefficient instances. |
| Sheaf.DeligneLaumon.QbarCurveDuality | unclaimed at audit | Only unchanged relocated exports and instances are relevant. Their signatures, attributes, bodies and public reexports are preserved; no adaptation. |
| Sheaf.DeligneLaumon.Reduction.FiniteMapPurity | unclaimed at audit | Only unchanged relocated exports and instances are relevant. Their signatures, attributes, bodies and public reexports are preserved; no adaptation. |
| Sheaf.Paper.A1FiniteEtaleWeilFibreComparison | unclaimed at audit | Only unchanged relocated exports and instances are relevant. Their signatures, attributes, bodies and public reexports are preserved; no adaptation. |
| Sheaf.Paper.CohomologicalSmoothEtaleLocality | unclaimed at audit | Only unchanged relocated exports and instances are relevant. Their signatures, attributes, bodies and public reexports are preserved; no adaptation. |
| Sheaf.Paper.CompletedStalkFrobeniusReduction | unclaimed at audit | Only unchanged relocated exports and instances are relevant. Their signatures, attributes, bodies and public reexports are preserved; no adaptation. |
| Sheaf.Paper.ConnectedConstantH0 | unclaimed at audit | Only unchanged relocated exports and instances are relevant. Their signatures, attributes, bodies and public reexports are preserved; no adaptation. |
| Sheaf.Paper.ConstantExtensionCompactComparison | unclaimed at audit | Only unchanged relocated exports and instances are relevant. Their signatures, attributes, bodies and public reexports are preserved; no adaptation. |
| Sheaf.Paper.ConstantExtensionWeilHeartEquivalence | unclaimed at audit | Only unchanged relocated exports and instances are relevant. Their signatures, attributes, bodies and public reexports are preserved; no adaptation. |
| Sheaf.Paper.CurveIntermediateExtension | unclaimed at audit | Only unchanged relocated exports and instances are relevant. Their signatures, attributes, bodies and public reexports are preserved; no adaptation. |
| Sheaf.Paper.DlConstantFieldCharts | unclaimed at audit | Only unchanged relocated exports and instances are relevant. Their signatures, attributes, bodies and public reexports are preserved; no adaptation. |
| Sheaf.Paper.FinitePointInternalHomEvaluation | unclaimed at audit | Only unchanged relocated exports and instances are relevant. Their signatures, attributes, bodies and public reexports are preserved; no adaptation. |
| Sheaf.Paper.FiniteTorStability | unclaimed at audit | Only unchanged relocated exports and instances are relevant. Their signatures, attributes, bodies and public reexports are preserved; no adaptation. |
| Sheaf.Paper.FixedStalkIdentificationReduction | unclaimed at audit | Uses prescribed ordinary equations and universal derived pair; unchanged source compiled; existing holes untouched. |
| Sheaf.Paper.FrobeniusFixesUnitSection | unclaimed at audit | Only unchanged relocated exports and instances are relevant. Their signatures, attributes, bodies and public reexports are preserved; no adaptation. |
| Sheaf.Paper.GlobalVerdierDuality | unclaimed at audit | Only unchanged relocated exports and instances are relevant. Their signatures, attributes, bodies and public reexports are preserved; no adaptation. |
| Sheaf.Paper.LocalFrobeniusTransportNormalization | unclaimed at audit | Only unchanged relocated exports and instances are relevant. Their signatures, attributes, bodies and public reexports are preserved; no adaptation. |
| Sheaf.Paper.PointCompletedEvaluation | unclaimed at audit | Only unchanged relocated exports and instances are relevant. Their signatures, attributes, bodies and public reexports are preserved; no adaptation. |
| Sheaf.Paper.PointReductionUnitNormalization | unclaimed at audit | Uses the abstract functor and unit; unchanged source compiled with the adapted unit module. |
| Sheaf.Paper.PointReductionUnits | unclaimed at audit | Two public proofs use typed model fields; private adjunction proof unpacks witnesses. All signatures, visibility and public imports preserved; compiled. |
| Sheaf.Paper.QbarPerverseSubcategories | unclaimed at audit | Only unchanged relocated exports and instances are relevant. Their signatures, attributes, bodies and public reexports are preserved; no adaptation. |
| Sheaf.Paper.QbarPerverseSupportCondition | unclaimed at audit | Only unchanged relocated exports and instances are relevant. Their signatures, attributes, bodies and public reexports are preserved; no adaptation. |
| Sheaf.Paper.RationalHomScalarTranspose | unclaimed at audit | Only unchanged relocated exports and instances are relevant. Their signatures, attributes, bodies and public reexports are preserved; no adaptation. |
| Sheaf.Paper.RationalScalarTransposeCompatibility | unclaimed at audit | Only unchanged relocated exports and instances are relevant. Their signatures, attributes, bodies and public reexports are preserved; no adaptation. |
| Sheaf.Paper.RationalStalkExact | unclaimed at audit | Only unchanged relocated exports and instances are relevant. Their signatures, attributes, bodies and public reexports are preserved; no adaptation. |
| Sheaf.Paper.RationalTensorSymmetry | unclaimed at audit | Only unchanged relocated exports and instances are relevant. Their signatures, attributes, bodies and public reexports are preserved; no adaptation. |
| Sheaf.Paper.RationalVerdierEvaluationAdjoints | unclaimed at audit | Only unchanged relocated exports and instances are relevant. Their signatures, attributes, bodies and public reexports are preserved; no adaptation. |
| Sheaf.Paper.SfBidualityClass | unclaimed at audit | Only unchanged relocated exports and instances are relevant. Their signatures, attributes, bodies and public reexports are preserved; no adaptation. |
| Sheaf.Paper.SitePerfectRationalBidual | unclaimed at audit | Only unchanged relocated exports and instances are relevant. Their signatures, attributes, bodies and public reexports are preserved; no adaptation. |
| Sheaf.Paper.SmoothPullbackSupportDimension | unclaimed at audit | Only unchanged relocated exports and instances are relevant. Their signatures, attributes, bodies and public reexports are preserved; no adaptation. |
| Sheaf.Paper.TateTwistSupportCondition | unclaimed at audit | Only unchanged relocated exports and instances are relevant. Their signatures, attributes, bodies and public reexports are preserved; no adaptation. |
| Sheaf.Paper.TraceFormulaTopologicalInvariance | unclaimed at audit | Only unchanged relocated exports and instances are relevant. Their signatures, attributes, bodies and public reexports are preserved; no adaptation. |
| Sheaf.Paper.WeilConstantExtensionFrobenius | unclaimed at audit | Only unchanged relocated exports and instances are relevant. Their signatures, attributes, bodies and public reexports are preserved; no adaptation. |
| Sheaf.Paper.WeilPullbackLocalFrobenius | unclaimed at audit | Only unchanged relocated exports and instances are relevant. Their signatures, attributes, bodies and public reexports are preserved; no adaptation. |
| Sheaf.SixFunctors.CoefDualFormulaScalarTranspose | unclaimed at audit | Only unchanged relocated exports and instances are relevant. Their signatures, attributes, bodies and public reexports are preserved; no adaptation. |
| Sheaf.SixFunctors.CoefIntegralFiniteExtension | unclaimed at audit | Only unchanged relocated exports and instances are relevant. Their signatures, attributes, bodies and public reexports are preserved; no adaptation. |
| Sheaf.SixFunctors.CoefQbarVerdier | unclaimed at audit | Only unchanged relocated exports and instances are relevant. Their signatures, attributes, bodies and public reexports are preserved; no adaptation. |
| Sheaf.SixFunctors.CoefTowerNaturalCurrying | unclaimed at audit | Only unchanged relocated exports and instances are relevant. Their signatures, attributes, bodies and public reexports are preserved; no adaptation. |
| Sheaf.SixFunctors.CoefVerdierWeilEquivariance | unclaimed at audit | Only unchanged relocated exports and instances are relevant. Their signatures, attributes, bodies and public reexports are preserved; no adaptation. |
| Sheaf.SixFunctors.FiniteAdjunctionDiagramRealization | unclaimed at audit | Only unchanged relocated exports and instances are relevant. Their signatures, attributes, bodies and public reexports are preserved; no adaptation. |
| Sheaf.SixFunctors.FiniteAdjunctionSystemData | unclaimed at audit | Only unchanged relocated exports and instances are relevant. Their signatures, attributes, bodies and public reexports are preserved; no adaptation. |
| Sheaf.SixFunctors.FiniteAdjunctionTransition | unclaimed at audit | Only unchanged relocated exports and instances are relevant. Their signatures, attributes, bodies and public reexports are preserved; no adaptation. |
| Sheaf.SixFunctors.FiniteExceptional | unclaimed at audit | Only unchanged relocated exports and instances are relevant. Their signatures, attributes, bodies and public reexports are preserved; no adaptation. |
| Sheaf.SixFunctors.FiniteMappingAdjunction | unclaimed at audit | Only unchanged relocated exports and instances are relevant. Their signatures, attributes, bodies and public reexports are preserved; no adaptation. |
| Sheaf.SixFunctors.IntegralDualizing | unclaimed at audit | Only unchanged relocated exports and instances are relevant. Their signatures, attributes, bodies and public reexports are preserved; no adaptation. |
| Sheaf.SixFunctors.IntegralVerdier | unclaimed at audit | Only unchanged relocated exports and instances are relevant. Their signatures, attributes, bodies and public reexports are preserved; no adaptation. |
| Sheaf.SixFunctors.NormalizedTowerTensorEvaluation | unclaimed at audit | Only unchanged relocated exports and instances are relevant. Their signatures, attributes, bodies and public reexports are preserved; no adaptation. |
| Sheaf.SixFunctors.RationalOperations | unclaimed at audit | Only unchanged relocated exports and instances are relevant. Their signatures, attributes, bodies and public reexports are preserved; no adaptation. |
| Sheaf.SixFunctors.RationalRetractEvaluation | unclaimed at audit | Only unchanged relocated exports and instances are relevant. Their signatures, attributes, bodies and public reexports are preserved; no adaptation. |
| Sheaf.SixFunctors.RationalVerdier | unclaimed at audit | Only unchanged relocated exports and instances are relevant. Their signatures, attributes, bodies and public reexports are preserved; no adaptation. |

The downstream audit was repeated after the shared tree gained the fixed-stalk consumer.
All 49 downstream users are listed above. Other downstream files use the exported point-sections theorem or unchanged aliases,
not raw choice projections. All 49 currently downstream modules were searched for the
changed declaration names; the direct uses are accounted for above.

The original PointReductionUnits fails with an unsolved conversion goal identifying
`(pointFiniteReductionSheafModel ...).F ⊣ restrictScalars ...` with
`z.choose ⊣ restrictScalars ...`, and the corresponding counit-normalization goal.
The original object-equation proof likewise refers to the old witness.
The public adaptations change only these witness references, use exact application
instead of recursive conversion, and add local irreducibility of the typed model.
A final batch exposed a 60-second consumer timeout. Profiling identified repeated
reduction of existential adjunction witnesses in the existing private normalization.
That private proof now obtains the limit/colimit witnesses and adjunct data by
existential elimination, and unpacks the normalized equation before applying the
generic cochain lemma. This preserves the same mathematical argument and avoids
large choice projections in kernel conversion. No public signature changes.
No source-library module is edited.

## Status

landed 20261021T061705-L-1812936 2026-10-21 (merge of deliver/T4/Sheaf.Paper.PointSectionsFiniteReduction)
