# CategoryTheory.RingedSiteDualityModel

## Reason

The generated constructor-injectivity and size-of specification lemmas unfold the native
derived coefficient category while Lean writes compiled artifacts. The original module,
without any worker proofs, exceeded the per-file limit. With only the original model
structure, artifact generation took 30.2 seconds; disabling constructor-injectivity
lemma generation reduced that check to 15.4 seconds. These generated helpers are not
used by this argument or any checked downstream source. The standard Mathlib options
also avoid generating the unused size-of specification lemma.

The structure's fields, their types, constructor and projections are verbatim. No data
construction, target statement, or target meaning changes. No source-library module
under WeilConjectures is changed. This is a change to unused generated helper availability,
not to the record presented to consumers. The independent review should check this
interface change together with the compilation result.

## Old

```lean
structure RingedSiteDualityModel where
  /-- The existing closed tensor-Hom structure. -/
  closed : WeilConjectures.CoefficientClosedStructure
    (derivedInternalHomOfUniverses.{c, v, r, w} J R)
  /-- The existing pure-tensor normalization of its adjunction. -/
  models : WeilConjectures.CoefficientTensorModels.{r, c, v, w} J R closed
  /-- Symmetry of this same tensor structure. -/
  symmetric : @SymmetricCategory _ _ closed.monoidal
  /-- Identification of its tensor unit with the coefficient in degree zero. -/
  unitIso : closed.monoidal.tensorUnit ≅ ringedSiteDualityUnit.{c, v, r, w} J R
  /-- The ordinary coefficient complex is K-flat. -/
  unitKFlat : CochainComplex.IsKFlatIndependentCoefficients.{c, v, max c v r} (J := J) (R := R)
    (ringedSiteDualityUnitComplex.{c, v, r} J R)
  /-- The symmetry descends the actual signed interchange of total-complex summands. -/
  symmetry_model : ∀ (P Q : CochainComplex (SheafOfModules.{max c v r}
      ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) ℤ) (hP :
      CochainComplex.IsKFlatIndependentCoefficients.{c, v, max c v r} (J := J) (R := R) P) (hQ :
      CochainComplex.IsKFlatIndependentCoefficients.{c, v, max c v r} (J := J) (R := R) Q),
    ∃ σ : (WeilConjectures.coefficientTotalTensor.{r, c, v} J R).obj (P, Q) ⟶
      (WeilConjectures.coefficientTotalTensor.{r, c, v} J R).obj (Q, P),
      (∀ (p q k : ℤ) (h : p + q = k) (h' : q + p = k) (U : Cᵒᵖ)
        (x : (P.X p).val.obj U) (y : (Q.X q).val.obj U),
        (σ.f k).val.app U (WeilConjectures.coefficientTensorGenerator.{r, c, v} J R P Q p q k h U x
      y) =
          (p * q).negOnePow • WeilConjectures.coefficientTensorGenerator.{r, c, v} J R Q P q p k h'
      U y x) ∧
      (models.iso J R closed P Q hP hQ).hom ≫
          (symmetric.braiding (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj Q)).hom =
        DerivedCategory.Q.map σ ≫ (models.iso J R closed Q P hQ hP).hom
  /-- The right unit constraint is induced by the actual scalar multiplication map. -/
  unit_model : ∀ (P : CochainComplex (SheafOfModules.{max c v r}
      ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) ℤ) (hP :
      CochainComplex.IsKFlatIndependentCoefficients.{c, v, max c v r} (J := J) (R := R) P),
    ∃ ρ : (WeilConjectures.coefficientTotalTensor.{r, c, v} J R).obj (P,
      ringedSiteDualityUnitComplex.{c, v, r} J R) ⟶ P,
      (∀ (p : ℤ) (U : Cᵒᵖ) (x : (P.X p).val.obj U)
        (a : ((ringedSiteDualityUnitComplex.{c, v, r} J R).X 0).val.obj U),
        (ρ.f p).val.app U
            (WeilConjectures.coefficientTensorGenerator.{r, c, v} J R P
      (ringedSiteDualityUnitComplex.{c, v, r} J R)
              p 0 p (Int.add_zero p) U x a) = a • x) ∧
      (models.iso J R closed P (ringedSiteDualityUnitComplex.{c, v, r} J R)
          hP unitKFlat).hom ≫ closed.tensor.map (Prod.mkHom (𝟙 _) unitIso.inv) ≫
          (closed.monoidal.rightUnitor (DerivedCategory.Q.obj P)).hom = DerivedCategory.Q.map ρ
  /-- The associator descends the actual reassociation of total-complex summands. -/
  associator_model : ∀ (P Q V : CochainComplex (SheafOfModules.{max c v r}
      ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) ℤ)
      (hP : CochainComplex.IsKFlatIndependentCoefficients.{c, v, max c v r} (J := J) (R := R) P)
      (hQ : CochainComplex.IsKFlatIndependentCoefficients.{c, v, max c v r} (J := J) (R := R) Q)
      (hV : CochainComplex.IsKFlatIndependentCoefficients.{c, v, max c v r} (J := J) (R := R) V),
    ∃ α : (WeilConjectures.coefficientTotalTensor.{r, c, v} J R).obj
      ((WeilConjectures.coefficientTotalTensor.{r, c, v} J R).obj (P, Q), V) ⟶
        (WeilConjectures.coefficientTotalTensor.{r, c, v} J R).obj (P,
      (WeilConjectures.coefficientTotalTensor.{r, c, v} J R).obj (Q, V)),
      (∀ (p q t i j k : ℤ) (hpq : p + q = i) (hit : i + t = k)
        (hqt : q + t = j) (hpj : p + j = k) (U : Cᵒᵖ)
        (x : (P.X p).val.obj U) (y : (Q.X q).val.obj U) (z : (V.X t).val.obj U),
        (α.f k).val.app U
          (WeilConjectures.coefficientTensorGenerator.{r, c, v} J R
      ((WeilConjectures.coefficientTotalTensor.{r, c, v} J R).obj (P, Q)) V i t k hit U
            (WeilConjectures.coefficientTensorGenerator.{r, c, v} J R P Q p q i hpq U x y) z) =
          WeilConjectures.coefficientTensorGenerator.{r, c, v} J R P
      ((WeilConjectures.coefficientTotalTensor.{r, c, v} J R).obj (Q, V)) p j k hpj U x
            (WeilConjectures.coefficientTensorGenerator.{r, c, v} J R Q V q t j hqt U y z)) ∧
      (models.iso J R closed ((WeilConjectures.coefficientTotalTensor.{r, c, v} J R).obj (P, Q)) V
          (WeilConjectures.coefficientTotalTensor_isKFlat.{r, c, v} J R P Q hP hQ) hV).hom ≫
        closed.tensor.map (Prod.mkHom (models.iso J R closed P Q hP hQ).hom (𝟙 _)) ≫
        (closed.monoidal.associator (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj Q)
          (DerivedCategory.Q.obj V)).hom =
      DerivedCategory.Q.map α ≫
        (models.iso J R closed P ((WeilConjectures.coefficientTotalTensor.{r, c, v} J R).obj (Q,
      V)) hP
          (WeilConjectures.coefficientTotalTensor_isKFlat.{r, c, v} J R Q V hQ hV)).hom ≫
        closed.tensor.map (Prod.mkHom (𝟙 _) (models.iso J R closed Q V hQ hV).hom)
```

## New

```lean
set_option genSizeOfSpec false in
set_option genInjectivity false in
structure RingedSiteDualityModel where
  /-- The existing closed tensor-Hom structure. -/
  closed : WeilConjectures.CoefficientClosedStructure
    (derivedInternalHomOfUniverses.{c, v, r, w} J R)
  /-- The existing pure-tensor normalization of its adjunction. -/
  models : WeilConjectures.CoefficientTensorModels.{r, c, v, w} J R closed
  /-- Symmetry of this same tensor structure. -/
  symmetric : @SymmetricCategory _ _ closed.monoidal
  /-- Identification of its tensor unit with the coefficient in degree zero. -/
  unitIso : closed.monoidal.tensorUnit ≅ ringedSiteDualityUnit.{c, v, r, w} J R
  /-- The ordinary coefficient complex is K-flat. -/
  unitKFlat : CochainComplex.IsKFlatIndependentCoefficients.{c, v, max c v r} (J := J) (R := R)
    (ringedSiteDualityUnitComplex.{c, v, r} J R)
  /-- The symmetry descends the actual signed interchange of total-complex summands. -/
  symmetry_model : ∀ (P Q : CochainComplex (SheafOfModules.{max c v r}
      ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) ℤ) (hP :
      CochainComplex.IsKFlatIndependentCoefficients.{c, v, max c v r} (J := J) (R := R) P) (hQ :
      CochainComplex.IsKFlatIndependentCoefficients.{c, v, max c v r} (J := J) (R := R) Q),
    ∃ σ : (WeilConjectures.coefficientTotalTensor.{r, c, v} J R).obj (P, Q) ⟶
      (WeilConjectures.coefficientTotalTensor.{r, c, v} J R).obj (Q, P),
      (∀ (p q k : ℤ) (h : p + q = k) (h' : q + p = k) (U : Cᵒᵖ)
        (x : (P.X p).val.obj U) (y : (Q.X q).val.obj U),
        (σ.f k).val.app U (WeilConjectures.coefficientTensorGenerator.{r, c, v} J R P Q p q k h U x
      y) =
          (p * q).negOnePow • WeilConjectures.coefficientTensorGenerator.{r, c, v} J R Q P q p k h'
      U y x) ∧
      (models.iso J R closed P Q hP hQ).hom ≫
          (symmetric.braiding (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj Q)).hom =
        DerivedCategory.Q.map σ ≫ (models.iso J R closed Q P hQ hP).hom
  /-- The right unit constraint is induced by the actual scalar multiplication map. -/
  unit_model : ∀ (P : CochainComplex (SheafOfModules.{max c v r}
      ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) ℤ) (hP :
      CochainComplex.IsKFlatIndependentCoefficients.{c, v, max c v r} (J := J) (R := R) P),
    ∃ ρ : (WeilConjectures.coefficientTotalTensor.{r, c, v} J R).obj (P,
      ringedSiteDualityUnitComplex.{c, v, r} J R) ⟶ P,
      (∀ (p : ℤ) (U : Cᵒᵖ) (x : (P.X p).val.obj U)
        (a : ((ringedSiteDualityUnitComplex.{c, v, r} J R).X 0).val.obj U),
        (ρ.f p).val.app U
            (WeilConjectures.coefficientTensorGenerator.{r, c, v} J R P
      (ringedSiteDualityUnitComplex.{c, v, r} J R)
              p 0 p (Int.add_zero p) U x a) = a • x) ∧
      (models.iso J R closed P (ringedSiteDualityUnitComplex.{c, v, r} J R)
          hP unitKFlat).hom ≫ closed.tensor.map (Prod.mkHom (𝟙 _) unitIso.inv) ≫
          (closed.monoidal.rightUnitor (DerivedCategory.Q.obj P)).hom = DerivedCategory.Q.map ρ
  /-- The associator descends the actual reassociation of total-complex summands. -/
  associator_model : ∀ (P Q V : CochainComplex (SheafOfModules.{max c v r}
      ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) ℤ)
      (hP : CochainComplex.IsKFlatIndependentCoefficients.{c, v, max c v r} (J := J) (R := R) P)
      (hQ : CochainComplex.IsKFlatIndependentCoefficients.{c, v, max c v r} (J := J) (R := R) Q)
      (hV : CochainComplex.IsKFlatIndependentCoefficients.{c, v, max c v r} (J := J) (R := R) V),
    ∃ α : (WeilConjectures.coefficientTotalTensor.{r, c, v} J R).obj
      ((WeilConjectures.coefficientTotalTensor.{r, c, v} J R).obj (P, Q), V) ⟶
        (WeilConjectures.coefficientTotalTensor.{r, c, v} J R).obj (P,
      (WeilConjectures.coefficientTotalTensor.{r, c, v} J R).obj (Q, V)),
      (∀ (p q t i j k : ℤ) (hpq : p + q = i) (hit : i + t = k)
        (hqt : q + t = j) (hpj : p + j = k) (U : Cᵒᵖ)
        (x : (P.X p).val.obj U) (y : (Q.X q).val.obj U) (z : (V.X t).val.obj U),
        (α.f k).val.app U
          (WeilConjectures.coefficientTensorGenerator.{r, c, v} J R
      ((WeilConjectures.coefficientTotalTensor.{r, c, v} J R).obj (P, Q)) V i t k hit U
            (WeilConjectures.coefficientTensorGenerator.{r, c, v} J R P Q p q i hpq U x y) z) =
          WeilConjectures.coefficientTensorGenerator.{r, c, v} J R P
      ((WeilConjectures.coefficientTotalTensor.{r, c, v} J R).obj (Q, V)) p j k hpj U x
            (WeilConjectures.coefficientTensorGenerator.{r, c, v} J R Q V q t j hqt U y z)) ∧
      (models.iso J R closed ((WeilConjectures.coefficientTotalTensor.{r, c, v} J R).obj (P, Q)) V
          (WeilConjectures.coefficientTotalTensor_isKFlat.{r, c, v} J R P Q hP hQ) hV).hom ≫
        closed.tensor.map (Prod.mkHom (models.iso J R closed P Q hP hQ).hom (𝟙 _)) ≫
        (closed.monoidal.associator (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj Q)
          (DerivedCategory.Q.obj V)).hom =
      DerivedCategory.Q.map α ≫
        (models.iso J R closed P ((WeilConjectures.coefficientTotalTensor.{r, c, v} J R).obj (Q,
      V)) hP
          (WeilConjectures.coefficientTotalTensor_isKFlat.{r, c, v} J R Q V hQ hV)).hom ≫
        closed.tensor.map (Prod.mkHom (𝟙 _) (models.iso J R closed Q V hQ hV).hom)
```

## Users

Ran tools/downstream.py on the item with --uses RingedSiteDualityModel,
RingedSiteDualityModel.mk.injEq, and RingedSiteDualityModel.mk.sizeOf_spec.
Read every model occurrence in the nineteen reported modules. All use the same record,
constructor, or field API. No statement becomes weaker, stronger, or different.
The sole injEq textual hit refers to Option.some.injEq, not this record; sizeOf_spec
has no downstream textual hits. A separate qualified-name search found no uses of the
suppressed record helpers in Sheaf or WeilConjectures. No adaptations are needed.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Algebra.Homology.RingedSliceHomSourceShift | unclaimed | Record fields and constructor unchanged; no suppressed helper used. |
| Sheaf.Algebra.Homology.SitePerfectScalarHomComparison | unclaimed | Record fields and constructor unchanged; no suppressed helper used. |
| Sheaf.CategoryTheory.CoefficientBidualEvaluationShiftOne | unclaimed | Record fields and constructor unchanged; no suppressed helper used. |
| Sheaf.CategoryTheory.CoefficientBidualTriangleCompatibility | unclaimed | Record fields and constructor unchanged; no suppressed helper used. |
| Sheaf.CategoryTheory.RelativeBidualTriangles | unclaimed | Record fields and constructor unchanged; no suppressed helper used. |
| Sheaf.CategoryTheory.RingedSiteDualityMaps | U7 | Own item; all fields preserved and all four holes proved. |
| Sheaf.CategoryTheory.RingedSitePerfectDuality | unclaimed | Record fields and constructor unchanged; no suppressed helper used. |
| Sheaf.CategoryTheory.RingedSitePerfectDualityForModel | unclaimed | Record fields and constructor unchanged; no suppressed helper used. |
| Sheaf.CategoryTheory.RingedSiteSignedDualRestriction | unclaimed | Record fields and constructor unchanged; no suppressed helper used. |
| Sheaf.Paper.FiniteClopenDerivedDecomposition | unclaimed | Record fields and constructor unchanged; no suppressed helper used. |
| Sheaf.Paper.HomFiniteProjective | unclaimed | Record fields and constructor unchanged; no suppressed helper used. |
| Sheaf.Paper.IntegralDerivedOperationsOnSlices | unclaimed | Record fields and constructor unchanged; no suppressed helper used. |
| Sheaf.Paper.IntegralLineReductionDefinitions | unclaimed | Record fields and constructor unchanged; no suppressed helper used. |
| Sheaf.Paper.NormalizedCompletedOperationModels | unclaimed | Record fields and constructor unchanged; no suppressed helper used. |
| Sheaf.Paper.PuritySourceTransports | unclaimed | Record fields and constructor unchanged; no suppressed helper used. |
| Sheaf.Paper.RationalRealizationTensorComparison | unclaimed | Record fields and constructor unchanged; no suppressed helper used. |
| Sheaf.Paper.RationalSmoothPurityCanonical | unclaimed | Record fields and constructor unchanged; no suppressed helper used. |
| Sheaf.Paper.SixFunctorDatum | unclaimed | Record fields and constructor unchanged; no suppressed helper used. |
| Sheaf.Paper.SmoothPurityTowerP1Adjunction | unclaimed | Record fields and constructor unchanged; no suppressed helper used. |
| Sheaf.SixFunctors.IntegralExpressionOccurrences | unclaimed | Textual injEq hit is Option.some.injEq at line 578; unrelated and unchanged. |

The `import all` consumers `RingedSiteFiniteRetractDualExact` and
`CoefficientBidualEvaluationShiftOne` also retain their exact private bidual helper
interface: section evaluation, sheaf bidual, components, degree projections and their
general evaluation formula remain verbatim. Neither consumer requires adaptation.

## Status

landed 20261022T114252-L-597874 2026-10-22 (merge of deliver/U7/Sheaf.CategoryTheory.RingedSiteDualityMaps)
