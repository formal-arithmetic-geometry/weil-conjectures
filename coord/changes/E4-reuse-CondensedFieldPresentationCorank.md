# Sheaf.AlgebraicGeometry.CondensedFieldPresentationCorank

## Reason

The returned delivery copied the coordinate and corank API from this module. Generalize its private coordinate construction and four proved lemmas in place to independent field and vector-space universes, and expose the coordinate definition, matrix lemma and cokernel-dimension lemma. The apply and single-vector lemmas stay private implementation details. This allows the item to use the existing API at Type 0 coefficients and ModuleCat.{u + 1}. The existing public corank theorem is unchanged. The definition body is unchanged except for its universe parameters. The public biproduct import makes the public definition body available to importers.

Both the original and changed module are checked against current shared sources. This module is unclaimed. No target statement or target-used definition changes meaning; no target statement review is reopened. Zero ranks and empty schemes remain covered.

## Old

```lean
universe u v₁ w₁
import Mathlib.Algebra.Category.ModuleCat.Biproducts

section FiniteFreeCoordinates

variable {E : Type u} [Field E]
variable {D : Type v₁} [Category.{w₁} D] [Preadditive D] [HasFiniteBiproducts D]
variable (A : D) (F : D ⥤ ModuleCat.{u + 1} E) [F.Additive]
variable (e : F.obj A ≃ₗ[E] E)

/-- Coordinates obtained from the biproduct comparison and the regular-module coordinates. -/
@[irreducible] private noncomputable def finiteFreeEvaluationCoords (k : ℕ) :
    F.obj (⨁ fun _ : Fin k ↦ A) ≃ₗ[E] (Fin k → E) :=
  ((F.mapBiproduct (fun _ : Fin k ↦ A)).toLinearEquiv.trans
    (ModuleCat.biproductIsoPi (fun _ : Fin k ↦ F.obj A)).toLinearEquiv).trans
      (LinearEquiv.piCongrRight fun _ ↦ e)

private lemma finiteFreeEvaluationCoords_apply (k : ℕ) (j : Fin k)
    (x : F.obj (⨁ fun _ : Fin k ↦ A)) :
    finiteFreeEvaluationCoords A F e k x j = e ((F.map (biproduct.π (fun _ : Fin k ↦ A) j)) x) := by
  unfold finiteFreeEvaluationCoords
  change e (((ModuleCat.biproductIsoPi _).hom ≫
    ModuleCat.ofHom (LinearMap.proj j)).hom
      ((F.mapBiproduct (fun _ : Fin k ↦ A)).hom x)) = _
  congr 1
  have hp : (ModuleCat.biproductIsoPi (F.obj ∘ (fun _ : Fin k ↦ A))).hom ≫
      ModuleCat.ofHom (LinearMap.proj j) = biproduct.π _ j := by
    rw [← ModuleCat.biproductIsoPi_inv_comp_π, Iso.hom_inv_id_assoc]
  have h := F.biproductComparison_π (fun _ : Fin k ↦ A) j
  rw [← hp] at h
  exact congrArg (fun t ↦ t x) h

private lemma finiteFreeEvaluationCoords_symm_single (k : ℕ) (j : Fin k) (x : E) :
    (finiteFreeEvaluationCoords A F e k).symm (Pi.single j x) =
      F.map (biproduct.ι (fun _ : Fin k ↦ A) j) (e.symm x) := by
  classical
  apply (finiteFreeEvaluationCoords A F e k).injective
  ext i
  rw [LinearEquiv.apply_symm_apply, finiteFreeEvaluationCoords_apply]
  change (Pi.single j x : Fin k → E) i = e ((F.map (biproduct.ι (fun _ : Fin k ↦ A) j) ≫
      F.map (biproduct.π (fun _ : Fin k ↦ A) i))
    (e.symm x))
  rw [← F.map_comp]
  by_cases h : j = i
  · subst i
    simp
  · simp [h]

private lemma finiteFreeEvaluationCoords_matrix (m n : ℕ)
    (f : (⨁ fun _ : Fin m ↦ A) ⟶ ⨁ fun _ : Fin n ↦ A)
    (M : Matrix (Fin n) (Fin m) E)
    (h : ∀ i j, e (F.map (biproduct.ι _ j ≫ f ≫ biproduct.π _ i) (e.symm 1)) =
      M i j) :
    (finiteFreeEvaluationCoords A F e n).toLinearMap ∘ₗ (F.map f).hom ∘ₗ
      (finiteFreeEvaluationCoords A F e m).symm.toLinearMap = M.mulVecLin := by
  classical
  apply LinearMap.toMatrix'.injective
  ext i j
  rw [LinearMap.toMatrix'_apply]
  change finiteFreeEvaluationCoords A F e n
    (F.map f ((finiteFreeEvaluationCoords A F e m).symm (Pi.single j 1))) i = _
  rw [finiteFreeEvaluationCoords_symm_single, finiteFreeEvaluationCoords_apply]
  simpa only [Functor.map_comp, ModuleCat.comp_apply, LinearMap.toMatrix'_apply,
    Matrix.mulVecLin_apply, Matrix.mulVec_single_one, Matrix.col_apply] using h i j

end FiniteFreeCoordinates

private lemma finrank_cokernel_of_matrix
    {E : Type u} [Field E] {A B : ModuleCat.{u + 1} E}
    {m n : ℕ} (a : A ≃ₗ[E] (Fin m → E)) (b : B ≃ₗ[E] (Fin n → E))
    (f : A ⟶ B) (M : Matrix (Fin n) (Fin m) E)
    (hf : b.toLinearMap ∘ₗ f.hom ∘ₗ a.symm.toLinearMap = M.mulVecLin) :
    Module.finrank E (cokernel f : ModuleCat.{u + 1} E) = n - M.rank := by
  have : Module.Finite E B := Module.Finite.of_injective b.toLinearMap b.injective
  have hr : M.rank = Module.finrank E (LinearMap.range f.hom) := by
    change Module.finrank E (LinearMap.range M.mulVecLin) = _
    rw [← hf, LinearMap.range_comp, LinearMap.range_comp,
      LinearMap.range_eq_top.2 a.symm.surjective, Submodule.map_top]
    exact b.finrank_map_eq _
  calc
    Module.finrank E (cokernel f : ModuleCat.{u + 1} E) =
        Module.finrank E (B ⧸ LinearMap.range f.hom) :=
      (ModuleCat.cokernelIsoRangeQuotient f).toLinearEquiv.finrank_eq
    _ = Module.finrank E B - Module.finrank E (LinearMap.range f.hom) :=
      Nat.eq_sub_of_add_eq (Submodule.finrank_quotient_add_finrank _)
    _ = n - M.rank := by
      rw [b.finrank_eq, Module.finrank_pi, Fintype.card_fin, ← hr]
```

## New

```lean
universe u v w v₁ w₁
public import Mathlib.Algebra.Category.ModuleCat.Biproducts

section FiniteFreeCoordinates

variable {E : Type v} [Field E]
variable {D : Type v₁} [Category.{w₁} D] [Preadditive D] [HasFiniteBiproducts D]
variable (A : D) (F : D ⥤ ModuleCat.{w} E) [F.Additive]
variable (e : F.obj A ≃ₗ[E] E)

/-- Coordinates obtained from the biproduct comparison and the regular-module coordinates. -/
@[irreducible] noncomputable def finiteFreeEvaluationCoords (k : ℕ) :
    F.obj (⨁ fun _ : Fin k ↦ A) ≃ₗ[E] (Fin k → E) :=
  ((F.mapBiproduct (fun _ : Fin k ↦ A)).toLinearEquiv.trans
    (ModuleCat.biproductIsoPi (fun _ : Fin k ↦ F.obj A)).toLinearEquiv).trans
      (LinearEquiv.piCongrRight fun _ ↦ e)

private lemma finiteFreeEvaluationCoords_apply (k : ℕ) (j : Fin k)
    (x : F.obj (⨁ fun _ : Fin k ↦ A)) :
    finiteFreeEvaluationCoords A F e k x j = e ((F.map (biproduct.π (fun _ : Fin k ↦ A) j)) x) := by
  unfold finiteFreeEvaluationCoords
  change e (((ModuleCat.biproductIsoPi _).hom ≫
    ModuleCat.ofHom (LinearMap.proj j)).hom
      ((F.mapBiproduct (fun _ : Fin k ↦ A)).hom x)) = _
  congr 1
  have hp : (ModuleCat.biproductIsoPi (F.obj ∘ (fun _ : Fin k ↦ A))).hom ≫
      ModuleCat.ofHom (LinearMap.proj j) = biproduct.π _ j := by
    rw [← ModuleCat.biproductIsoPi_inv_comp_π, Iso.hom_inv_id_assoc]
  have h := F.biproductComparison_π (fun _ : Fin k ↦ A) j
  rw [← hp] at h
  exact congrArg (fun t ↦ t x) h

private lemma finiteFreeEvaluationCoords_symm_single (k : ℕ) (j : Fin k) (x : E) :
    (finiteFreeEvaluationCoords A F e k).symm (Pi.single j x) =
      F.map (biproduct.ι (fun _ : Fin k ↦ A) j) (e.symm x) := by
  classical
  apply (finiteFreeEvaluationCoords A F e k).injective
  ext i
  rw [LinearEquiv.apply_symm_apply, finiteFreeEvaluationCoords_apply]
  change (Pi.single j x : Fin k → E) i = e ((F.map (biproduct.ι (fun _ : Fin k ↦ A) j) ≫
      F.map (biproduct.π (fun _ : Fin k ↦ A) i))
    (e.symm x))
  rw [← F.map_comp]
  by_cases h : j = i
  · subst i
    simp
  · simp [h]

lemma finiteFreeEvaluationCoords_matrix (m n : ℕ)
    (f : (⨁ fun _ : Fin m ↦ A) ⟶ ⨁ fun _ : Fin n ↦ A)
    (M : Matrix (Fin n) (Fin m) E)
    (h : ∀ i j, e (F.map (biproduct.ι _ j ≫ f ≫ biproduct.π _ i) (e.symm 1)) =
      M i j) :
    (finiteFreeEvaluationCoords A F e n).toLinearMap ∘ₗ (F.map f).hom ∘ₗ
      (finiteFreeEvaluationCoords A F e m).symm.toLinearMap = M.mulVecLin := by
  classical
  apply LinearMap.toMatrix'.injective
  ext i j
  rw [LinearMap.toMatrix'_apply]
  change finiteFreeEvaluationCoords A F e n
    (F.map f ((finiteFreeEvaluationCoords A F e m).symm (Pi.single j 1))) i = _
  rw [finiteFreeEvaluationCoords_symm_single, finiteFreeEvaluationCoords_apply]
  simpa only [Functor.map_comp, ModuleCat.comp_apply, LinearMap.toMatrix'_apply,
    Matrix.mulVecLin_apply, Matrix.mulVec_single_one, Matrix.col_apply] using h i j

end FiniteFreeCoordinates

lemma finrank_cokernel_of_matrix
    {E : Type v} [Field E] {A B : ModuleCat.{w} E}
    {m n : ℕ} (a : A ≃ₗ[E] (Fin m → E)) (b : B ≃ₗ[E] (Fin n → E))
    (f : A ⟶ B) (M : Matrix (Fin n) (Fin m) E)
    (hf : b.toLinearMap ∘ₗ f.hom ∘ₗ a.symm.toLinearMap = M.mulVecLin) :
    Module.finrank E (cokernel f : ModuleCat.{w} E) = n - M.rank := by
  have : Module.Finite E B := Module.Finite.of_injective b.toLinearMap b.injective
  have hr : M.rank = Module.finrank E (LinearMap.range f.hom) := by
    change Module.finrank E (LinearMap.range M.mulVecLin) = _
    rw [← hf, LinearMap.range_comp, LinearMap.range_comp,
      LinearMap.range_eq_top.2 a.symm.surjective, Submodule.map_top]
    exact b.finrank_map_eq _
  calc
    Module.finrank E (cokernel f : ModuleCat.{w} E) =
        Module.finrank E (B ⧸ LinearMap.range f.hom) :=
      (ModuleCat.cokernelIsoRangeQuotient f).toLinearEquiv.finrank_eq
    _ = Module.finrank E B - Module.finrank E (LinearMap.range f.hom) :=
      Nat.eq_sub_of_add_eq (Submodule.finrank_quotient_add_finrank _)
    _ = n - M.rank := by
      rw [b.finrank_eq, Module.finrank_pi, Fintype.card_fin, ← hr]
```

## Users

Every transitive importer from tools/downstream.py is listed, together with the new callers. The original helpers had no external users while private.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.CondensedConstructibleSerre | unclaimed | No statement or definition changes; no adaptation |
| Sheaf.AlgebraicGeometry.CondensedFieldLfpLocalTriviality | unclaimed | No statement or definition changes; no adaptation |
| Sheaf.AlgebraicGeometry.CondensedFieldPresentationCorank | unclaimed | API exposed/generalized as above |
| Sheaf.Paper.CondensedCoefficientComparisons | unclaimed | No statement or definition changes; no adaptation |
| Sheaf.Paper.CondensedFiniteModelExtensions | unclaimed | No statement or definition changes; no adaptation |
| Sheaf.Paper.CondensedFiniteModelProofAPI | unclaimed | No statement or definition changes; no adaptation |
| Sheaf.Paper.CondensedFinitePresentationDescent | unclaimed | No statement or definition changes; no adaptation |
| Sheaf.Paper.CondensedFlatCoefficientCalculus | unclaimed | No statement or definition changes; no adaptation |
| Sheaf.Paper.CondensedLfpHomContinuity | unclaimed | No statement or definition changes; no adaptation |
| Sheaf.Paper.CondensedLocalPieceHomContinuity | unclaimed | No statement or definition changes; no adaptation |
| Sheaf.Paper.CondensedQbarBaseChangeCompatibility | unclaimed | No statement or definition changes; no adaptation |
| Sheaf.Paper.CondensedQbarComparisons | unclaimed | No statement or definition changes; no adaptation |
| Sheaf.Paper.CondensedQbarExchangeEquality | A3 | No statement or definition changes; no adaptation |
| Sheaf.Paper.CondensedQbarLfpLocalTriviality | unclaimed | No statement or definition changes; no adaptation |
| Sheaf.Paper.CondensedQbarLfpMatrixRefinement | unclaimed | No statement or definition changes; no adaptation |
| Sheaf.Paper.CondensedSheafExtContinuity | unclaimed | No statement or definition changes; no adaptation |
| Sheaf.Paper.CondensedStratumModelAssembly | unclaimed | No statement or definition changes; no adaptation |
| Sheaf.Paper.CondensedStratumModelInductionStep | unclaimed | No statement or definition changes; no adaptation |
| Sheaf.Paper.CondensedStratumModelInductionStepEmpty | unclaimed | No statement or definition changes; no adaptation |
| Sheaf.Paper.CondensedStratumModelInductionStepNonempty | unclaimed | No statement or definition changes; no adaptation |
| Sheaf.Paper.CondensedStratumModelInductionStepNonemptyGluing | unclaimed | No statement or definition changes; no adaptation |
| Sheaf.Paper.ConstructibleCokernelsExtensions | unclaimed | No statement or definition changes; no adaptation |
| Sheaf.Paper.ContinuousConstructibleIntegralDenominators | unclaimed | No statement or definition changes; no adaptation |
| Sheaf.Paper.ContinuousConstructibleIntegralGluing | unclaimed | No statement or definition changes; no adaptation |
| Sheaf.Paper.ContinuousConstructibleIntegralImage | unclaimed | No statement or definition changes; no adaptation |
| Sheaf.Paper.ContinuousConstructibleIntegralModel | unclaimed | No statement or definition changes; no adaptation |
| Sheaf.Paper.ContinuousConstructibleIntegralSingle | unclaimed | No statement or definition changes; no adaptation |
| Sheaf.Paper.ContinuousConstructibleIntegralStratum | unclaimed | No statement or definition changes; no adaptation |
| Sheaf.Paper.ContinuousExchangeIntegralModel | unclaimed | No statement or definition changes; no adaptation |
| Sheaf.Paper.ContinuousFiniteEtaleLatticeDescent | unclaimed | No statement or definition changes; no adaptation |
| Sheaf.Paper.ContinuousFiniteFreeKernelModel | unclaimed | No statement or definition changes; no adaptation |
| Sheaf.Paper.ContinuousIntegralComplexTelescope | unclaimed | No statement or definition changes; no adaptation |
| Sheaf.Paper.ContinuousIntegralExchangeSquare | unclaimed | No statement or definition changes; no adaptation |
| Sheaf.Paper.ContinuousIntegralLocalization | unclaimed | No statement or definition changes; no adaptation |
| Sheaf.Paper.ContinuousIntegralLocalizationColimitTransport | unclaimed | No statement or definition changes; no adaptation |
| Sheaf.Paper.ContinuousIntegralLocalizationContinuity | unclaimed | No statement or definition changes; no adaptation |
| Sheaf.Paper.ContinuousIntegralLocalizationCounit | unclaimed | No statement or definition changes; no adaptation |
| Sheaf.Paper.ContinuousIntegralLocalizationHomology | unclaimed | No statement or definition changes; no adaptation |
| Sheaf.Paper.ContinuousIntegralLocalizationLegs | unclaimed | No statement or definition changes; no adaptation |
| Sheaf.Paper.ContinuousIntegralLocalizationMate | unclaimed | No statement or definition changes; no adaptation |
| Sheaf.Paper.ContinuousIntegralLocalizationModel | unclaimed | No statement or definition changes; no adaptation |
| Sheaf.Paper.ContinuousIntegralModuleTelescope | unclaimed | No statement or definition changes; no adaptation |
| Sheaf.Paper.ContinuousIntegralPushComparison | unclaimed | No statement or definition changes; no adaptation |
| Sheaf.Paper.ContinuousIntegralRegularTelescope | unclaimed | No statement or definition changes; no adaptation |
| Sheaf.Paper.ContinuousIntegralUnderivedPushComparison | unclaimed | No statement or definition changes; no adaptation |
| Sheaf.Paper.ContinuousLatticeIntersectionLocalModel | unclaimed | No statement or definition changes; no adaptation |
| Sheaf.Paper.ContinuousLatticeIntersectionRationalModel | unclaimed | No statement or definition changes; no adaptation |
| Sheaf.Paper.ContinuousLatticeIntersectionRationalization | unclaimed | No statement or definition changes; no adaptation |
| Sheaf.Paper.ContinuousLatticeIntersectionSplitData | B2 | No statement or definition changes; no adaptation |
| Sheaf.Paper.ContinuousLatticeIntersectionSplitModel | unclaimed | No statement or definition changes; no adaptation |
| Sheaf.Paper.ContinuousLisseStratifiedLattices | unclaimed | No statement or definition changes; no adaptation |
| Sheaf.Paper.IntegralConstructibleKernels | unclaimed | No statement or definition changes; no adaptation |
| Sheaf.Paper.IntegralConstructibleNakayama | unclaimed | No statement or definition changes; no adaptation |
| Sheaf.Paper.IntegralConstructibleSequentialHom | unclaimed | No statement or definition changes; no adaptation |
| Sheaf.Paper.IntegralConstructibleSerre | unclaimed | No statement or definition changes; no adaptation |
| Sheaf.Paper.IntegralConstructibleSheafHom | unclaimed | No statement or definition changes; no adaptation |
| Sheaf.Paper.IntegralExchangeReduction | unclaimed | No statement or definition changes; no adaptation |
| Sheaf.Paper.IntegralFiniteExchangeComparison | unclaimed | No statement or definition changes; no adaptation |
| Sheaf.Paper.IntegralLfpEventualFreeImage | unclaimed | No statement or definition changes; no adaptation |
| Sheaf.Paper.IntegralLfpFiniteQuotientCharts | unclaimed | No statement or definition changes; no adaptation |
| Sheaf.Paper.IntegralLfpHomContinuity | unclaimed | No statement or definition changes; no adaptation |
| Sheaf.Paper.IntegralLfpLocalTorsionCharts | unclaimed | No statement or definition changes; no adaptation |
| Sheaf.Paper.IntegralLfpLocallyFreeResolution | unclaimed | No statement or definition changes; no adaptation |
| Sheaf.Paper.IntegralMatrixCoefficientTransport | E4 (new) | Imports and uses shared API; theorem signature unchanged |
| Sheaf.Paper.IntegralMatrixKernelLocallyFree | unclaimed | Imports and uses shared API; theorem signature unchanged |
| Sheaf.Paper.IntegralMatrixPointwiseRank | E4 | Imports and uses shared API; theorem signature unchanged |
| Sheaf.Paper.IntegralReductionConservative | unclaimed | No statement or definition changes; no adaptation |
| Sheaf.Paper.IntegralReductionConstructible | unclaimed | No statement or definition changes; no adaptation |
| Sheaf.Paper.IntegralResidueExchange | unclaimed | No statement or definition changes; no adaptation |
| Sheaf.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperApp | unclaimed | No statement or definition changes; no adaptation |
| TargetsCheck | unclaimed | No statement or definition changes; no adaptation |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.CompactSupport | unclaimed | No statement or definition changes; no adaptation |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.Proper | unclaimed | No statement or definition changes; no adaptation |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit | unclaimed | No statement or definition changes; no adaptation |

## Status

landed 20261016T093726-L-2050747 2026-10-16 (merge of deliver/E4/Sheaf.Paper.IntegralMatrixPointwiseRank)
