/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingOperations
public import WeilConjectures.Algebra.Homology.CanonicalTensorPullbackOfUniverses.RingedTopoiCanonicalTensorPullbackOfUniverses
public import WeilConjectures.Algebra.Homology.Strict.StrictPerfectCoefficientPackageOfUniverses
public import WeilConjectures.AlgebraicGeometry.ProEtale.Projection.ProEtaleProjectionFormulaArrows
public import WeilConjectures.Algebra.Homology.RingedTensorCorner.ProjectionMateExact
public import WeilConjectures.Algebra.Homology.FixedTensorLocalization.FixedTensorLocalizationComparison
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleMixedProjectionMate

/-! # Normalized signed projection formula on chosen resolutions

Source: main-20261015 blueprint, proper base change, perfect projection formula,
proof paragraphs 2 and 3; Stacks Tag 0B56, equation-projection-formula-map
(blueprint: lem-weil-pbc-signed-projection-resolution-normalization).

The source and target comparisons are the specified mixed tensor comparisons,
with arbitrary derived isomorphisms to the chosen representatives. All operations
are on the original small pro-etale sites and ordinary uncompleted derived categories.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace AlgebraicGeometry.Scheme.SignedProjectionResolution

variable {X Y : Scheme.{u}} (f : X ⟶ Y)
  (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
  (S : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
  (c : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R ≅ S)

/-- The coefficient complex pulled back termwise by the exact module pullback.
Source: blueprint, perfect projection formula, paragraph 2
(blueprint: lem-weil-pbc-signed-projection-resolution-normalization). -/
abbrev pulledCoefficient (F : CochainComplex (proEtaleRingModules Y R) ℤ) :=
  ((proEtaleRingModulePullback f R S c).mapHomologicalComplex (.up ℤ)).obj F

/-- The signed total complex C = Tot(f_* I tensor F); its second differential
has sign (-1)^a on bidegree (a,r).
Source: blueprint, perfect projection formula, paragraph 2
(blueprint: lem-weil-pbc-signed-projection-resolution-normalization). -/
abbrev sourceComplex (I : CochainComplex (proEtaleRingModules X S) ℤ)
    (F : CochainComplex (proEtaleRingModules Y R) ℤ) :=
  CochainComplex.mapBifunctor
    (((proEtaleRingModuleDirectImage f R S c).mapHomologicalComplex (.up ℤ)).obj I)
    F (proEtaleOrdinaryTensor Y R)

/-- The signed total complex J = Tot(I tensor f^* F), with the same sign convention.
Source: blueprint, perfect projection formula, paragraph 2
(blueprint: lem-weil-pbc-signed-projection-resolution-normalization). -/
abbrev targetComplex (I : CochainComplex (proEtaleRingModules X S) ℤ)
    (F : CochainComplex (proEtaleRingModules Y R) ℤ) :=
  CochainComplex.mapBifunctor I (pulledCoefficient f R S c F) (proEtaleOrdinaryTensor X S)

/-- The ordinary direct image B = f_* J, taken termwise.
Source: blueprint, perfect projection formula, paragraph 2
(blueprint: lem-weil-pbc-signed-projection-resolution-normalization). -/
abbrev pushTargetComplex (I : CochainComplex (proEtaleRingModules X S) ℤ)
    (F : CochainComplex (proEtaleRingModules Y R) ℤ) :=
  ((proEtaleRingModuleDirectImage f R S c).mapHomologicalComplex (.up ℤ)).obj
    (targetComplex f R S c I F)

variable (a : ProEtaleTensorModel Y R) (b : ProEtaleTensorModel X S)
  (K : DerivedCategory (proEtaleRingModules X S))
  (P : DerivedCategory (proEtaleRingModules Y R))
  (I : CochainComplex (proEtaleRingModules X S) ℤ) (hI : I.IsKInjective)
  (alpha : K ≅ DerivedCategory.Q.obj I)
  (F : CochainComplex (proEtaleRingModules Y R) ℤ)
  (beta : DerivedCategory.Q.obj F ≅ P)
  (package : SheafOfModules.StrictPerfectCoefficientPackageOnSite
    ((sheafCompose (ProEt.topology Y)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R) F)
  (bounded : ∃ l h : ℤ, ∀ r : ℤ, r < l ∨ h < r → IsZero (F.X r))

/-- The ordinary signed total counit mate t, using the published total construction.
Source: blueprint, perfect projection formula, paragraph 2
(blueprint: lem-weil-pbc-signed-projection-resolution-normalization). -/
def totalMate : sourceComplex f R S c I F ⟶ pushTargetComplex f R S c I F := by
  letI := SheafOfModules.monoidalCategory R
  letI := SheafOfModules.monoidalCategory S
  exact CategoryTheory.tensorAdjunctionTotal
    (proEtaleRingModulePullback f R S c) (proEtaleRingModuleDirectImage f R S c)
    (proEtaleRingModuleAdjunction f R S c) (proEtaleOrdinaryTensorPullback f R S c)
    (fun {_ _ _ _} v z ↦ proEtaleOrdinaryTensorPullback_naturality f R S c _ _ _ _ v z) I F

private theorem transport_projection
    {C : Type*} [Category C] {D : Type*} [Category D]
    (L : C ⥤ D) (V : D ⥤ C) (T : C × C ⥤ C) (U : D × D ⥤ D)
    (pi : ∀ (K : D) (Q : C), T.obj (V.obj K, Q) ⟶ V.obj (U.obj (K, L.obj Q)))
    (hn₁ : ∀ {K I : D} (k : K ⟶ I) (Q : C),
      pi K Q ≫ V.map (U.map (Prod.mkHom k (𝟙 _))) =
        T.map (Prod.mkHom (V.map k) (𝟙 Q)) ≫ pi I Q)
    (hn₂ : ∀ (K : D) {P Q : C} (q : P ⟶ Q),
      T.map (Prod.mkHom (𝟙 _) q) ≫ pi K Q =
        pi K P ≫ V.map (U.map (Prod.mkHom (𝟙 K) (L.map q))))
    {K I : D} {A F Q M B : C} (k : K ≅ I) (q : F ≅ Q) (s : A ≅ V.obj I)
    (t : V.obj (U.obj (I, L.obj F)) ⟶ B) (m : T.obj (A, F) ⟶ M) (z : M ⟶ B)
    (h : T.map (Prod.mkHom s.hom (𝟙 F)) ≫ pi I F ≫ t = m ≫ z) :
    pi K Q ≫ V.map (U.map (Prod.mkHom k.hom (L.map q.inv))) ≫ t =
      T.map (Prod.mkHom (V.map k.hom ≫ s.inv) q.inv) ≫ m ≫ z := by
  have hs := congrArg (fun v ↦ T.map (Prod.mkHom s.inv (𝟙 F)) ≫ v) h
  simp only [← Category.assoc, ← T.map_comp, prod_comp, Iso.inv_hom_id,
    Category.id_comp] at hs
  change (T.map (𝟙 (V.obj I, F)) ≫ pi I F) ≫ t = _ at hs
  rw [T.map_id, Category.id_comp, Category.assoc] at hs
  calc
    _ = T.map (Prod.mkHom (𝟙 _) q.inv) ≫ pi K F ≫
        V.map (U.map (Prod.mkHom k.hom (𝟙 _))) ≫ t := by
      rw [← Category.assoc (T.map _) (pi K F), hn₂ K q.inv, Category.assoc]
      simp only [← Category.assoc, ← V.map_comp, ← U.map_comp, prod_comp,
        Category.comp_id, Category.id_comp]
    _ = T.map (Prod.mkHom (V.map k.hom) q.inv) ≫ pi I F ≫ t := by
      rw [← Category.assoc (pi K F), hn₁ k.hom F, ← Category.assoc,
        ← Category.assoc, ← T.map_comp, Category.assoc]
      simp only [prod_comp, Category.comp_id, Category.id_comp]
    _ = _ := by
      have hh := congrArg (fun v ↦ T.map (Prod.mkHom (V.map k.hom) q.inv) ≫ v) hs
      simpa only [← Category.assoc, ← T.map_comp, prod_comp, Category.comp_id] using hh

end AlgebraicGeometry.Scheme.SignedProjectionResolution
