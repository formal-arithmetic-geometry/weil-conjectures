/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalarsCompLevelwise
public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalarsTriangleNatural

/-!

# Transition maps between natural reduction triangles

Let `φ : R ⟶ S`, `ψ : S ⟶ T` and `χ : R ⟶ T` be morphisms of commutative algebra objects with
`φ ≫ ψ = χ`. Write `T_φ = L(Ext_φ) ⋙ D(Res_φ)` for the monad of the derived adjunction
`L(Ext_φ) ⊣ D(Res_φ)`. This file constructs the canonical *transition*
`T_φ ⟶ T_χ` (`Mod.derivedExtendComapTransition`), sending `S ⊗ᴸ_R K` to `T ⊗ᴸ_R K`: it is
`D(Res_φ)` applied to the unit `S ⊗ᴸ_R K ⟶ D(Res_ψ) (T ⊗ᴸ_S (S ⊗ᴸ_R K)) ≅ D(Res_ψ) (T ⊗ᴸ_R K)`.
It is compatible with the units (`Mod.unit_app_comp_derivedExtendComapTransition_app`).

If moreover `0 ⟶ R --k--> R --φ--> S ⟶ 0` and `0 ⟶ R --k'--> R --χ--> T ⟶ 0` are short exact
with `k = m * k'`, then the triple `(m, 𝟙, transition)` is a morphism between the natural
reduction triangles `K --k--> K ⟶ T_φ K ⟶ K[1]` and `K --k'--> K ⟶ T_χ K ⟶ K[1]`
(`Mod.derivedExtendScalarsTriangleδ_comp_shift_map_zsmul`). On a complex of flat objects this is
the naturality of the connecting morphisms of short exact sequences of complexes, applied to the
levelwise transition `S ⊗_R P ⟶ T ⊗_R P` (`Mod.extendComapTransition`), which computes the
derived transition (`Mod.derivedExtendComapComparisonh_comp_map_extendComapComplexTransition`).

-/

@[expose] public section

universe v u

open CategoryTheory MonoidalCategory MonObj Limits Pretriangulated

namespace CategoryTheory.Mod

variable {C : Type u} [Category.{v} C] [Abelian C] [MonoidalCategory C] [MonoidalPreadditive C]
  [SymmetricCategory C] [MonoidalClosed C] [IsGrothendieckAbelian.{v} C]
  [Abelian.HasFunctorialFlatResolution C]
  {R S T : C} [MonObj R] [MonObj S] [MonObj T] [IsCommMonObj R] [IsCommMonObj S]
  [IsCommMonObj T] (φ : R ⟶ S) [IsMonHom φ] (ψ : S ⟶ T) [IsMonHom ψ] (χ : R ⟶ T) [IsMonHom χ]

/-! ### The levelwise transition -/

/-- The `S`-linear transition `S ⊗_R M ⟶ T ⊗_R M` (with `T ⊗_R M` regarded as an `S`-module) for
`φ ≫ ψ = χ`: the unit of `Ext_ψ ⊣ Res_ψ` followed by the transitivity isomorphism. -/
noncomputable def extendScalarsToComap (h : φ ≫ ψ = χ) :
    extendScalars φ ⟶ extendScalars χ ⋙ comap ψ :=
  Functor.whiskerLeft (extendScalars φ) (extendRestrictAdjunction ψ).unit ≫
    Functor.whiskerRight ((extendScalarsComp φ ψ).symm ≪≫ extendScalarsIsoOfEq h).hom (comap ψ)

/-- The transition `S ⊗_R M ⟶ T ⊗_R M` of `R`-modules, for `φ ≫ ψ = χ`. -/
noncomputable def extendComapTransition (h : φ ≫ ψ = χ) :
    extendScalars φ ⋙ comap φ ⟶ extendScalars χ ⋙ comap χ :=
  Functor.whiskerRight (extendScalarsToComap φ ψ χ h) (comap φ) ≫
    Functor.whiskerLeft (extendScalars χ) ((comapComp φ ψ).symm ≪≫ comapCongr h).hom

omit [MonoidalPreadditive C] [Abelian.HasFunctorialFlatResolution C] [IsCommMonObj T] in
/-- The levelwise transition is compatible with the units. -/
@[reassoc (attr := simp)]
lemma extendRestrictAdjunction_unit_app_comp_extendComapTransition_app (h : φ ≫ ψ = χ)
    (M : Mod C R) :
    (extendRestrictAdjunction φ).unit.app M ≫ (extendComapTransition φ ψ χ h).app M =
      (extendRestrictAdjunction χ).unit.app M := by
  have hL := extendRestrictAdjunction_unit_app_comp_map_extendScalarsComp φ ψ χ h M
  have hn := ((comapComp φ ψ).symm ≪≫ comapCongr h).hom.naturality
    (((extendScalarsComp φ ψ).symm ≪≫ extendScalarsIsoOfEq h).hom.app M)
  simp only [Functor.comp_map, Functor.comp_obj] at hn
  simp only [extendComapTransition, extendScalarsToComap, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.map_comp, Category.assoc]
  rw [hn, ← reassoc_of% hL, ← Functor.map_comp, Iso.inv_hom_id_app, Functor.map_id,
    Category.comp_id]

/-- The levelwise transition `S ⊗_R P ⟶ T ⊗_R P` on complexes of `R`-modules. -/
noncomputable abbrev extendComapComplexTransition (h : φ ≫ ψ = χ) :
    extendComapComplexFunctor φ ⟶ extendComapComplexFunctor χ :=
  NatTrans.mapHomologicalComplex (extendComapTransition φ ψ χ h) (ComplexShape.up ℤ)

omit [Abelian.HasFunctorialFlatResolution C] [IsCommMonObj T] in
/-- The levelwise transition on complexes is compatible with the units. -/
@[reassoc (attr := simp)]
lemma extendUnitComplexHom_comp_extendComapComplexTransition_app (h : φ ≫ ψ = χ)
    (P : CochainComplex (Mod C R) ℤ) :
    extendUnitComplexHom φ P ≫ (extendComapComplexTransition φ ψ χ h).app P =
      extendUnitComplexHom χ P := by
  ext i : 1
  rw [HomologicalComplex.comp_f, extendUnitComplexHom_f, extendUnitComplexHom_f,
    NatTrans.mapHomologicalComplex_app_f, ← extendRestrictAdjunction_unit_app,
    ← extendRestrictAdjunction_unit_app]
  exact extendRestrictAdjunction_unit_app_comp_extendComapTransition_app φ ψ χ h (P.X i)

/-! ### The derived transition -/

/-- The derived `S`-linear transition `S ⊗ᴸ_R K ⟶ T ⊗ᴸ_R K`, for `φ ≫ ψ = χ`. -/
noncomputable def derivedExtendScalarsToComap (h : φ ≫ ψ = χ) :
    (extendScalars φ).leftDerivedFunctor ⟶
      (extendScalars χ).leftDerivedFunctor ⋙ (comap ψ).mapDerivedCategory :=
  Functor.whiskerLeft (extendScalars φ).leftDerivedFunctor
      (derivedExtendMapDerivedCategoryAdjunction ψ).unit ≫
    Functor.whiskerRight (derivedExtendScalarsCompIso φ ψ χ h).inv (comap ψ).mapDerivedCategory

/-- **The transition between the reductions** `S ⊗ᴸ_R K ⟶ T ⊗ᴸ_R K` of `R`-modules, for
`φ ≫ ψ = χ`: `D(Res_φ)` of the derived `S`-linear transition. -/
noncomputable def derivedExtendComapTransition (h : φ ≫ ψ = χ) :
    (extendScalars φ).leftDerivedFunctor ⋙ (comap φ).mapDerivedCategory ⟶
      (extendScalars χ).leftDerivedFunctor ⋙ (comap χ).mapDerivedCategory :=
  Functor.whiskerRight (derivedExtendScalarsToComap φ ψ χ h) (comap φ).mapDerivedCategory ≫
    Functor.whiskerLeft (extendScalars χ).leftDerivedFunctor
      (mapDerivedCategoryComapCompIso φ ψ χ h).hom

/-- The transition between the reductions is compatible with the units. -/
@[reassoc (attr := simp)]
lemma unit_app_comp_derivedExtendComapTransition_app (h : φ ≫ ψ = χ)
    (K : DerivedCategory (Mod C R)) :
    (derivedExtendMapDerivedCategoryAdjunction φ).unit.app K ≫
        (derivedExtendComapTransition φ ψ χ h).app K =
      (derivedExtendMapDerivedCategoryAdjunction χ).unit.app K := by
  have hc := unit_conjugateEquiv_symm ((derivedExtendMapDerivedCategoryAdjunction φ).comp
    (derivedExtendMapDerivedCategoryAdjunction ψ)) (derivedExtendMapDerivedCategoryAdjunction χ)
    (mapDerivedCategoryComapCompIso φ ψ χ h).hom K
  have he : ((conjugateEquiv ((derivedExtendMapDerivedCategoryAdjunction φ).comp
      (derivedExtendMapDerivedCategoryAdjunction ψ))
      (derivedExtendMapDerivedCategoryAdjunction χ)).symm
        (mapDerivedCategoryComapCompIso φ ψ χ h).hom) =
      (derivedExtendScalarsCompIso φ ψ χ h).hom := rfl
  have hn := (mapDerivedCategoryComapCompIso φ ψ χ h).hom.naturality
    ((derivedExtendScalarsCompIso φ ψ χ h).inv.app K)
  simp only [Functor.comp_map, Functor.comp_obj] at hn
  rw [Adjunction.comp_unit_app, he, Category.assoc] at hc
  simp only [Functor.comp_obj] at hc
  simp only [derivedExtendComapTransition, derivedExtendScalarsToComap, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.map_comp, Category.assoc]
  rw [hn, reassoc_of% hc, ← Functor.map_comp, Iso.hom_inv_id_app, Functor.map_id,
    Category.comp_id]

/-- On a complex `P`, the derived transition is computed by the levelwise transition. -/
@[reassoc]
lemma derivedExtendComapComparisonh_comp_map_extendComapComplexTransition (h : φ ≫ ψ = χ)
    (P : CochainComplex (Mod C R) ℤ) :
    derivedExtendComapComparisonh φ P ≫ DerivedCategory.Qh.map
        ((HomotopyCategory.quotient _ _).map ((extendComapComplexTransition φ ψ χ h).app P)) =
      (derivedExtendComapTransition φ ψ χ h).app
          (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj P)) ≫
        derivedExtendComapComparisonh χ P := by
  let X := (HomotopyCategory.quotient (Mod C R) (ComplexShape.up ℤ)).obj P
  let Y := ((extendScalars χ).mapHomotopyCategory (ComplexShape.up ℤ)).obj X
  let e := (HomotopyCategory.quotient _ _).mapIso ((NatIso.mapHomologicalComplex
    (Functor.isoWhiskerLeft (extendScalars χ) ((comapComp φ ψ).symm ≪≫ comapCongr h))
    (ComplexShape.up ℤ)).app P)
  let θ := (comap φ).mapDerivedCategoryFactorsh.hom.app
      (((comap ψ).mapHomotopyCategory (ComplexShape.up ℤ)).obj Y) ≫ DerivedCategory.Qh.map e.hom
  let q := (HomotopyCategory.quotient _ _).map
    ((NatTrans.mapHomologicalComplex (extendScalarsToComap φ ψ χ h) (ComplexShape.up ℤ)).app P)
  let u₁ := (extendScalars φ).leftDerivedFunctorCounit.app X ≫ DerivedCategory.Qh.map q
  let u₂ := (derivedExtendScalarsToComap φ ψ χ h).app (DerivedCategory.Qh.obj X) ≫
    (comap ψ).mapDerivedCategory.map ((extendScalars χ).leftDerivedFunctorCounit.app X) ≫
    (comap ψ).mapDerivedCategoryFactorsh.hom.app Y
  have hlev : (HomotopyCategory.quotient _ _).map ((extendComapComplexTransition φ ψ χ h).app P) =
      ((comap φ).mapHomotopyCategory (ComplexShape.up ℤ)).map q ≫ e.hom := rfl
  have hA : derivedExtendComapComparisonh φ P ≫ DerivedCategory.Qh.map
        ((HomotopyCategory.quotient _ _).map ((extendComapComplexTransition φ ψ χ h).app P)) =
      (comap φ).mapDerivedCategory.map u₁ ≫ θ := by
    have hfac : (comap φ).mapDerivedCategory.map (DerivedCategory.Qh.map q) ≫
        (comap φ).mapDerivedCategoryFactorsh.hom.app
          (((comap ψ).mapHomotopyCategory (ComplexShape.up ℤ)).obj Y) =
        (comap φ).mapDerivedCategoryFactorsh.hom.app
          (((extendScalars φ).mapHomotopyCategory (ComplexShape.up ℤ)).obj X) ≫
        DerivedCategory.Qh.map (((comap φ).mapHomotopyCategory (ComplexShape.up ℤ)).map q) :=
      (comap φ).mapDerivedCategoryFactorsh.hom.naturality q
    simp only [derivedExtendComapComparisonh, hlev, u₁, θ, Functor.map_comp, Category.assoc]
    rw [reassoc_of% hfac]
  have hB : (derivedExtendComapTransition φ ψ χ h).app (DerivedCategory.Qh.obj X) ≫
        derivedExtendComapComparisonh χ P = (comap φ).mapDerivedCategory.map u₂ ≫ θ := by
    have hn := (mapDerivedCategoryComapCompIso φ ψ χ h).hom.naturality
      ((extendScalars χ).leftDerivedFunctorCounit.app X)
    simp only [Functor.comp_map] at hn
    have hfac := mapDerivedCategoryComapCompIso_hom_app_Qh_obj_comp_factorsh φ ψ χ h Y
    have he : (Functor.mapHomotopyCategoryCompIso (Iso.refl (comap ψ ⋙ comap φ))
        (ComplexShape.up ℤ)).hom.app Y ≫ (NatTrans.mapHomotopyCategory
          ((comapComp φ ψ).symm ≪≫ comapCongr h).hom (ComplexShape.up ℤ)).app Y = e.hom := by
      have h₁ : (Functor.mapHomotopyCategoryCompIso (Iso.refl (comap ψ ⋙ comap φ))
          (ComplexShape.up ℤ)).hom.app Y = 𝟙 _ := rfl
      rw [h₁, Category.id_comp]
      rfl
    rw [he] at hfac
    simp only [derivedExtendComapTransition, derivedExtendComapComparisonh, u₂, θ,
      NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.map_comp,
      Category.assoc]
    rw [← reassoc_of% hn, hfac]
  have hη₁ : (derivedExtendMapDerivedCategoryAdjunction φ).unit.app (DerivedCategory.Qh.obj X) ≫
      derivedExtendComapComparisonh φ P ≫ DerivedCategory.Qh.map
        ((HomotopyCategory.quotient _ _).map ((extendComapComplexTransition φ ψ χ h).app P)) =
      DerivedCategory.Qh.map ((HomotopyCategory.quotient _ _).map (extendUnitComplexHom χ P)) := by
    rw [derivedExtendComapComparisonh, Category.assoc,
      reassoc_of% (derivedExtendMapDerivedCategoryAdjunction_unit_app_fac φ X),
      Adjunction.mapHomotopyCategory_unit_app_quotient, ← extendUnitComplexHom_eq,
      ← Functor.map_comp, ← Functor.map_comp]
    exact congrArg (fun f ↦ DerivedCategory.Qh.map ((HomotopyCategory.quotient _ _).map f))
      (extendUnitComplexHom_comp_extendComapComplexTransition_app φ ψ χ h P)
  have hη₂ : (derivedExtendMapDerivedCategoryAdjunction φ).unit.app (DerivedCategory.Qh.obj X) ≫
      (derivedExtendComapTransition φ ψ χ h).app (DerivedCategory.Qh.obj X) ≫
        derivedExtendComapComparisonh χ P =
      DerivedCategory.Qh.map ((HomotopyCategory.quotient _ _).map (extendUnitComplexHom χ P)) := by
    rw [reassoc_of% (unit_app_comp_derivedExtendComapTransition_app φ ψ χ h
        (DerivedCategory.Qh.obj X)),
      derivedExtendComapComparisonh,
      derivedExtendMapDerivedCategoryAdjunction_unit_app_fac,
      Adjunction.mapHomotopyCategory_unit_app_quotient, ← extendUnitComplexHom_eq]
  have hu : u₁ = u₂ := by
    apply ((derivedExtendMapDerivedCategoryAdjunction φ).homEquiv _ _).injective
    rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, ← cancel_mono θ, Category.assoc,
      Category.assoc, ← hA, ← hB, hη₁, hη₂]
  rw [hA, hB, hu]

/-- On a complex `P`, the derived transition is computed by the levelwise transition. -/
@[reassoc]
lemma derivedExtendComapComparison_comp_map_extendComapComplexTransition (h : φ ≫ ψ = χ)
    (P : CochainComplex (Mod C R) ℤ) :
    derivedExtendComapComparison φ P ≫
        DerivedCategory.Q.map ((extendComapComplexTransition φ ψ χ h).app P) =
      (derivedExtendComapTransition φ ψ χ h).app (DerivedCategory.Q.obj P) ≫
        derivedExtendComapComparison χ P := by
  have hn := (derivedExtendComapTransition φ ψ χ h).naturality
    ((DerivedCategory.quotientCompQhIso (Mod C R)).inv.app P)
  simp only [Functor.comp_map] at hn
  simp only [derivedExtendComapComparison, Category.assoc]
  rw [← DerivedCategory.quotientCompQhIso_hom_naturality,
    derivedExtendComapComparisonh_comp_map_extendComapComplexTransition_assoc, reassoc_of% hn]

variable {φ χ} {k k' : ℤ} (w : (k • 𝟙 R) ≫ φ = 0) (hφ : (ShortComplex.mk _ _ w).ShortExact)
  (w' : (k' • 𝟙 R) ≫ χ = 0) (hχ : (ShortComplex.mk _ _ w').ShortExact)

/-- For `φ ≫ ψ = χ` and `k = m * k'`, the morphism `(m, 𝟙, transition)` between the reduction
sequences `P --k--> P ⟶ S ⊗_R P` and `P --k'--> P ⟶ T ⊗_R P` of a complex `P`. -/
@[simps]
noncomputable def reductionShortComplexTransition (h : φ ≫ ψ = χ) (m : ℤ) (hk : k = m * k')
    (P : CochainComplex (Mod C R) ℤ) :
    reductionShortComplex k w P ⟶ reductionShortComplex k' w' P where
  τ₁ := m • 𝟙 P
  τ₂ := 𝟙 P
  τ₃ := (extendComapComplexTransition φ ψ χ h).app P
  comm₁₂ := by
    rw [Preadditive.zsmul_comp, Category.id_comp, smul_smul, ← hk, Category.comp_id]
  comm₂₃ := by
    rw [Category.id_comp]
    exact (extendUnitComplexHom_comp_extendComapComplexTransition_app φ ψ χ h P).symm

/-- `(m • 𝟙)⟦1⟧` commutes with the shift of any morphism. -/
lemma _root_.CategoryTheory.shift_map_comp_shift_map_zsmul {D : Type*} [Category* D]
    [Preadditive D] [HasShift D ℤ] {K L : D} (f : K ⟶ L) (m : ℤ) :
    f⟦(1 : ℤ)⟧' ≫ (m • 𝟙 L)⟦(1 : ℤ)⟧' = (m • 𝟙 K)⟦(1 : ℤ)⟧' ≫ f⟦(1 : ℤ)⟧' := by
  rw [← Functor.map_comp, ← Functor.map_comp, Preadditive.comp_zsmul, Preadditive.zsmul_comp,
    Category.comp_id, Category.id_comp]

/-- The compatibility `Mod.derivedExtendScalarsTriangleδ_comp_shift_map_zsmul` on the image of a
complex: it is the naturality of the connecting morphisms of short exact sequences of complexes,
on the functorial K-flat resolution. -/
lemma derivedExtendScalarsTriangleδ_comp_shift_map_zsmul_Q_obj (h : φ ≫ ψ = χ) (m : ℤ)
    (hk : k = m * k') (K : CochainComplex (Mod C R) ℤ) :
    (derivedExtendScalarsTriangleδ k w hφ).app (DerivedCategory.Q.obj K) ≫
        (m • 𝟙 (DerivedCategory.Q.obj K))⟦(1 : ℤ)⟧' =
      (derivedExtendComapTransition φ ψ χ h).app (DerivedCategory.Q.obj K) ≫
        (derivedExtendScalarsTriangleδ k' w' hχ).app (DerivedCategory.Q.obj K) := by
  let P := (CochainComplex.flatResolutionFunctor (Mod C R)).obj K
  have hP := CochainComplex.flat_flatResolutionFunctor_obj_X K
  have hS := DerivedCategory.triangleOfSESδ_naturality
    (shortExact_extendUnitComplexHom k w hφ P hP) (shortExact_extendUnitComplexHom k' w' hχ P hP)
    (reductionShortComplexTransition ψ w w' h m hk P)
  rw [reductionShortComplexTransition_τ₁, reductionShortComplexTransition_τ₃, Functor.map_zsmul,
    CategoryTheory.Functor.map_id] at hS
  have hn := (derivedExtendComapTransition φ ψ χ h).naturality
    (inv (DerivedCategory.Q.map ((CochainComplex.flatResolutionπ _).app K)))
  simp only [Functor.comp_map] at hn
  rw [derivedExtendScalarsTriangleδ_app_Q_obj, derivedExtendScalarsTriangleδ_app_Q_obj]
  simp only [reductionδComplex, Category.assoc]
  rw [← reassoc_of% hn, ← derivedExtendComapComparison_comp_map_extendComapComplexTransition_assoc,
    ← reassoc_of% hS, shift_map_comp_shift_map_zsmul]

/-- **The transition is a morphism of reduction triangles**: for `φ ≫ ψ = χ` and `k = m * k'`,
the connecting morphisms of the natural reduction triangles `K --k--> K ⟶ T_φ K ⟶ K[1]` and
`K --k'--> K ⟶ T_χ K ⟶ K[1]` are compatible with the transition `T_φ K ⟶ T_χ K` and the
multiplication by `m` on `K`. -/
theorem derivedExtendScalarsTriangleδ_comp_shift_map_zsmul (h : φ ≫ ψ = χ) (m : ℤ)
    (hk : k = m * k') (K : DerivedCategory (Mod C R)) :
    (derivedExtendScalarsTriangleδ k w hφ).app K ≫ (m • 𝟙 K)⟦(1 : ℤ)⟧' =
      (derivedExtendComapTransition φ ψ χ h).app K ≫
        (derivedExtendScalarsTriangleδ k' w' hχ).app K := by
  let e := DerivedCategory.Q.objObjPreimageIso K
  have h₁ := (derivedExtendScalarsTriangleδ k w hφ).naturality e.hom
  have h₂ := (derivedExtendComapTransition φ ψ χ h).naturality e.hom
  have h₃ := (derivedExtendScalarsTriangleδ k' w' hχ).naturality e.hom
  simp only [Functor.comp_map] at h₁ h₂ h₃
  rw [← cancel_epi ((comap φ).mapDerivedCategory.map
    ((extendScalars φ).leftDerivedFunctor.map e.hom)), reassoc_of% h₁,
    shift_map_comp_shift_map_zsmul, reassoc_of% h₂, h₃,
    reassoc_of% (derivedExtendScalarsTriangleδ_comp_shift_map_zsmul_Q_obj ψ w hφ w' hχ h m hk
      (DerivedCategory.Q.objPreimage K))]

end CategoryTheory.Mod
