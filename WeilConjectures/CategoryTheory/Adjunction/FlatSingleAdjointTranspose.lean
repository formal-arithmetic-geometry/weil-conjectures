/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.ExactRightDerivedAdjointKFlatRepresentative
/-! # Flat single complexes and adjoint transposes
Source: finite-reduction blueprint, bounded flat representatives in Step 2.
(blueprint: lem-pur-flat-single-adjoint-transpose).
-/
@[expose] public noncomputable section
set_option autoImplicit false
universe uV vV wV uW vW wW
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian MonoidalCategory
namespace CategoryTheory
variable {V : Type uV} {W : Type uW} [Category.{vV} V] [Category.{vW} W]
  [Abelian V] [Abelian W] (E : V ⥤ W) (U : W ⥤ V) [E.Additive] [U.Additive]
variable [HasDerivedCategory.{wV} V] [HasDerivedCategory.{wW} W]
  [PreservesFiniteLimits U] [PreservesFiniteColimits U]

variable [IsGrothendieckAbelian.{vV} V]
  [MonoidalCategory V] [MonoidalPreadditive V] [MonoidalClosed V] [BraidedCategory V]
  [HasFunctorialFlatResolution V] [E.PreservesKFlatQuasiIso]

/-- An invertible ordinary adjunct with flat source gives an invertible derived adjunct.
Source: thm-pur-finite-reduction-of-purity.proof.md, Step 2, flat models.
(blueprint: lem-pur-flat-single-adjoint-transpose).
Proof: the flat source single complex is K-flat. The derived adjunct of the
cochain unit is therefore invertible. Its composite with the single-complex
comparison for E is the adjunct of the ordinary unit. Naturality of the exact
single comparison for U then identifies the displayed arrow with this
isomorphism followed by the single of the ordinary adjunct. Both factors are
invertible. Only flatness of the source is used; no exactness of E is required. -/
theorem Adjunction.isIso_single_transpose {L : DerivedCategory V ⥤ DerivedCategory W}
    (a : E ⊣ U) (b : L ⊣ U.mapDerivedCategory) (F : V) (G : W)
    (η : F ⟶ U.obj G) (hF : ObjectProperty.flat F)
    [IsIso ((a.homEquiv _ _).symm η)] :
    IsIso ((b.homEquiv _ _).symm
      ((DerivedCategory.singleFunctor V 0).map η ≫
        (U.mapDerivedCategorySingleFunctor 0).inv.app G)) := by
  let X := (HomologicalComplex.single V (.up ℤ) 0).obj F
  let c := DerivedCategory.Q.mapIso
    ((HomologicalComplex.singleMapHomologicalComplex E (.up ℤ) 0).app F)
  let δ := DerivedCategory.Q.map ((a.mapHomologicalComplex (.up ℤ)).unit.app X) ≫
    U.mapDerivedCategoryFactors.inv.app ((E.mapHomologicalComplex (.up ℤ)).obj X)
  have hδ : IsIso ((b.homEquiv _ _).symm δ) :=
    Adjunction.isIso_cochainTranspose_of_kFlat E U a b X
      ((CochainComplex.kFlat_single_obj_iff_flat F 0).2 hF)
  let t : L.obj ((DerivedCategory.singleFunctor V 0).obj F) ⟶
      (DerivedCategory.singleFunctor W 0).obj (E.obj F) := (b.homEquiv _ _).symm
    ((DerivedCategory.singleFunctor V 0).map (a.unit.app F) ≫
      (U.mapDerivedCategorySingleFunctor 0).inv.app (E.obj F))
  have ht : t = (b.homEquiv _ _).symm δ ≫ c.hom := by
    rw [← Adjunction.homEquiv_naturality_right_symm]
    apply congrArg (b.homEquiv _ _).symm
    simpa only [δ, c, X, Functor.mapIso_hom, Iso.app_hom, Category.assoc] using
      (derived_single_unit_square E U a F).symm
  have : IsIso t := by rw [ht]; infer_instance
  let q := (a.homEquiv _ _).symm η
  have hηq : a.unit.app F ≫ U.map q = η := by
    calc
      _ = a.homEquiv F G q := (a.homEquiv_unit F G q).symm
      _ = η := (a.homEquiv F G).apply_symm_apply η
  have hraw : (DerivedCategory.singleFunctor V 0).map η ≫
      (U.mapDerivedCategorySingleFunctor 0).inv.app G =
    ((DerivedCategory.singleFunctor V 0).map (a.unit.app F) ≫
      (U.mapDerivedCategorySingleFunctor 0).inv.app (E.obj F)) ≫
      U.mapDerivedCategory.map ((DerivedCategory.singleFunctor W 0).map q) := by
    rw [← hηq, Functor.map_comp]
    simpa only [Functor.comp_map, Category.assoc] using congrArg
      ((DerivedCategory.singleFunctor V 0).map (a.unit.app F) ≫ ·)
      ((U.mapDerivedCategorySingleFunctor 0).inv.naturality q)
  rw [hraw, Adjunction.homEquiv_naturality_right_symm]
  change IsIso (t ≫ (DerivedCategory.singleFunctor W 0).map q)
  infer_instance
end CategoryTheory
