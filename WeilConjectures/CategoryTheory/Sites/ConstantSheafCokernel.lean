/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
public import Mathlib.RingTheory.Finiteness.Cardinality

/-!
# Cokernels of scalar matrices between constant sheaves of modules

Let `R` be a commutative ring and `(C, J)` a site with a terminal object. For a sheaf `F` of
`R`-modules and `r ∈ R`, write `r • 𝟙 : F ⟶ F` for the multiplication by `r`
(`CategoryTheory.Sheaf.scalarEnd`). If `F` is isomorphic to the constant sheaf `R`, the cokernel
of a matrix `F^m ⟶ F^n` of such scalars is the constant sheaf of the cokernel of the
corresponding matrix of scalars `R^m ⟶ R^n`
(`CategoryTheory.Sheaf.exists_iso_constantSheaf_cokernel_matrix_scalarEnd`): the constant sheaf
functor is additive, preserves cokernels, being a left adjoint, and commutes with the
multiplication by scalars (`CategoryTheory.Sheaf.constantSheaf_map_smul_id`).

We also record how an additive functor acts on matrices between finite biproducts
(`CategoryTheory.Functor.map_biproduct_matrix_conj`).
-/

@[expose] public section

universe w v u

open CategoryTheory Limits Opposite

namespace CategoryTheory.Functor

variable {C D : Type*} [Category* C] [Category* D] [Preadditive C] [Preadditive D]
  [HasFiniteBiproducts C] [HasFiniteBiproducts D] (G : C ⥤ D) [G.Additive]

/-- The isomorphism `G(⨁_J A) ≅ ⨁_J A'` induced by an isomorphism `G A ≅ A'`, for an additive
functor `G`. -/
noncomputable def mapBiproductConstIso {A : C} {A' : D} (a : G.obj A ≅ A') (ι : Type)
    [Finite ι] : G.obj (⨁ fun _ : ι ↦ A) ≅ ⨁ fun _ : ι ↦ A' :=
  G.mapBiproduct _ ≪≫ biproduct.mapIso fun _ ↦ a

/-- **An additive functor acts on matrices entrywise**: conjugated by `G(⨁ A) ≅ ⨁ A'`, the image
of a matrix `⨁_ι A ⟶ ⨁_κ A` is the matrix of the conjugated images of its entries. -/
lemma map_biproduct_matrix_conj {A : C} {A' : D} (a : G.obj A ≅ A') {ι κ : Type} [Finite ι]
    [Finite κ] (m : ι → κ → (A ⟶ A)) :
    (G.mapBiproductConstIso a ι).inv ≫ G.map (biproduct.matrix m) ≫
        (G.mapBiproductConstIso a κ).hom =
      biproduct.matrix fun i k ↦ a.inv ≫ G.map (m i k) ≫ a.hom := by
  have := Fintype.ofFinite ι
  have := Fintype.ofFinite κ
  refine biproduct.hom_ext' _ _ fun i ↦ biproduct.hom_ext _ _ fun k ↦ ?_
  simp [mapBiproductConstIso, ← G.map_comp_assoc]

end CategoryTheory.Functor

namespace CategoryTheory.Sheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Type w} [CommRing R]

/-- The multiplication by a scalar `r` on a sheaf of `R`-modules. -/
def scalarEnd (r : R) (F : Sheaf J (ModuleCat.{w} R)) : F ⟶ F :=
  ObjectProperty.homMk
    { app U := ModuleCat.ofHom (r • LinearMap.id)
      naturality U V f := by
        ext x
        simp }

@[simp]
lemma scalarEnd_hom_app_apply (r : R) (F : Sheaf J (ModuleCat.{w} R)) (U : Cᵒᵖ)
    (x : F.obj.obj U) : (scalarEnd r F).hom.app U x = r • x :=
  rfl

/-- The multiplication by a scalar commutes with every morphism of sheaves of modules. -/
@[reassoc]
lemma scalarEnd_comp (r : R) {F G : Sheaf J (ModuleCat.{w} R)} (f : F ⟶ G) :
    scalarEnd r F ≫ f = f ≫ scalarEnd r G := by
  ext U x
  simp

variable (J) [HasWeakSheafify J (ModuleCat.{w} R)] {T : C} (hT : IsTerminal T)

include hT in
/-- **The constant sheaf functor commutes with scalars**: it sends the multiplication by `r` on
an `R`-module to the multiplication by `r` on the constant sheaf. -/
lemma constantSheaf_map_smul_id (r : R) (M : ModuleCat.{w} R) :
    (constantSheaf J (ModuleCat.{w} R)).map (r • 𝟙 M) =
      scalarEnd r ((constantSheaf J (ModuleCat.{w} R)).obj M) := by
  let adj := constantSheafAdj J (ModuleCat.{w} R) hT
  refine (adj.homEquiv _ _).injective ?_
  rw [adj.homEquiv_unit, adj.homEquiv_unit, ← Functor.comp_map, ← adj.unit.naturality]
  ext x
  simp

variable [HasFiniteBiproducts (Sheaf J (ModuleCat.{w} R))]
  [HasCokernels (Sheaf J (ModuleCat.{w} R))]

include hT in
/-- **The cokernel of a matrix of scalars between copies of the constant sheaf `R`** is the
constant sheaf of the cokernel of the matrix of scalars `R^ι ⟶ R^κ`, a finite `R`-module when
`R` is finite. -/
lemma exists_iso_constantSheaf_cokernel_matrix_scalarEnd [Finite R]
    {F : Sheaf J (ModuleCat.{w} R)}
    (e : F ≅ (constantSheaf J (ModuleCat.{w} R)).obj (ModuleCat.of R R)) {ι κ : Type} [Finite ι]
    [Finite κ] (c : ι → κ → R) :
    ∃ N : ModuleCat.{w} R, Finite N ∧
      Nonempty (cokernel (biproduct.matrix fun i k ↦ scalarEnd (c i k) F) ≅
        (constantSheaf J (ModuleCat.{w} R)).obj N) := by
  have := Fintype.ofFinite ι
  have := Fintype.ofFinite κ
  let L := constantSheaf J (ModuleCat.{w} R)
  let adj := constantSheafAdj J (ModuleCat.{w} R) hT
  have := adj.isLeftAdjoint
  have := preservesBinaryBiproducts_of_preservesBinaryCoproducts L
  have : L.Additive := Functor.additive_of_preservesBinaryBiproducts L
  let m : (⨁ fun _ : ι ↦ ModuleCat.of R R) ⟶ ⨁ fun _ : κ ↦ ModuleCat.of R R :=
    biproduct.matrix fun i k ↦ c i k • 𝟙 _
  refine ⟨cokernel m, ?_, ⟨?_⟩⟩
  · have hs := (ModuleCat.epi_iff_surjective (cokernel.π m)).1 inferInstance
    have : Finite (ToType (⨁ fun _ : κ ↦ ModuleCat.of R R : ModuleCat.{w} R)) :=
      Finite.of_equiv _
        (ModuleCat.biproductIsoPi fun _ : κ ↦ ModuleCat.of R R).toLinearEquiv.symm.toEquiv
    exact Finite.of_surjective _ hs
  · have hw : L.map m ≫ (L.mapBiproductConstIso (Iso.refl _) κ).hom =
        (L.mapBiproductConstIso (Iso.refl _) ι).hom ≫
          biproduct.matrix fun i k ↦ scalarEnd (c i k) (L.obj (ModuleCat.of R R)) := by
      rw [← Iso.inv_comp_eq, L.map_biproduct_matrix_conj]
      simp [L, constantSheaf_map_smul_id J hT]
    refine cokernel.mapIso _ _ (biproduct.mapIso fun _ ↦ e) (biproduct.mapIso fun _ ↦ e) ?_ ≪≫
      (cokernel.mapIso _ _ (L.mapBiproductConstIso (Iso.refl _) ι)
        (L.mapBiproductConstIso (Iso.refl _) κ) hw).symm ≪≫ (PreservesCokernel.iso L m).symm
    simp [biproduct.matrix_map, biproduct.map_matrix, scalarEnd_comp]
    rfl

/-- The sections over a terminal object of a sheaf of `R`-modules, as a functor to types. -/
abbrev sectionsTypeFunctor : Sheaf J (ModuleCat.{w} R) ⥤ Type w :=
  (sheafSections J (ModuleCat.{w} R)).obj (op T) ⋙ forget (ModuleCat.{w} R)

/-- **The constant sheaf `R` corepresents the sections over a terminal object**: a morphism out
of it is determined by the image of `1`. -/
noncomputable def constantSheafCorepresentableBy :
    (sectionsTypeFunctor J (T := T)).CorepresentableBy
      ((constantSheaf J (ModuleCat.{w} R)).obj (ModuleCat.of R R)) where
  homEquiv {G} := ((constantSheafAdj J (ModuleCat.{w} R) hT).homEquiv _ G).trans
    { toFun f := f.hom 1
      invFun x := ModuleCat.ofHom (LinearMap.toSpanSingleton R _ x)
      left_inv f := by
        ext
        simp
      right_inv x := by simp }
  homEquiv_comp g f := by
    dsimp only [Equiv.trans_apply, Equiv.coe_fn_mk]
    rw [Adjunction.homEquiv_naturality_right]
    rfl

end CategoryTheory.Sheaf
