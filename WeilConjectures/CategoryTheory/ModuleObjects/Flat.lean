/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Monoidal.Closed.Braided
public import WeilConjectures.CategoryTheory.ModuleObjects.Abelian
public import WeilConjectures.CategoryTheory.ModuleObjects.Symmetric
public import WeilConjectures.CategoryTheory.Monoidal.Mod.TensorRegular
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic

/-!

# Free module objects are flat

Let `C` be a braided monoidal category with coequalizers preserved by the tensor product and
`R : C` a commutative algebra object. For an object `F` of `C`, the relative tensor product of an
`R`-module `P` with the free module `R ⊗ F` is `P ⊗ F`, with `R` acting on `P`
(`Mod.tensorRightIsoTensorRightFree`): the coequalizer of `P ⊗ R ⊗ (R ⊗ F) ⇉ P ⊗ (R ⊗ F)` is
`P ⊗ (R ⊗ F) ⟶ P ⊗ F`, `p ⊗ r ⊗ f ↦ p r ⊗ f`, split by `p ⊗ f ↦ p ⊗ 1 ⊗ f`.

Consequently, in an abelian symmetric monoidal closed category, the free module on a flat object
is flat (`Mod.flat_free`), and functorial flat resolutions of `C` induce functorial flat
resolutions of `Mod C R` by free modules: `R ⊗ P(M) ⟶ R ⊗ M ⟶ M`
(`Mod.flatLeftResolution`, `Mod.hasFunctorialFlatResolution_of_symmetric`).

-/

@[expose] public section

universe v u

open CategoryTheory MonoidalCategory MonObj Limits

namespace CategoryTheory.Mod

section FreeTensor

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [HasCoequalizers C] [∀ X : C, PreservesColimitsOfSize.{0, 0} (MonoidalCategory.tensorLeft X)]
  [∀ X : C, PreservesColimitsOfSize.{0, 0} (MonoidalCategory.tensorRight X)]
  [BraidedCategory C] {R : C} [MonObj R] [IsCommMonObj R]

variable (R) in
/-- The morphism `F ⟶ R ⊗ F`, `f ↦ 1 ⊗ f`. -/
def freeUnit (F : C) : F ⟶ R ⊗ F := (λ_ F).inv ≫ η[R] ▷ F

omit [HasCoequalizers C] [∀ X : C, PreservesColimitsOfSize.{0, 0} (MonoidalCategory.tensorLeft X)]
  [∀ X : C, PreservesColimitsOfSize.{0, 0} (MonoidalCategory.tensorRight X)] [BraidedCategory C]
  [IsCommMonObj R] in
lemma whiskerLeft_freeUnit_act (F : C) :
    R ◁ freeUnit R F ≫ ((α_ R R F).inv ≫ μ[R] ▷ F) = 𝟙 _ := by
  change R ◁ ((λ_ F).inv ≫ η[R] ▷ F) ≫ (α_ R R F).inv ≫ μ[R] ▷ F = 𝟙 _
  rw [MonoidalCategory.whiskerLeft_comp_assoc, associator_inv_naturality_middle_assoc,
    ← comp_whiskerRight, MonObj.mul_one]
  monoidal

/-- The map `P ⊗_R (R ⊗ F) ⟶ P ⊗ F`, `p ⊗ r ⊗ f ↦ p r ⊗ f`. -/
noncomputable def tensorFreeToTensorRight (P : Mod C R) (F : C) :
    (P ⊗ (free R).obj F).X ⟶ P.X ⊗ F :=
  Cofork.IsColimit.desc (isColimitTensorπ P ((free R).obj F))
    ((α_ P.X R F).inv ≫ rightAct P ▷ F) (by
      have h : rightAct P ▷ R ≫ rightAct P = (α_ P.X R R).hom ≫ P.X ◁ μ[R] ≫ rightAct P := by
        rw [whiskerLeft_mul_rightAct, Iso.hom_inv_id_assoc]
      change rightAct P ▷ (R ⊗ F) ≫ _ =
        ((α_ P.X R (R ⊗ F)).hom ≫ P.X ◁ ((α_ R R F).inv ≫ μ[R] ▷ F)) ≫ _
      rw [associator_inv_naturality_left_assoc, ← comp_whiskerRight, h]
      simp only [comp_whiskerRight, MonoidalCategory.whiskerLeft_comp, Category.assoc,
        associator_inv_naturality_middle_assoc]
      monoidal)

@[reassoc (attr := simp)]
lemma tensorObjπ_tensorFreeToTensorRight (P : Mod C R) (F : C) :
    tensorObjπ P ((free R).obj F) ≫ tensorFreeToTensorRight P F =
      (α_ P.X R F).inv ≫ rightAct P ▷ F :=
  Cofork.IsColimit.π_desc' (isColimitTensorπ P ((free R).obj F)) _ _

/-- The isomorphism `P ⊗ F ≅ P ⊗_R (R ⊗ F)` of the underlying objects. -/
noncomputable def tensorRightIsoTensorFreeX (P : Mod C R) (F : C) :
    P.X ⊗ F ≅ (P ⊗ (free R).obj F).X where
  hom := P.X ◁ freeUnit R F ≫ tensorObjπ P ((free R).obj F)
  inv := tensorFreeToTensorRight P F
  hom_inv_id := by
    have h := congrArg Mod.Hom.hom (unitRight_rightActHom P)
    change ((ρ_ P.X).inv ≫ P.X ◁ η[R]) ≫ rightAct P = 𝟙 _ at h
    rw [Category.assoc, tensorObjπ_tensorFreeToTensorRight]
    calc P.X ◁ freeUnit R F ≫ (α_ P.X R F).inv ≫ rightAct P ▷ F =
        (((ρ_ P.X).inv ≫ P.X ◁ η[R]) ≫ rightAct P) ▷ F := by unfold freeUnit; monoidal
      _ = 𝟙 _ := by rw [h, id_whiskerRight]
  inv_hom_id := by
    rw [← cancel_epi (tensorObjπ P ((free R).obj F)), tensorObjπ_tensorFreeToTensorRight_assoc,
      Category.comp_id]
    -- `p ⊗ r ⊗ f ↦ p r ⊗ 1 ⊗ f` and `p ⊗ r ⊗ f ↦ p ⊗ r 1 ⊗ f` agree in `P ⊗_R (R ⊗ F)`.
    let t : P.X ⊗ (R ⊗ F) ⟶ (P.X ⊗ R) ⊗ (R ⊗ F) :=
      (α_ P.X R F).inv ≫ (P.X ⊗ R) ◁ freeUnit R F
    have ht₁ : t ≫ rightAct P ▷ (R ⊗ F) =
        (α_ P.X R F).inv ≫ rightAct P ▷ F ≫ P.X ◁ freeUnit R F := by
      simp only [t, Category.assoc, whisker_exchange]
    have ht₂ : t ≫ (α_ P.X R (R ⊗ F)).hom ≫ P.X ◁ ((α_ R R F).inv ≫ μ[R] ▷ F) = 𝟙 _ := by
      simp only [t, Category.assoc]
      rw [associator_naturality_right_assoc, Iso.inv_hom_id_assoc,
        ← MonoidalCategory.whiskerLeft_comp, whiskerLeft_freeUnit_act,
        MonoidalCategory.whiskerLeft_id]
    have hc := tensorObjπ_condition P ((free R).obj F)
    calc (α_ P.X R F).inv ≫ rightAct P ▷ F ≫ P.X ◁ freeUnit R F ≫
          tensorObjπ P ((free R).obj F)
        = t ≫ (rightAct P ▷ (R ⊗ F) ≫ tensorObjπ P ((free R).obj F)) := by
          rw [reassoc_of% ht₁]
      _ = t ≫ (((α_ P.X R (R ⊗ F)).hom ≫ P.X ◁ ((α_ R R F).inv ≫ μ[R] ▷ F)) ≫
          tensorObjπ P ((free R).obj F)) := congrArg (t ≫ ·) hc
      _ = tensorObjπ P ((free R).obj F) := by
          rw [← Category.assoc, ← Category.assoc, Category.assoc t, ht₂, Category.id_comp]

variable (R) in
/-- **Tensoring with a free module**: `P ⊗_R (R ⊗ F) ≅ P ⊗ F`, naturally in the `R`-module `P`,
with `R` acting on `P ⊗ F` through `P`. -/
noncomputable def tensorRightIsoTensorRightFree (F : C) :
    tensorRight R F ≅ MonoidalCategory.tensorRight ((free R).obj F) :=
  NatIso.ofComponents (fun P ↦ isoMk (M := (tensorRight R F).obj P)
      (tensorRightIsoTensorFreeX P F) (by
        change ((α_ R P.X F).inv ≫ act P.X ▷ F) ≫ P.X ◁ freeUnit R F ≫
            tensorObjπ P ((free R).obj F) =
          R ◁ (P.X ◁ freeUnit R F ≫ tensorObjπ P ((free R).obj F)) ≫ act (P ⊗ _).X
        rw [MonoidalCategory.whiskerLeft_comp_assoc, whiskerLeft_tensorπ_smul,
          associator_inv_naturality_right_assoc, whisker_exchange_assoc, Category.assoc]))
    fun {P Q} f ↦ by
      refine Mod.hom_ext _ _ ?_
      change f.hom ▷ F ≫ Q.X ◁ freeUnit R F ≫ tensorObjπ Q ((free R).obj F) =
        (P.X ◁ freeUnit R F ≫ tensorObjπ P ((free R).obj F)) ≫ (f ▷ (free R).obj F).hom
      rw [Category.assoc, tensorObjπ_whiskerRight, whisker_exchange_assoc]

end FreeTensor

section Flat

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [Abelian C] [MonoidalPreadditive C]
  [SymmetricCategory C] [MonoidalClosed C] {R : C} [MonObj R] [IsCommMonObj R]

omit [MonoidalPreadditive C] [SymmetricCategory C] [IsCommMonObj R] in
/-- If `F` is flat, then `P ↦ P ⊗ F` is an exact functor on `R`-modules. -/
lemma exactFunctor_tensorRight {F : C} (hF : ObjectProperty.flat F) :
    exactFunctor _ _ (tensorRight R F) := by
  have := hF.tensorRight.preservesFiniteLimits
  have := hF.tensorRight.preservesFiniteColimits
  have : PreservesFiniteLimits (tensorRight R F ⋙ forget R) :=
    inferInstanceAs (PreservesFiniteLimits (forget R ⋙ MonoidalCategory.tensorRight F))
  have : PreservesFiniteColimits (tensorRight R F ⋙ forget R) :=
    inferInstanceAs (PreservesFiniteColimits (forget R ⋙ MonoidalCategory.tensorRight F))
  exact ⟨preservesFiniteLimits_of_reflects_of_preserves _ (forget R),
    preservesFiniteColimits_of_reflects_of_preserves _ (forget R)⟩

omit [MonoidalPreadditive C] in
/-- **Free modules on flat objects are flat.** -/
lemma flat_free {F : C} (hF : ObjectProperty.flat F) :
    ObjectProperty.flat ((free R).obj F) := by
  have h := (exactFunctor _ _).prop_of_iso (tensorRightIsoTensorRightFree R F)
    (exactFunctor_tensorRight hF)
  exact ⟨(exactFunctor _ _).prop_of_iso
    (BraidedCategory.tensorLeftIsoTensorRight ((free R).obj F)).symm h, h⟩

variable (R) in
/-- The functorial flat resolution of `R`-modules induced by a functorial flat resolution
`P(X) ⟶ X` of `C`: the free module `R ⊗ P(M)` with the epimorphism `R ⊗ P(M) ⟶ R ⊗ M ⟶ M`. -/
noncomputable def flatLeftResolution
    (Λ : Abelian.LeftResolution (ObjectProperty.flat.ι : _ ⥤ C)) :
    Abelian.LeftResolution (ObjectProperty.flat.ι : _ ⥤ Mod C R) where
  F := ObjectProperty.lift _ (forget R ⋙ Λ.F ⋙ ObjectProperty.flat.ι ⋙ free R)
    fun M ↦ flat_free (Λ.F.obj M.X).property
  π := Functor.whiskerLeft (forget R) (Functor.whiskerRight Λ.π (free R)) ≫
    (freeForgetAdjunction R).counit
  epi_π_app M := by
    have : (free R).IsLeftAdjoint := ⟨_, ⟨freeForgetAdjunction R⟩⟩
    have : Epi ((forget R).map ((freeForgetAdjunction R).counit.app M)) := by
      have := IsSplitEpi.mk' ⟨_, (freeForgetAdjunction R).right_triangle_components M⟩
      infer_instance
    have : Epi ((freeForgetAdjunction R).counit.app M) := (forget R).epi_of_epi_map this
    change Epi ((free R).map (Λ.π.app M.X) ≫ (freeForgetAdjunction R).counit.app M)
    have := Λ.epi_π_app M.X
    have := (free R).map_epi (Λ.π.app M.X)
    exact epi_comp _ _

/-- If `C` admits functorial flat resolutions, then so does `Mod C R`, by free modules. -/
lemma hasFunctorialFlatResolution_of_symmetric [Abelian.HasFunctorialFlatResolution C] :
    Abelian.HasFunctorialFlatResolution (Mod C R) :=
  ⟨flatLeftResolution R (Classical.choice ‹_›)⟩

end Flat

end CategoryTheory.Mod
