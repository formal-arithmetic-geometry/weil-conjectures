/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Algebra.Homology.HomotopyCategory.MapBraided
public import WeilConjectures.Algebra.Homology.HomotopyCategory.MapMonoidal
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MapDerivedCategory
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Monoidal
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Unit
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategoryBraidedQh
public import WeilConjectures.CategoryTheory.Monoidal.OplaxOfLaxSquare
public import WeilConjectures.CategoryTheory.Monoidal.OplaxOfLaxSquareBraided

/-!
# The left derived functor of an exact braided functor is braided

Let `F : C ⥤ D` be an exact strong monoidal functor between monoidal Grothendieck abelian
categories with functorial flat resolutions, which preserves flat objects and is a left adjoint.
Its total left derived functor `LF : D(C) ⥤ D(D)` is a monoidal functor, with comonoidal
structure the tensor comparison `CategoryTheory.Functor.leftDerivedTensorComparison`; if `F` is
braided, so is `LF`, for the braidings `DerivedCategory.braidedCategory`.

## Main definitions

- `CategoryTheory.Functor.leftDerivedOplaxMonoidal F`: the oplax monoidal structure of `LF`.
- `CategoryTheory.Functor.leftDerivedMonoidal F`: the monoidal structure of `LF`.
- `CategoryTheory.Functor.leftDerivedBraided F`: the braided structure of `LF`, for `F` braided.

## Implementation notes

The coherence axioms are checked on complexes whose image under `F` is K-flat
(`CategoryTheory.Functor.OplaxMonoidal.ofLaxSquare`), exactly as for the derived pullback of
étale sheaves (`AlgebraicGeometry.Etale.leftDerivedUpperStarMonoidal`).
-/

@[expose] public section

universe u u₁ u₂

open CategoryTheory Abelian Limits MonoidalCategory DerivedCategory

open scoped CategoryTheory.Functor

namespace CategoryTheory.Functor

variable {C : Type u₁} [Category.{u + 1} C] [Abelian C] [IsGrothendieckAbelian.{u + 1} C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
  [HasFunctorialFlatResolution C]
  {D : Type u₂} [Category.{u + 1} D] [Abelian D] [IsGrothendieckAbelian.{u + 1} D]
  [MonoidalCategory D] [MonoidalPreadditive D] [MonoidalClosed D] [BraidedCategory D]
  [HasFunctorialFlatResolution D]

variable (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [F.PreservesFlat] [F.IsLeftAdjoint]

omit [HasFunctorialFlatResolution D] [PreservesFiniteLimits F] [PreservesFiniteColimits F] in
/-- Every object of `D(C)` is isomorphic to `Qh P` for a complex `P` whose image under `F` is
K-flat. -/
lemma exists_kFlatMap_iso (X : DerivedCategory C) :
    ∃ P, F.kFlatMap P ∧ Nonempty (Qh.obj P ≅ X) := by
  have := Localization.essSurj (Qh (C := C)) (HomotopyCategory.quasiIso _ (.up ℤ))
  obtain ⟨R⟩ := LocalizerMorphism.IsLeftDerivabilityStructure.hasLeftResolutions
    (Φ := HomotopyCategory.quasiIsoLocalizerMorphism F.kFlatMap) (Qh.objPreimage X)
  have : IsIso (Qh.map R.w) := Localization.inverts Qh (HomotopyCategory.quasiIso _ _) _ R.hw
  exact ⟨R.X₁.obj, R.X₁.property, ⟨asIso (Qh.map R.w) ≪≫ Qh.objObjPreimageIso X⟩⟩

open OplaxMonoidal LaxMonoidal

section Monoidal

variable [F.Monoidal]

/-- The oplax monoidal structure on the left derived functor `LF : D(C) ⥤ D(D)` of an exact
monoidal functor `F`, whose comonoidal structure is the tensor comparison
`CategoryTheory.Functor.leftDerivedTensorComparison`. It is induced by the oplax monoidal
structure of `F` on homotopy categories, computing on complexes whose image under `F` is
K-flat. -/
@[instance_reducible]
noncomputable def leftDerivedOplaxMonoidal : F.leftDerivedFunctor.OplaxMonoidal :=
  haveI := DerivedCategory.isIso_ε_Qh D
  OplaxMonoidal.ofLaxSquare (Q₁ := Qh) (Q₂ := Qh)
    (F := F.mapHomotopyCategory (.up ℤ)) F.leftDerivedTensorComparison
    (fun a ↦ F.leftDerivedFunctorCounit.app a)
    (fun _ _ f ↦ F.leftDerivedFunctorCounit.naturality f)
    F.leftDerivedTensorComparison_app_app_comp_tensorHom F.kFlatMap
    F.exists_kFlatMap_iso (fun x _ hb ↦ isIso_μNatTrans_Qh_app_app_of_kFlat x _ hb)

lemma isIso_leftDerivedOplaxMonoidal_δ (X X' : DerivedCategory C) :
    letI := F.leftDerivedOplaxMonoidal
    IsIso (δ F.leftDerivedFunctor X X') :=
  inferInstanceAs (IsIso ((F.leftDerivedTensorComparison.app X).app X'))

lemma isIso_leftDerivedOplaxMonoidal_η :
    letI := F.leftDerivedOplaxMonoidal
    IsIso (η F.leftDerivedFunctor) := by
  have := DerivedCategory.isIso_ε_Qh D
  have := DerivedCategory.isIso_ε_Qh C
  have : IsIso (η (F.mapHomotopyCategory (.up ℤ))) := by
    rw [Functor.mapHomotopyCategory_η]
    infer_instance
  exact inferInstanceAs (IsIso (F.leftDerivedFunctor.map (ε Qh) ≫
    F.leftDerivedFunctorCounit.app (𝟙_ _) ≫
      Qh.map (η (F.mapHomotopyCategory (.up ℤ))) ≫ CategoryTheory.inv (ε Qh)))

/-- The left derived functor `LF : D(C) ⥤ D(D)` of an exact monoidal functor `F` as a monoidal
functor: the oplax monoidal structure `leftDerivedOplaxMonoidal`, whose structure maps are
isomorphisms. -/
@[instance_reducible]
noncomputable def leftDerivedMonoidal : F.leftDerivedFunctor.Monoidal :=
  letI := F.leftDerivedOplaxMonoidal
  haveI := F.isIso_leftDerivedOplaxMonoidal_δ
  haveI := F.isIso_leftDerivedOplaxMonoidal_η
  (Functor.CoreMonoidal.ofOplaxMonoidal _).toMonoidal

end Monoidal

section Braided

variable [F.Braided]

/-- The tensor comparison `LF(K ⊗ᴸ M) ⟶ LF K ⊗ᴸ LF M` of the left derived functor of an exact
braided functor is compatible with the braidings `DerivedCategory.braidedCategory`. -/
lemma leftDerived_map_braiding_comp_tensorComparison (X X' : DerivedCategory C) :
    letI := DerivedCategory.braidedCategory C
    letI := DerivedCategory.braidedCategory D
    F.leftDerivedFunctor.map (β_ X X').hom ≫ (F.leftDerivedTensorComparison.app X').app X =
      (F.leftDerivedTensorComparison.app X).app X' ≫
        (β_ (F.leftDerivedFunctor.obj X) (F.leftDerivedFunctor.obj X')).hom :=
  letI := DerivedCategory.braidedCategory C
  letI := DerivedCategory.braidedCategory D
  map_braiding_comp_app_app_of_lax_square (Q₁ := Qh) (Q₂ := Qh)
    (F := F.mapHomotopyCategory (.up ℤ)) F.leftDerivedTensorComparison
    (fun a ↦ F.leftDerivedFunctorCounit.app a)
    (fun _ _ f ↦ F.leftDerivedFunctorCounit.naturality f)
    F.leftDerivedTensorComparison_app_app_comp_tensorHom braiding_hom_μ_Qh
    braiding_hom_μ_Qh F.mapHomotopyCategory_δ_comp_braiding
    F.kFlatMap F.exists_kFlatMap_iso
    (fun x _ hb ↦ isIso_μNatTrans_Qh_app_app_of_kFlat x _ hb) X X'

/-- The left derived functor `LF : D(C) ⥤ D(D)` of an exact braided functor `F` is a braided
monoidal functor for the braidings `DerivedCategory.braidedCategory` of the derived tensor
products. Its underlying monoidal structure is `CategoryTheory.Functor.leftDerivedMonoidal`. -/
@[instance_reducible]
noncomputable def leftDerivedBraided :
    letI := DerivedCategory.braidedCategory C
    letI := DerivedCategory.braidedCategory D
    F.leftDerivedFunctor.Braided :=
  letI := DerivedCategory.braidedCategory C
  letI := DerivedCategory.braidedCategory D
  letI := F.leftDerivedMonoidal
  Functor.Braided.ofMapBraidingCompδ _ F.leftDerived_map_braiding_comp_tensorComparison

end Braided

end CategoryTheory.Functor
