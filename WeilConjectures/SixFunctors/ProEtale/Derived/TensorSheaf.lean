/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Algebra.Homology.BifunctorSingleComparison
public import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
public import WeilConjectures.SixFunctors.ProEtale.Derived.TensorResolution
public import WeilConjectures.SixFunctors.ProEtale.Derived.UpperStarMonoidal.Comparison

/-!
# The derived tensor product with a sheaf

For a pro-étale sheaf `c` on `X`, the left derived functor `L(- ⊗ c)` of the tensor product with
`c` is the derived tensor product `- ⊗ᴸ c` with `c` placed in degree `0`: both are computed on a
K-flat complex `K` by the complex `K ⊗ c`.

For `g : Z ⟶ Y`, sheaves `c_Y` on `Y` and `c_Z` on `Z` and a morphism `κ : g^* c_Y ⟶ c_Z`, the
comparison `g^*(P ⊗ c_Y) ⟶ g^* P ⊗ g^* c_Y ⟶ g^* P ⊗ c_Z` induces a natural transformation
`Lg^* (K ⊗ᴸ c_Y) ⟶ Lg^* K ⊗ᴸ c_Z` of left derived functors. Through `L(- ⊗ c) ≅ - ⊗ᴸ c`, it is the
comparison `Lg^* (K ⊗ᴸ c_Y) ⟶ Lg^* K ⊗ᴸ Lg^* c_Y` of the derived pullback with the derived
tensor product (`AlgebraicGeometry.ProEtale.leftDerivedUpperStarTensorComparison`) followed by
`Lg^* c_Y ⟶ c_Z`.

The constructions are made for a general coefficient category `A`: for a concrete category such
as `ModuleCat R`, the kernel is slow to check terms involving the tensor product of the homotopy
category.

## Main definitions and results

- `AlgebraicGeometry.ProEtale.leftDerivedTensorRightIso`: `L(- ⊗ c) ≅ - ⊗ᴸ c`.
- `AlgebraicGeometry.ProEtale.leftDerivedTensorRightUpperStarMap`: the comparison
  `Lg^* (K ⊗ᴸ c_Y) ⟶ Lg^* K ⊗ᴸ c_Z` induced by `κ`.
- `AlgebraicGeometry.ProEtale.leftDerivedTensorRightUpperStarMap_app_comp`: its identification with
  the comparison of the derived pullback with the derived tensor product.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory HomologicalComplex Functor.OplaxMonoidal

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open Scheme

variable {A : Type u'} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

section Single

variable {X : Scheme.{u}} (c : Sheaf (ProEt.topology X) A)

/-- Tensoring with a fixed pro-étale sheaf sends quasi-isomorphisms between K-flat complexes to
quasi-isomorphisms. -/
instance preservesKFlatQuasiIso_tensorRight : (tensorRight c).PreservesKFlatQuasiIso :=
  sorry

/-- A pro-étale sheaf `c` placed in degree `0`, as an object of `D(X_proét)`. -/
noncomputable abbrev derivedSingle : DerivedCategory (Sheaf (ProEt.topology X) A) :=
  DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj ((single _ (.up ℤ) 0).obj c))

/-- On homotopy categories, the tensor product with `c` placed in degree `0` is the degreewise
tensor product with `c`. -/
noncomputable def tensorSingleIso :
    (curriedTensor (HomotopyCategory (Sheaf (ProEt.topology X) A) (.up ℤ))).flip.obj
        ((HomotopyCategory.quotient _ _).obj ((single _ (.up ℤ) 0).obj c)) ≅
      (tensorRight c).mapHomotopyCategory (.up ℤ) :=
  sorry

/-- The counit exhibiting `- ⊗ᴸ c` as the left derived functor of `- ⊗ c`: the comparison
`Qh K ⊗ᴸ Qh c ⟶ Qh (K ⊗ c)` followed by `AlgebraicGeometry.ProEtale.tensorSingleIso`. -/
noncomputable def derivedTensorSingleCounit :
    DerivedCategory.Qh ⋙ (-⊗ᴸ-(X)[A]).flip.obj (derivedSingle c) ⟶
      (tensorRight c).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh :=
  sorry

instance isLeftDerivedFunctor_derivedTensorSingle :
    ((-⊗ᴸ-(X)[A]).flip.obj (derivedSingle c)).IsLeftDerivedFunctor
      (derivedTensorSingleCounit c) (HomotopyCategory.quasiIso _ (.up ℤ)) :=
  sorry

/-- **`L(- ⊗ c) ≅ - ⊗ᴸ c`**: the left derived functor of the tensor product with a sheaf `c` is
the derived tensor product with `c` placed in degree `0`. -/
noncomputable def leftDerivedTensorRightIso :
    L(tensorRight c) ≅ (-⊗ᴸ-(X)[A]).flip.obj (derivedSingle c) :=
  Functor.leftDerivedUnique _ _ (tensorRight c).leftDerivedFunctorCounit
    (derivedTensorSingleCounit c) (HomotopyCategory.quasiIso _ (.up ℤ))

end Single

section Pullback

variable [ProEtale.UpperStarPreservesFlat A] {Y Z : Scheme.{u}} (g : Z ⟶ Y)
  {c_Y : Sheaf (ProEt.topology Y) A} {c_Z : Sheaf (ProEt.topology Z) A}
  (κ : (g)^*[A].obj c_Y ⟶ c_Z)

/-- The comparison `g^*(P ⊗ c_Y) ⟶ g^* P ⊗ c_Z` of pro-étale sheaves: the comonoidal structure of
the pullback followed by `κ : g^* c_Y ⟶ c_Z`. -/
noncomputable def tensorRightUpperStarMap :
    tensorRight c_Y ⋙ (g)^*[A] ⟶ (g)^*[A] ⋙ tensorRight c_Z where
  app P := δ (g)^*[A] P c_Y ≫ (_ ◁ κ)
  naturality P Q f := by
    dsimp
    rw [← δ_natural_left_assoc, Category.assoc, whisker_exchange]

/-- The counit of `L(- ⊗ c_Y) ⋙ Lg^*`: the counit of `L(- ⊗ c_Y)` followed by the counit of
`Lg^*`. -/
noncomputable def leftDerivedTensorRightUpperStarCounit :
    DerivedCategory.Qh ⋙ L(tensorRight c_Y) ⋙ L((g)^*[A]) ⟶
      (tensorRight c_Y).mapHomotopyCategory (.up ℤ) ⋙ (g)^*[A].mapHomotopyCategory (.up ℤ) ⋙
        DerivedCategory.Qh :=
  Functor.whiskerRight (tensorRight c_Y).leftDerivedFunctorCounit L((g)^*[A]) ≫
    Functor.whiskerLeft ((tensorRight c_Y).mapHomotopyCategory (.up ℤ))
      (g)^*[A].leftDerivedFunctorCounit

variable (c_Z) in
/-- The counit of `Lg^* ⋙ L(- ⊗ c_Z)`: the counit of `Lg^*` followed by the counit of
`L(- ⊗ c_Z)`. -/
noncomputable def leftDerivedUpperStarTensorRightCounit :
    DerivedCategory.Qh ⋙ L((g)^*[A]) ⋙ L(tensorRight c_Z) ⟶
      (g)^*[A].mapHomotopyCategory (.up ℤ) ⋙ (tensorRight c_Z).mapHomotopyCategory (.up ℤ) ⋙
        DerivedCategory.Qh :=
  Functor.whiskerRight (g)^*[A].leftDerivedFunctorCounit L(tensorRight c_Z) ≫
    Functor.whiskerLeft ((g)^*[A].mapHomotopyCategory (.up ℤ))
      (tensorRight c_Z).leftDerivedFunctorCounit

variable (c_Z) in
instance isLeftDerivedFunctor_leftDerivedUpperStarTensorRight :
    (L((g)^*[A]) ⋙ L(tensorRight c_Z)).IsLeftDerivedFunctor
      (leftDerivedUpperStarTensorRightCounit g c_Z) (HomotopyCategory.quasiIso _ (.up ℤ)) :=
  sorry

/-- The comparison `g^*(P ⊗ c_Y) ⟶ g^* P ⊗ c_Z` on homotopy categories. -/
noncomputable def mapHomotopyCategoryTensorRightUpperStarMap :
    (tensorRight c_Y).mapHomotopyCategory (.up ℤ) ⋙ (g)^*[A].mapHomotopyCategory (.up ℤ) ⟶
      (g)^*[A].mapHomotopyCategory (.up ℤ) ⋙ (tensorRight c_Z).mapHomotopyCategory (.up ℤ) :=
  (Functor.mapHomotopyCategoryCompIso (Iso.refl _) _).hom ≫
    NatTrans.mapHomotopyCategory (tensorRightUpperStarMap g κ) (.up ℤ) ≫
    (Functor.mapHomotopyCategoryCompIso (Iso.refl _) _).inv

/-- The comparison `Lg^* (K ⊗ᴸ c_Y) ⟶ Lg^* K ⊗ᴸ c_Z` induced by the comparison
`g^*(P ⊗ c_Y) ⟶ g^* P ⊗ c_Z` of sheaves, where `- ⊗ᴸ c` is the left derived functor of `- ⊗ c`. -/
noncomputable def leftDerivedTensorRightUpperStarMap :
    L(tensorRight c_Y) ⋙ L((g)^*[A]) ⟶ L((g)^*[A]) ⋙ L(tensorRight c_Z) :=
  Functor.leftDerivedNatTrans _ _ (leftDerivedTensorRightUpperStarCounit g)
    (leftDerivedUpperStarTensorRightCounit g c_Z) (HomotopyCategory.quasiIso _ (.up ℤ))
    (Functor.whiskerRight (mapHomotopyCategoryTensorRightUpperStarMap g κ) DerivedCategory.Qh)

/-- The defining property of `AlgebraicGeometry.ProEtale.leftDerivedTensorRightUpperStarMap`. -/
@[reassoc]
lemma leftDerivedTensorRightUpperStarMap_app_comp_counit
    (K : HomotopyCategory (Sheaf (ProEt.topology Y) A) (.up ℤ)) :
    (leftDerivedTensorRightUpperStarMap g κ).app (DerivedCategory.Qh.obj K) ≫
        (leftDerivedUpperStarTensorRightCounit g c_Z).app K =
      (leftDerivedTensorRightUpperStarCounit g).app K ≫
        DerivedCategory.Qh.map ((mapHomotopyCategoryTensorRightUpperStarMap g κ).app K) :=
  Functor.leftDerivedNatTrans_app _ _ _ _ _ _ K

/-- The morphism `Lg^* c_Y ⟶ c_Z` in the derived category induced by `κ`: the counit of `Lg^*`
at `c_Y` followed by `κ`. -/
noncomputable def leftDerivedUpperStarDerivedSingleMap :
    L((g)^*[A]).obj (derivedSingle c_Y) ⟶ derivedSingle c_Z :=
  (g)^*[A].leftDerivedFunctorCounit.app _ ≫
    DerivedCategory.Qh.map ((HomotopyCategory.quotient _ _).map
      ((singleMapHomologicalComplex (g)^*[A] (.up ℤ) 0).hom.app c_Y ≫ (single _ (.up ℤ) 0).map κ))

instance isIso_leftDerivedUpperStarDerivedSingleMap [IsIso κ] :
    IsIso (leftDerivedUpperStarDerivedSingleMap g κ) :=
  sorry

/-- **The comparison `Lg^* (K ⊗ᴸ c_Y) ⟶ Lg^* K ⊗ᴸ c_Z` is induced by the comparison of the derived
pullback with the derived tensor product**: through `L(- ⊗ c) ≅ - ⊗ᴸ c`, the comparison
`AlgebraicGeometry.ProEtale.leftDerivedTensorRightUpperStarMap` is
`Lg^* (K ⊗ᴸ c_Y) ⟶ Lg^* K ⊗ᴸ Lg^* c_Y ⟶ Lg^* K ⊗ᴸ c_Z`. -/
lemma leftDerivedTensorRightUpperStarMap_app_comp
    (K : DerivedCategory (Sheaf (ProEt.topology Y) A)) :
    (leftDerivedTensorRightUpperStarMap g κ).app K ≫
        (leftDerivedTensorRightIso c_Z).hom.app (L((g)^*[A]).obj K) =
      L((g)^*[A]).map ((leftDerivedTensorRightIso c_Y).hom.app K) ≫
        ((leftDerivedUpperStarTensorComparison A g).app K).app (derivedSingle c_Y) ≫
        ((-⊗ᴸ-(Z)[A]).obj (L((g)^*[A]).obj K)).map (leftDerivedUpperStarDerivedSingleMap g κ) :=
  sorry

end Pullback

end AlgebraicGeometry.ProEtale
