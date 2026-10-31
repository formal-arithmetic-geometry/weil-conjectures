/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralVerdier.IntegralVerdierModels
public import WeilConjectures.SixFunctors.Finite.Scalar.Tensor.FiniteScalarTensorRealization

/-! # Constructed tensor comparison for an intrinsic Hom presentation

Source: Stacks Project, Tags 06YS, 07A4 and 04VK.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures.IntegralVerdier

attribute [local instance high] SymmetricCategory.toBraidedCategory
attribute [local instance 20000] ProEtale.sheafBraidedCategory

/-- Restrict the given K-flat tensor presentation to flat-term K-flat representatives.
Source: Stacks 06YS and 07A4
(blueprint: def-sf-finite-intrinsic-tensor-realization). -/
def finiteIntrinsicTensorModel (X : Scheme.{u}) (B : Type u) [CommRing B] [Finite B]
    (a : IntegralHom.TensorPresentation.{u, u} X (proEtaleConstantRing X B)) :
    ProEtaleTensorModel X (proEtaleConstantRing X B) := by
  let j := ObjectProperty.ιOfLE
    (P := proEtaleFlatRepresentatives X (proEtaleConstantRing X B))
    (P' := IntegralHom.flat.{u, u} X (proEtaleConstantRing X B))
    (fun P hP ↦ (CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat P).mpr hP.1)
  exact { tensor := a.tensor
          representative := Functor.isoWhiskerLeft (j.prod j) a.representative }

/-- The inverse of the specified scalar tensor realization, in uncurried notation.
This is constructed from the existing normalized tensor comparison, with no choice
of tensor data and no assertion about internal Hom or biduality.
Source: Stacks 07A4 and 04VK
(blueprint: def-sf-finite-intrinsic-tensor-realization). -/
def finiteIntrinsicTensorRealization (X : Scheme.{u}) (B : Type u) [CommRing B] [Finite B]
    (a : IntegralHom.TensorPresentation.{u, u} X (proEtaleConstantRing X B)) :
    (sfIntrinsicDerivedEquivalence X B).functor.prod
        (sfIntrinsicDerivedEquivalence X B).functor ⋙ a.tensor ≅
      Functor.uncurry.obj (CategoryTheory.MonoidalCategory.curriedTensor _) ⋙
        (sfIntrinsicDerivedEquivalence X B).functor := by
  let F := (sfIntrinsicDerivedEquivalence X B).functor
  let T := CategoryTheory.MonoidalCategory.curriedTensor
    (DerivedCategory (Sheaf (ProEt.topology X)
      (ModuleCat.{u + 1} (ULift.{u + 1, u} B))))
  let S := a.tensor
  let t := finiteScalarTensorRealization X B (finiteIntrinsicTensorModel X B a)
  refine NatIso.ofComponents (fun KL ↦ ((t.app KL.1).app KL.2).symm) ?_
  rintro ⟨K, L⟩ ⟨K', L'⟩ ⟨f, g⟩
  have h₁ : S.map (Prod.mkHom (F.map f) (𝟙 _)) ≫ (t.inv.app K').app L =
      (t.inv.app K).app L ≫ F.map ((T.map f).app L) := by
    exact congr_app (t.inv.naturality f) L
  have h₂ : S.map (Prod.mkHom (𝟙 _) (F.map g)) ≫ (t.inv.app K').app L' =
      (t.inv.app K').app L ≫ F.map ((T.obj K').map g) :=
    (t.inv.app K').naturality g
  change S.map (Prod.mkHom (F.map f) (F.map g)) ≫ (t.inv.app K').app L' =
    (t.inv.app K).app L ≫ F.map ((Functor.uncurry.obj T).map (f, g))
  rw [show S.map (Prod.mkHom (F.map f) (F.map g)) =
      S.map (Prod.mkHom (F.map f) (𝟙 _)) ≫ S.map (Prod.mkHom (𝟙 _) (F.map g)) by
    rw [← S.map_comp]
    simp only [prod_comp, Category.comp_id, Category.id_comp]]
  rw [Category.assoc, h₂, ← Category.assoc, h₁, Category.assoc, ← F.map_comp]
  rfl

end WeilConjectures.IntegralVerdier
