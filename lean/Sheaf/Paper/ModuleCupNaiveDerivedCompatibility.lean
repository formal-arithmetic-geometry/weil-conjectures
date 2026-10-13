/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P3
-/
module

public import Sheaf.Paper.ModuleCupResolutionData
public import Sheaf.AlgebraicGeometry.DerivedTensorStructure
public import Sheaf.AlgebraicGeometry.RingedSpaceDerivedDirectImage
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution

/-! # Naive/derived cup diagram for arbitrary module complexes

Source: Stacks Project, Section 20.31, Lemma 20.31.3, specialized to
(X, O_X) to (pt, Gamma(X, O_X)). The theorem gives the actual section tensor
formula, a natural derived cup, and equality of the two composites of the diagram.
-/

@[expose] public section

universe u wC
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

noncomputable section

variable (X : Scheme.{u})
  [HasDerivedCategory.{u} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]

local instance : MonoidalCategory (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
  SheafOfModules.monoidalCategory X.sheaf
local instance : SymmetricCategory (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
  SheafOfModules.symmetricCategory X.sheaf

local instance : HasColimitsOfSize.{0, 0} (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
  hasColimitsOfSizeShrink.{0, 0, u} _

local instance : MonoidalPreadditive (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
  Classical.choice (SheafOfModules.tensorClosed X.sheaf).1
local instance : MonoidalClosed (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
  Classical.choice (SheafOfModules.tensorClosed X.sheaf).2.1
local instance : Abelian.HasFunctorialFlatResolution
    (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
  schemeModule_hasFunctorialFlatResolution X

/-- The canonical comparison from termwise global sections to derived global sections.
It is the unit of the right derived functor, transported from homotopy categories
using the quotient/localization comparison isomorphisms. -/
def moduleCup_globalComparison
    (K : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ) :
    DerivedCategory.Q.obj
      (((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj K) ⟶
    (RingedSpace.globalSectionsFunctor X.toRingedSpace).rightDerivedFunctor.obj
      (DerivedCategory.Q.obj K) :=
  let S := RingedSpace.globalSectionsFunctor X.toRingedSpace
  (DerivedCategory.quotientCompQhIso
    (ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤)))).inv.app _ ≫
    S.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient _ _).obj K) ≫
    S.rightDerivedFunctor.map ((DerivedCategory.quotientCompQhIso
      (SheafOfModules.{u} (moduleRings X.toRingedSpace))).hom.app K)

/-- The six-object global specialization of the naive/derived cup diagram.
Source: Stacks Project, Section 20.31, Lemma 20.31.3 and the following global
specialization to (X,O_X) → (pt,Γ(X,O_X)).
(blueprint: lem-sc-module-cup-naive-derived-compatibility)
The product μ is a natural family on derived objects. For every pair of arbitrary
integer complexes there is a naive cochain map, specified on every tensor summand
by tensoring sections. The top arrow is the tensor of the right-derived comparison
units, the two tensor comparisons are the lax monoidal maps of Q, and the bottom
arrow is the same right-derived unit at the total tensor complex. No commutativity
is assumed, and no boundedness, flatness or acyclicity hypothesis is imposed.
Proof: construct μ as the relative cup for the map to the one-point ringed space,
adjoint to the tensor of the counits of derived pullback/direct image. Construct
ν on tensor summands by the displayed formula; the signed Leibniz rule makes it
a cochain map. Naturality of counits gives naturality of μ. To check the outer
six-object diagram, take adjoints of both composites. Naturality of the maps from
derived pullback to ordinary pullback and from derived tensor to total tensor
reduces the equality to the ordinary pullback/sections adjunction formula for ν.
This is precisely the polygon argument in the cited lemma. -/
theorem moduleCup_naive_derived_compatibility :
    let S := RingedSpace.globalSectionsFunctor X.toRingedSpace
    let T := S.mapHomologicalComplex (ComplexShape.up ℤ)
    let R := S.rightDerivedFunctor
    ∃ μ : ∀ A B : DerivedCategory (SheafOfModules.{u} (moduleRings X.toRingedSpace)),
        R.obj A ⊗ R.obj B ⟶ R.obj (A ⊗ B),
      (∀ (A A' B B' : DerivedCategory
          (SheafOfModules.{u} (moduleRings X.toRingedSpace)))
        (f : A ⟶ A') (g : B ⟶ B'),
        (R.map f ⊗ₘ R.map g) ≫ μ A' B' = μ A B ≫ R.map (f ⊗ₘ g)) ∧
      ∀ K L : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ,
        ∃ ν : T.obj K ⊗ T.obj L ⟶ T.obj (K ⊗ L),
          (∀ (i j n : ℤ) (h : i + j = n)
            (x : Γ(K.X i, ⊤)) (y : Γ(L.X j, ⊤)),
            (ν.f n).hom
              ((HomologicalComplex.ιTensorObj (T.obj K) (T.obj L) i j n h).hom
                (TensorProduct.tmul Γ(X, ⊤) x y)) =
              (HomologicalComplex.ιTensorObj K L i j n h).val.app (op ⊤)
                (tmulSection x y)) ∧
          (moduleCup_globalComparison X K ⊗ₘ moduleCup_globalComparison X L) ≫
              μ (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj L) ≫
              R.map (Functor.LaxMonoidal.μ DerivedCategory.Q K L) =
            Functor.LaxMonoidal.μ DerivedCategory.Q (T.obj K) (T.obj L) ≫
              DerivedCategory.Q.map ν ≫ moduleCup_globalComparison X (K ⊗ L) := by sorry

end
end AlgebraicGeometry.Scheme.Modules
