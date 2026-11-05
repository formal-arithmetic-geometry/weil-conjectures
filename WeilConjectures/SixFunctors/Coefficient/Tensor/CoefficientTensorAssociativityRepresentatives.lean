/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Coefficient.Tensor.CoefficientTensorAssociativityModelData
import all WeilConjectures.SixFunctors.Coefficient.Tensor.CoefficientTensorAssociativityModelData
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.Algebra.Homology.KFlatTotalTensorModel.KFlatTotalTensorModelSupplement

/-! # Associativity on simultaneous resolving representatives

Source: Stacks 07A4 and 0FPT.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option Elab.async false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe c v r wb d vd s wa b vb a va
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
namespace WeilConjectures

attribute [local implicit_reducible] CoefficientClosedStructure.tensor
  CategoryTheory.uniformProd
  CategoryTheory.MonoidalCategory.leftAssocTensor
  CategoryTheory.MonoidalCategory.rightAssocTensor

attribute [local irreducible] homComplexFunctor homComplexπ derivedInternalHomOfUniverses
  coefficientHomResolutionIso
  DerivedCategory instCategoryDerivedCategory DerivedCategory.Q
  SheafOfModules.IsFlatOnSite
  CochainComplex.IsKFlatIndependentCoefficients

variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  (R : Sheaf J CommRingCat.{max c v r})
  {D : Type d} [Category.{vd} D] (J' : GrothendieckTopology D)
  [HasSheafify J' AddCommGrpCat.{max d vd s}]
  [J'.WEqualsLocallyBijective AddCommGrpCat.{max d vd s}]
  (R' : Sheaf J' CommRingCat.{max d vd s})
  [HasDerivedCategory.{wb} (RingedTensorModules.{c, v, r} J R)]
  [HasDerivedCategory.{wa} (RingedTensorModules.{d, vd, s} J' R')]

variable (SB : CoefficientClosedStructure (derivedInternalHomOfUniverses.{c, v, r, wb} J R))
  (TB : CoefficientTensorModels.{r, c, v, wb} J R SB)
  (βB : @SymmetricCategory _ _ SB.monoidal)
  (cB : RingedDerivedTensorCoherence.{c, v, r, wb} J R SB TB βB)
  (SA : CoefficientClosedStructure (derivedInternalHomOfUniverses.{d, vd, s, wa} J' R'))
  (TA : CoefficientTensorModels.{s, d, vd, wa} J' R' SA)
  (βA : @SymmetricCategory _ _ SA.monoidal)
  (cA : RingedDerivedTensorCoherence.{d, vd, s, wa} J' R' SA TA βA)
  (K : CochainComplex (RingedTensorModules.{c, v, r} J R) ℤ ⥤
    CochainComplex (RingedTensorModules.{d, vd, s} J' R') ℤ)
  (F : DerivedCategory (RingedTensorModules.{c, v, r} J R) ⥤
    DerivedCategory (RingedTensorModules.{d, vd, s} J' R'))
  (ε : DerivedCategory.Q ⋙ F ⟶ K ⋙ DerivedCategory.Q)
  (hε : ∀ (P : CochainComplex (RingedTensorModules.{c, v, r} J R) ℤ),
    P.IsKFlatIndependentCoefficients →
    (∀ p : ℤ, SheafOfModules.IsFlatOnSite.{c, v, max c v r, max c v r}
      (R := R) (P.X p)) → IsIso (ε.app P))
  (hU : ∀ (P : CochainComplex (RingedTensorModules.{c, v, r} J R) ℤ),
    P.IsKFlatIndependentCoefficients →
    (∀ p : ℤ, SheafOfModules.IsFlatOnSite.{c, v, max c v r, max c v r}
      (R := R) (P.X p)) →
    CochainComplex.IsKFlatIndependentCoefficients (R := R') (K.obj P))
  (chain : coefficientTotalTensor.{r, c, v} J R ⋙ K ≅
    K.prod K ⋙ coefficientTotalTensor.{s, d, vd} J' R')
  (hκ : CoefficientComplexTensorAssociativity J R J' R' K chain)
  (μ : SB.tensor ⋙ F ≅ F.prod F ⋙ SA.tensor)
  (hμ : ∀ (P Q : CochainComplex (RingedTensorModules.{c, v, r} J R) ℤ)
    (hP : P.IsKFlatIndependentCoefficients) (hQ : Q.IsKFlatIndependentCoefficients)
    (hUP : CochainComplex.IsKFlatIndependentCoefficients (R := R') (K.obj P))
    (hUQ : CochainComplex.IsKFlatIndependentCoefficients (R := R') (K.obj Q))
    (_fP : ∀ p : ℤ, SheafOfModules.IsFlatOnSite.{c, v, max c v r, max c v r}
      (R := R) (P.X p))
    (_fQ : ∀ p : ℤ, SheafOfModules.IsFlatOnSite.{c, v, max c v r, max c v r}
      (R := R) (Q.X p)),
    F.map (TB.iso J R SB P Q hP hQ).hom ≫
        μ.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫
        SA.tensor.map
          (X := (F.obj (DerivedCategory.Q.obj P), F.obj (DerivedCategory.Q.obj Q)))
          (Y := (DerivedCategory.Q.obj (K.obj P), DerivedCategory.Q.obj (K.obj Q)))
          (Prod.mkHom (ε.app P) (ε.app Q)) =
      ε.app ((coefficientTotalTensor.{r, c, v} J R).obj (P, Q)) ≫
        DerivedCategory.Q.map (chain.hom.app (P, Q)) ≫
        (TA.iso J' R' SA (K.obj P) (K.obj Q) hUP hUQ).hom)

include cB cA hε hU hκ hμ

attribute [local irreducible] coefficientTotalTensor SheafOfModules.monoidalCategory

end WeilConjectures
