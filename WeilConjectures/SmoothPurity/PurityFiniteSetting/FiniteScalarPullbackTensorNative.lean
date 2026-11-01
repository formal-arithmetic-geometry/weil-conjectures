/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Tensor.FiniteTensorFixedComparisons
public import WeilConjectures.AlgebraicGeometry.Etale.ProEtale.EtaleProEtaleScalarMateData
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ExtendScalars
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MonoidalStructure

/-! # The native scalar-extension/pullback tensor square

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-lem-sp-reduction/
thm-pur-finite-reduction-of-purity.proof.md, Step 2; Stacks Project, Tag 07A4.
(blueprint: lem-pur-finite-scalar-pullback-tensor-native)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option maxRecDepth 2000
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
open MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.Scheme

attribute [local implicit_reducible] WeilConjectures.PurityFiniteSetting.Coefficient
  Equivalence.mapDerivedCategory CategoryTheory.Equivalence.mk
  Scheme.sfIntrinsicDerivedEquivalence WeilConjectures.PurityFiniteSetting.coefficientCommRing
attribute [local irreducible] Functor.mapDerivedCategory Functor.leftDerivedFunctor
  Functor.rightDerivedFunctor ProEtale.upperStar ProEtale.sheafExtendScalars
  Functor.leftDerivedFunctorCounit Functor.leftAdjoint Functor.rightAdjoint
  Functor.mapDerivedCategoryFactors Functor.mapDerivedCategoryFactorsh
  HasDerivedCategory.standard

namespace WeilConjectures.PurityFiniteSetting

/-- The finite tensor reduction square of `finiteTensorPullbackTensorReduction` in which all
three pullback comparisons are the native pro-étale scalar/pullback mate
`scalarPullbackProEtaleIso`, conjugated by `leftDerivedUpperStarIsoMapDerivedCategory`.
Source: thm-pur-finite-reduction-of-purity, proof Step 2; Stacks 07A4
(blueprint: lem-pur-finite-scalar-pullback-tensor-native).
Proof: by naturality of every map in `K` and `L` and essential surjectivity of the
localization it suffices to treat `K = Q P` and `L = Q R` for flat-term K-flat complexes
`P`, `R`. Derived pullback and coefficient extension are computed on these
representatives (ringed pullback and change of coefficients preserve flat-term
K-flatness). There `finiteTensorCore` is the descent of the scalar balancing map and
`finiteTensorPullbackTensor` is the descent of the exact inverse-image tensor comparison,
so the square is the K-flat scalar/pullback tensor square of
`lem-pur-etale-scalar-pullback-tensor-kflat-representative`, transported to the pro-étale
site. Cancel the `leftDerivedUpperStarIsoMapDerivedCategory` conjugations by naturality.
No flatness of the coefficient quotient, no field structure on `X` or `Y` and no
finiteness on `K`, `L` is used. -/
theorem finiteScalarPullbackTensorNative (P : PurityFiniteSetting.{u})
    (m : ℕ) (hm : 1 ≤ m) (hmn : m ≤ P.level) {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K L : DerivedCategory
      (Sheaf (ProEt.topology Y) (ModuleCat.{u + 1} P.Coefficient))) :
    (P.finiteTensorReduction m hm hmn X).map
          (P.finiteTensorPullbackTensor f K L).hom ≫
        ((P.finiteTensorCore m hm hmn X).μIso
          ((P.smoothPurityPullback f).obj K)
          ((P.smoothPurityPullback f).obj L)).inv ≫
        (((P.finiteTensorReduction m hm hmn X).map
          ((ProEtale.leftDerivedUpperStarIsoMapDerivedCategory
            (ModuleCat.{u + 1} P.Coefficient) f).inv.app K) ≫
          (ProEtale.scalarPullbackProEtaleIso
            (P.finiteReductionRingHom m hm hmn).ulift f).inv.app K ≫
          (ProEtale.leftDerivedUpperStarIsoMapDerivedCategory
            (ModuleCat.{u + 1} (P.finiteReductionSetting m hm).Coefficient) f).hom.app
            ((P.finiteTensorReduction m hm hmn Y).obj K)) ⊗ₘ
        ((P.finiteTensorReduction m hm hmn X).map
          ((ProEtale.leftDerivedUpperStarIsoMapDerivedCategory
            (ModuleCat.{u + 1} P.Coefficient) f).inv.app L) ≫
          (ProEtale.scalarPullbackProEtaleIso
            (P.finiteReductionRingHom m hm hmn).ulift f).inv.app L ≫
          (ProEtale.leftDerivedUpperStarIsoMapDerivedCategory
            (ModuleCat.{u + 1} (P.finiteReductionSetting m hm).Coefficient) f).hom.app
            ((P.finiteTensorReduction m hm hmn Y).obj L))) =
      ((P.finiteTensorReduction m hm hmn X).map
          ((ProEtale.leftDerivedUpperStarIsoMapDerivedCategory
            (ModuleCat.{u + 1} P.Coefficient) f).inv.app (K ⊗ L)) ≫
        (ProEtale.scalarPullbackProEtaleIso
          (P.finiteReductionRingHom m hm hmn).ulift f).inv.app (K ⊗ L) ≫
        (ProEtale.leftDerivedUpperStarIsoMapDerivedCategory
          (ModuleCat.{u + 1} (P.finiteReductionSetting m hm).Coefficient) f).hom.app
          ((P.finiteTensorReduction m hm hmn Y).obj (K ⊗ L))) ≫
        ((P.finiteReductionSetting m hm).smoothPurityPullback f).map
          ((P.finiteTensorCore m hm hmn Y).μIso K L).inv ≫
        ((P.finiteReductionSetting m hm).finiteTensorPullbackTensor f
          ((P.finiteTensorReduction m hm hmn Y).obj K)
          ((P.finiteTensorReduction m hm hmn Y).obj L)).hom := by
  sorry

end WeilConjectures.PurityFiniteSetting
