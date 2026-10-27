/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NY
-/
module

public import Sheaf.Paper.ClassicalNormalizedTwoFibreData
/-! # The two normalized fibres of a classical lisse adic system

Source: Bhatt--Scholze, Proposition 6.8.4(1),(4), Proposition 6.8.14(2),
Remark 6.8.15; blueprint real-mixed-by-curves, proof paragraph 1
(blueprint: def-zl-classical-two-fibre-common-data).

## Main definitions and statements

* `Common`: normalized scalar extension to the common-stage fibre.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option genSizeOfSpec false
set_option genCtorIdx false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
attribute [instance] AlgebraicGeometry.Scheme.pbcRationalHasShift
open scoped TensorProduct
namespace WeilConjectures.ClassicalTwoFibre
open AlgebraicGeometry.Scheme.ContinuousRational
open AlgebraicGeometry.Scheme.AdicFibreComparison

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] [hl : Fact (l ≠ D.p)]
  (Ω : Type u) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
  (Y₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
  [IsSeparated Y₀.hom]


/-- The common-stage comparison on realized finite-stage lisse objects. The sf
inclusion is the actual pair-category inclusion, and the PBC inclusion is `stageHeart`.
The normalization square specifies extension of the same finite-stage comparison.
Naturality is for every lisse map; common-stage representatives are such maps after
extension, with independence and further-extension compatibility supplied by `Descent`.
Source: BS 6.8.14(2), Remark 6.8.15
(blueprint: def-zl-classical-two-fibre-common-data). -/
structure Common (a : LisseRealization.Family D l hl.out) (R : ContinuousRational.Family.{u} l)
    (C : FdCoefficientComparison l Ω (D.geometricFiber Y₀).left)
    (ω : Fibres (k := D.k) l R) (V : CommonAssertions l R Ω ω)
    (S : ∀ E, AtStage D l Ω Y₀ E a R C ω) where
  fibres : ∀ (E : Padic.FiniteCoefficientFields l Ω)
      (K : (rationalLisseHeartProperty l (pbcFiniteField.{u} l Ω E)
        (D.geometricFiber Y₀).left).FullSubcategory)
      (x : Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left),
    (commonVector D l Ω Y₀ x).obj
      ((GeneralAlgebraicallyClosedCoefficients.inclusion
        (l := l) (Ω := Ω) (Y := (D.geometricFiber Y₀).left) E).obj K.obj) ≅
    (V.point (geometricBase D l Y₀) D.k x).functor.obj
      ((stageHeart l Ω (geometricBase D l Y₀) E).obj
        (((S E).toStage.heartFunctor D l Ω Y₀ E).obj K))
  normalization : ∀ (E : Padic.FiniteCoefficientFields l Ω)
      (K : (rationalLisseHeartProperty l (pbcFiniteField.{u} l Ω E)
        (D.geometricFiber Y₀).left).FullSubcategory)
      (x : Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left),
    (fibres E K x).hom ≫
      ((V.point (geometricBase D l Y₀) D.k x).finite_stage E).hom.app
        (((S E).toStage.heartFunctor D l Ω Y₀ E).obj K) =
      (commonVectorScalar D l Ω Y₀ E x K.obj).hom ≫
        (ModuleCat.extendScalars (stageEmbedding l Ω E)).map (((S E).fibres x).hom.app K)

end WeilConjectures.ClassicalTwoFibre
