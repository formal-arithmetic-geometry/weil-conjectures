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
(blueprint: def-zl-classical-two-fibre-scalar-data).

## Main definitions and statements

* `Scalars`: canonical finite coefficient commuting square.
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
attribute [-instance] AlgebraicGeometry.Scheme.pbcRationalHasShift
open scoped TensorProduct
namespace WeilConjectures.ClassicalTwoFibre
open AlgebraicGeometry.Scheme.ContinuousRational
open AlgebraicGeometry.Scheme.AdicFibreComparison

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] [hl : Fact (l ≠ D.p)]
  (Ω : Type u) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
  (Y₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
  [IsSeparated Y₀.hom]


/-- Finite coefficient compatibility with the normalized derived scalar comparison.
A comparison under J is fixed by its image under the faithful continuous realization;
its image must be the composite of the recorded, normalized sf and PBC scalar maps.
Source: BS 6.8.14(2), Remark 6.8.15
(blueprint: def-zl-classical-two-fibre-scalar-data). -/
structure Scalars (a : LisseRealization.Family D l hl.out) (R : ContinuousRational.Family.{u} l)
    (C : FdCoefficientComparison l Ω (D.geometricFiber Y₀).left)
    (ω : Fibres (k := D.k) l R) (c : AllComparisons l R ω)
    (S : ∀ E, AtStage D l Ω Y₀ E a R C ω) where
  square : ∀ (E L : Padic.FiniteCoefficientFields l Ω) (h : E ≤ L)
      (K : (rationalLisseHeartProperty l (pbcFiniteField.{u} l Ω E)
        (D.geometricFiber Y₀).left).FullSubcategory)
      (H : (rationalLisseHeartProperty l (pbcFiniteField.{u} l Ω L)
        (D.geometricFiber Y₀).left).FullSubcategory)
      (e : (sfRationalScalarExtension l (pbcFiniteField.{u} l Ω E)
        (D.geometricFiber Y₀).left 0 (Nat.Prime.ne_zero (Fact.out : l.Prime))
        (pbcFiniteField.{u} l Ω L) (pbcFiniteFieldInclusion l Ω h)).obj K.obj ≅ H.obj)
      (eD : (sfRationalScalarExtension l (pbcFiniteField.{u} l Ω E)
        (D.geometricFiber Y₀).left D.p hl.out
        (pbcFiniteField.{u} l Ω L) (pbcFiniteFieldInclusion l Ω h)).obj K.obj ≅ H.obj)
      (_he : HEq e.hom eD.hom)
      (b : LisseRealization.FieldNormalized D l hl.out (pbcFiniteField.{u} l Ω E)
        (pbcFiniteField.{u} l Ω L) (pbcFiniteFieldInclusion l Ω h)
        (zlRealizationBase D l hl.out Y₀) (a.realization _ _) (a.realization _ _)
        (a.fieldChange _ _ (pbcFiniteFieldInclusion l Ω h) _))
      (_hc : (a.fieldChange (pbcFiniteField.{u} l Ω E) (pbcFiniteField.{u} l Ω L)
        (pbcFiniteFieldInclusion l Ω h) (zlRealizationBase D l hl.out Y₀)).coefficient =
          (R.fieldChange (pbcFiniteField.{u} l Ω E) (pbcFiniteField.{u} l Ω L)
            (pbcFiniteFieldInclusion l Ω h) (base l (geometricBase D l Y₀))).coefficient)
      (j : (heartScalar l (pbcFiniteField.{u} l Ω E) (pbcFiniteField.{u} l Ω L)
        (pbcFiniteFieldInclusion l Ω h) (geometricBase D l Y₀)).obj
          (((S E).toStage.heartFunctor D l Ω Y₀ E).obj K) ≅
        ((S L).toStage.heartFunctor D l Ω Y₀ L).obj H)
      (_hj : HEq
        ((R.realization (pbcFiniteField.{u} l Ω L) (base l (geometricBase D l Y₀))).J.map
          j.hom.hom ≫ (S L).realization.hom.app H.obj ≫
          (a.realization (pbcFiniteField.{u} l Ω L) (zlRealizationBase D l hl.out Y₀)).J.map
            eD.inv ≫ b.derived.hom.app K.obj)
        ((R.fieldChange (pbcFiniteField.{u} l Ω E) (pbcFiniteField.{u} l Ω L)
          (pbcFiniteFieldInclusion l Ω h) (base l (geometricBase D l Y₀))).comparison.hom.app
            (((S E).toStage.heartFunctor D l Ω Y₀ E).obj K).obj ≫
          (pbcDerivedExtend (R.fieldChange (pbcFiniteField.{u} l Ω E)
            (pbcFiniteField.{u} l Ω L) (pbcFiniteFieldInclusion l Ω h)
            (base l (geometricBase D l Y₀))).coefficient).map
              ((S E).realization.hom.app K.obj)))
      (x : Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left),
    (sfVector D l Ω Y₀ L x).map e.hom ≫ ((S L).fibres x).hom.app H ≫
      ((ω (pbcFiniteField.{u} l Ω L) (geometricBase D l Y₀)).point D.k x).functor.map j.inv ≫
      ((c (pbcFiniteField.{u} l Ω E) (pbcFiniteField.{u} l Ω L)).scalar
        (pbcFiniteFieldInclusion l Ω h) (geometricBase D l Y₀) D.k x).hom.app
          (((S E).toStage.heartFunctor D l Ω Y₀ E).obj K) =
    (finiteVectorScalar D l Ω Y₀ E L h x K.obj).hom ≫
      (ModuleCat.extendScalars (pbcFiniteFieldInclusion l Ω h).toRingHom).map
        (((S E).fibres x).hom.app K)

end WeilConjectures.ClassicalTwoFibre
