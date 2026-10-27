/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N9
-/
module

public import Sheaf.Paper.ClassicalRawLisseCommonRealization

/-! # Coherent operations on classical raw lisse realizations

Source: BS 6.8.4, 6.8.14, 6.8.15
(blueprint: def-zl-classical-raw-lisse-common-fibres).
## Main definitions

* `CommonRealization` and `Common`: the common-stage realization and normalized fibre.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async true
set_option genCtorIdx false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option genSizeOfSpec false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u v
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale
open scoped TensorProduct
namespace WeilConjectures.ClassicalRawLisse
variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
variable (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (W : PerAdic.Base D.k)

variable (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]

/-- The common-stage fibre comparison after ordinary coefficient extension.
Source: BS 6.8.15 (blueprint: def-zl-classical-raw-lisse-common-fibres). -/
structure Common (a : LisseRealization.Family D l hl)
    (b : ContinuousRational.Family.{u} l) (s : Family D l hl a b)
    (o : Operations D l hl a b s) (c : ScalarCoherence D l hl a b s o) extends
      CommonRealization D l hl W Ω a b s o c where
  fibre (x : Spec (.of D.k) ⟶ W.scheme) :
    generalAlgebraicallyClosedConstructibleCategory l Ω W.scheme ⥤ ModuleCat.{max (u + 1) v} Ω
  fibre_spec (x : Spec (.of D.k) ⟶ W.scheme) :
    SfAdicCommonFiberSpec l W.scheme x Ω (fibre x)
  finite (x : Spec (.of D.k) ⟶ W.scheme)
      (i : AlgebraicallyClosedCoefficients.Index l Ω) :
    GeneralAlgebraicallyClosedCoefficients.inclusion i ⋙ fibre x ≅
      sfAdicRationalFiber l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω i) W.scheme x ⋙
        ModuleCat.extendScalars (sfAdicCoefficientEmbedding.{u} l Ω i)
  classical_fibre (x : Spec (.of D.k) ⟶ W.scheme)
      (i : AlgebraicallyClosedCoefficients.Index l Ω)
      (M : Rational D l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω i) W) :
    (fibre x).obj (realization.functor.obj ((system.ι i).obj M)) ≅
      (ModuleCat.extendScalars.{u, v, u + 1} (sfAdicCoefficientEmbedding.{u} l Ω i)).obj
        (classicalFibre D l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω i) W M.obj x)

  classical_normalization (x : Spec (.of D.k) ⟶ W.scheme)
      (i : AlgebraicallyClosedCoefficients.Index l Ω)
      (M : Rational D l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω i) W) :
    HEq (classical_fibre x i M).hom
      ((finite x i).hom.app ((s.raw
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω i) W).raw.obj M).obj ≫
        (ModuleCat.extendScalars.{u, v, u + 1} (sfAdicCoefficientEmbedding.{u} l Ω i)).map
          ((s.finite (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω i) W).fibre x M).hom)


end WeilConjectures.ClassicalRawLisse
