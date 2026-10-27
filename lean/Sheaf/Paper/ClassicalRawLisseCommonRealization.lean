/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N9
-/
module

public import Sheaf.Paper.ClassicalRawLisseCommonSystem

/-! # Coherent operations on classical raw lisse realizations

Source: BS 6.8.4, 6.8.14, 6.8.15
(blueprint: def-zl-classical-raw-lisse-common-realization).
## Main definitions

* `CommonRealization`: the stage morphism, common heart and Hom bijections.
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

/-- The common-stage realization, with its transition and Hom-colimit formulas.
Source: BS 6.8.4(4) (blueprint: def-zl-classical-raw-lisse-common-realization). -/
structure CommonRealization (a : LisseRealization.Family D l hl)
    (b : ContinuousRational.Family.{u} l) (s : Family D l hl a b)
    (o : Operations D l hl a b s) (c : ScalarCoherence D l hl a b s o) extends
      CommonSystem D l hl W Ω a b s o c where
  realization : system.Morphism (GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω W.scheme)
  stages (i : AlgebraicallyClosedCoefficients.Index l Ω) :
    realization.Φ i = (s.raw (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω i) W).raw ⋙
      (sfRationalHeartProperty l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω i) W.scheme).ι
  scalar_comparison {i j : AlgebraicallyClosedCoefficients.Index l Ω} (h : i ≤ j) :
    HEq (realization.β h).hom
      ((o.scalar (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω i)
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω j) W
          (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω i j h)).comparison.hom)
  heart (M : system.PairCategory) :
    sfCommonStageHeartProperty l W.scheme Ω (realization.functor.obj M)
  fullyFaithful : realization.functor.FullyFaithful


end WeilConjectures.ClassicalRawLisse
