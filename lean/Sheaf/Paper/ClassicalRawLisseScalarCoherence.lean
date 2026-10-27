/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N9
-/
module

public import Sheaf.Paper.ClassicalRawLisseOperations

/-! # Coherent operations on classical raw lisse realizations

Source: BS 6.8.4, 6.8.14, 6.8.15
(blueprint: def-zl-classical-raw-lisse-scalar-coherence).
## Main definitions

* `ScalarCoherence`: the normalized scalar unit and associator equations.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async true
set_option genCtorIdx false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
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

variable (F : Type u) [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]

/-- Raw coherence is characterized through the faithful prescribed sf realization.
The scalar compositor is exactly the existing normalized balanced tensor associator.
Source: BS 6.8.4(4), 6.8.15 (blueprint: def-zl-classical-raw-lisse-scalar-coherence). -/
structure ScalarCoherence (a : LisseRealization.Family D l hl)
    (b : ContinuousRational.Family.{u} l) (s : Family D l hl a b)
    (o : Operations D l hl a b s) where
  scalarId (A : Type u) [Field A] [Algebra ℚ_[l] A] [FiniteDimensional ℚ_[l] A]
      (X : PerAdic.Base D.k) : (o.scalar A A X (AlgHom.id _ _)).raw ≅
        𝟭 (Rational D l A X)
  scalarId_normalization (A : Type u) [Field A] [Algebra ℚ_[l] A]
      [FiniteDimensional ℚ_[l] A] (X : PerAdic.Base D.k) :
    HEq (Functor.whiskerRight (scalarId A X).hom
      ((s.raw A X).raw ⋙ (sfRationalHeartProperty l A X.scheme).ι))
      ((o.scalar A A X (AlgHom.id _ _)).comparison.inv ≫
        Functor.whiskerLeft ((s.raw A X).raw ⋙ (sfRationalHeartProperty l A X.scheme).ι)
          (sfRationalScalarUnit l A X.scheme D.p hl).hom)
  scalarComp (A B C : Type u) [Field A] [Field B] [Field C]
      [Algebra ℚ_[l] A] [Algebra ℚ_[l] B] [Algebra ℚ_[l] C]
      [FiniteDimensional ℚ_[l] A] [FiniteDimensional ℚ_[l] B]
      [FiniteDimensional ℚ_[l] C] (X : PerAdic.Base D.k)
      (i : A →ₐ[ℚ_[l]] B) (j : B →ₐ[ℚ_[l]] C) :
    (o.scalar A B X i).raw ⋙ (o.scalar B C X j).raw ≅ (o.scalar A C X (j.comp i)).raw
  scalarComp_normalization (A B C : Type u) [Field A] [Field B] [Field C]
      [Algebra ℚ_[l] A] [Algebra ℚ_[l] B] [Algebra ℚ_[l] C]
      [FiniteDimensional ℚ_[l] A] [FiniteDimensional ℚ_[l] B]
      [FiniteDimensional ℚ_[l] C] (X : PerAdic.Base D.k)
      (i : A →ₐ[ℚ_[l]] B) (j : B →ₐ[ℚ_[l]] C) :
    HEq (Functor.whiskerRight (scalarComp A B C X i j).hom
      ((s.raw C X).raw ⋙ (sfRationalHeartProperty l C X.scheme).ι))
      (Functor.whiskerLeft (o.scalar A B X i).raw (o.scalar B C X j).comparison.inv ≫
        Functor.whiskerRight (o.scalar A B X i).comparison.inv
          (sfRationalScalarExtension l B X.scheme D.p hl C j) ≫
        Functor.whiskerLeft ((s.raw A X).raw ⋙ (sfRationalHeartProperty l A X.scheme).ι)
          (sfRationalScalarComp l A B i X.scheme D.p hl C j).hom ≫
        (o.scalar A C X (j.comp i)).comparison.hom)


end WeilConjectures.ClassicalRawLisse
