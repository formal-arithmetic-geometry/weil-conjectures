/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q05
-/
module

public import Sheaf.Paper.IntegralScalarExtension
public import Sheaf.Paper.IntegralScalarExtensionConstructible
public import Sheaf.Paper.RationalizationKaroubi

import Sheaf.Paper.ScalarExtensionComposition

/-! # Exactness of finite scalar extension

Source: blueprint `sec-smooth-purity/sk-prop-sf-pf-reduction`, order 1883
(blueprint: lem-weil-scalar-extension-exact-triangulated).
The shift comparison is specified on integral representatives, including its sign.
-/

@[expose] public section
set_option autoImplicit false

universe d u
open CategoryTheory TensorProduct

namespace WeilConjectures

variable (D : FiniteFieldDatum.{d}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (Y : AlgebraicGeometry.Scheme.{u})
  (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
  (ι : E →ₐ[Padic l] L)

/-- The full subcategory inherits the ordinary derived tensor shift comparison.
Source: blueprint order 1883 (blueprint: lem-weil-scalar-extension-exact-triangulated).
Proof: the ambient termwise exact tensor functor has its canonical derived shift
comparison. Full faithfulness of the inclusions lifts it uniquely. The ambient zero
and addition coherence equations imply the same equations after this lift. -/
theorem integralConstructibleScalarCommShift_existsUnique :
    ∃! c : (integralConstructibleScalarExtension D l hl E L ι Y).CommShift ℤ,
      (fun [commInst :
          (integralConstructibleScalarExtension D l hl E L ι Y).CommShift ℤ] ↦
        ∀ (n : ℤ) K,
          HEq (((integralConstructibleScalarExtension D l hl E L ι Y).commShiftIso n).hom.app K).hom
            (((integralOrdinaryDerivedScalar l E L ι Y).commShiftIso n).hom.app K.obj))
        (commInst := c) := by
  sorry

/-- The uniquely normalized integral shift comparison.
Source: blueprint order 1883 (blueprint: lem-weil-scalar-extension-exact-triangulated). -/
noncomputable instance integralConstructibleScalarCommShift :
    (integralConstructibleScalarExtension D l hl E L ι Y).CommShift ℤ :=
  (integralConstructibleScalarCommShift_existsUnique D l hl E Y L ι).exists.choose

/-- The rational shift comparison is the integral one tensored with one.
Source: blueprint order 1883 (blueprint: lem-weil-scalar-extension-exact-triangulated).
Proof: localize the integral shift comparison and inverse. Naturality on pure tensors
extends by additivity. The rational shift by one is the tensor-induced integral shift;
its localization comparison is the identity. Thus the displayed normalization holds.
Iteration and inverse shifts give a coherent comparison for every integer. A coherent
comparison for integer shifts is determined by its component at one, proving uniqueness. -/
theorem rationalOrdinaryScalarCommShift_existsUnique :
    ∃! c : (rationalOrdinaryScalarExtension D l hl E Y L ι).CommShift ℤ,
      (fun [commInst :
          (rationalOrdinaryScalarExtension D l hl E Y L ι).CommShift ℤ] ↦
        ∀ K, HEq
          (((rationalOrdinaryScalarExtension D l hl E Y L ι).commShiftIso (1 : ℤ)).hom.app K)
          ((1 : Localization.Away (Padic.coefficientExtensionUniformizer l L)) ⊗ₜ[
            Padic.coefficientExtensionIntegers l L]
            (((integralConstructibleScalarExtension D l hl E L ι Y).commShiftIso
              (1 : ℤ)).hom.app K.obj))) (commInst := c) := by
  sorry

/-- The normalized rational shift comparison.
Source: blueprint order 1883 (blueprint: lem-weil-scalar-extension-exact-triangulated). -/
noncomputable instance rationalOrdinaryScalarCommShift :
    (rationalOrdinaryScalarExtension D l hl E Y L ι).CommShift ℤ :=
  (rationalOrdinaryScalarCommShift_existsUnique D l hl E Y L ι).exists.choose

/-- Scalar extension preserves shifts and distinguished triangles.
Source: blueprint order 1883 (blueprint: lem-weil-scalar-extension-exact-triangulated).
Proof: finite free ordinary tensor is exact. Its canonical derived functor is therefore
triangulated. On complete objects it agrees with the fixed Roos construction by its
canonical augmentation, whose signed shift comparison is the same derived comparison.
Full integral constructible subcategories inherit distinguished triangles. Rational
triangles are exactly the isomorphic localization images of integral triangles; tensor
with one sends each such image to the localization of its exact integral image, including
the connecting arrow. This proves preservation of every distinguished triangle. -/
theorem rationalOrdinaryScalar_exact :
    (rationalOrdinaryScalarExtension D l hl E Y L ι).IsTriangulated := by
  sorry

/-- Additivity of the explicit tensor Hom map.
Source: blueprint order 1883 (blueprint: lem-weil-scalar-extension-exact-triangulated).
Proof: rationalScalarHom is an additive group homomorphism by its tensor construction. -/
theorem rationalOrdinaryScalar_additive :
    (rationalOrdinaryScalarExtension D l hl E Y L ι).Additive := by
  sorry

attribute [instance] rationalOrdinaryScalar_exact rationalOrdinaryScalar_additive

/-- The published completed functor carries the unique shift comparison making its
normalized comparison with ordinary tensor commute with every integer shift.
Source: blueprint order 1883 (blueprint: lem-weil-scalar-extension-exact-triangulated).
Proof: conjugate the ordinary derived tensor comparison by rationalOrdinaryComparison.
The ordinary comparison satisfies zero and addition coherence; naturality of the
conjugating isomorphism carries both equations to the completed functor. The displayed
commutation fixes every component uniquely, including the signed shift by one. -/
theorem rationalConstructibleScalarCommShift_existsUnique :
    ∃! c : (rationalScalarExtension D l hl E Y L ι).CommShift ℤ,
      (fun [commInst : (rationalScalarExtension D l hl E Y L ι).CommShift ℤ] ↦
        NatTrans.CommShift (rationalOrdinaryComparison D l hl E Y L ι).hom ℤ)
        (commInst := c) := by
  sorry

/-- The shift comparison transported through the canonical completion comparison.
Source: blueprint order 1883 (blueprint: lem-weil-scalar-extension-exact-triangulated). -/
noncomputable instance rationalConstructibleScalarCommShift :
    (rationalScalarExtension D l hl E Y L ι).CommShift ℤ :=
  (rationalConstructibleScalarCommShift_existsUnique D l hl E Y L ι).exists.choose

/-- The existing completed scalar functor is exact for its specified shift comparison.
Source: blueprint order 1883 (blueprint: lem-weil-scalar-extension-exact-triangulated).
Proof: ordinary finite free tensor is exact on sheaves and hence on derived complexes.
Restriction to the constructible full subcategories and rationalization preserve its
image triangles, proving rationalOrdinaryScalar_exact. The normalized natural
isomorphism rationalOrdinaryComparison commutes with the displayed shifts, so its
triangle isomorphisms transport preservation to the published completed functor. -/
theorem rationalConstructibleScalar_exact :
    (rationalScalarExtension D l hl E Y L ι).IsTriangulated := by
  sorry

/-- The published scalar functor is additive by its original tensor-Hom specification.
Source: blueprint order 1883 (blueprint: lem-weil-scalar-extension-exact-triangulated). -/
noncomputable instance rationalConstructibleScalar_additive :
    (rationalScalarExtension D l hl E Y L ι).Additive :=
  rationalScalarExtension_additive D l hl E Y L ι

attribute [instance] rationalConstructibleScalar_exact

end WeilConjectures
