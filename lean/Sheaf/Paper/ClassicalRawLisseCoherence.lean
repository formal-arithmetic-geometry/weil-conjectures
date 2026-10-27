/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N9
-/
module

public import Sheaf.Paper.ClassicalRawLisseScalarCoherence

/-! # Coherent operations on classical raw lisse realizations

Source: BS 6.8.4, 6.8.14, 6.8.15
(blueprint: def-zl-classical-raw-lisse-coherence).
## Main definitions

* `RestrictionCoherence` and `Coherence`: identity and composition equations.
* `Mixed`: compatibility of scalar extension and restriction.
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

/-- Restriction unit and composition, normalized by the actual ordinary pullback.
Source: BS 6.8.15 (blueprint: def-zl-classical-raw-lisse-coherence). -/
structure RestrictionCoherence (a : LisseRealization.Family D l hl)
    (b : ContinuousRational.Family.{u} l) (s : Family D l hl a b)
    (o : Operations D l hl a b s) where
  restrictionId (A : Type u) [Field A] [Algebra ℚ_[l] A]
      [FiniteDimensional ℚ_[l] A] (X : PerAdic.Base D.k) :
    (o.restriction A X X (𝟙 X.scheme)).raw ≅ 𝟭 (Rational D l A X)
  restrictionId_normalization (A : Type u) [Field A] [Algebra ℚ_[l] A]
      [FiniteDimensional ℚ_[l] A] (X : PerAdic.Base D.k) :
    HEq (Functor.whiskerRight (restrictionId A X).hom (s.finite A X).modules)
      ((o.restriction A X X (𝟙 X.scheme)).ordinary.inv ≫
        Functor.whiskerLeft (s.finite A X).modules
          (a.identity A (realizationBase D l hl X)).ordinary.hom)
  restrictionComp (A : Type u) [Field A] [Algebra ℚ_[l] A]
      [FiniteDimensional ℚ_[l] A] (X Y Z : PerAdic.Base D.k)
      (f : Y.scheme ⟶ X.scheme) (g : Z.scheme ⟶ Y.scheme)
      [IsImmersion f] [IsImmersion g] :
    (o.restriction A X Y f).raw ⋙ (o.restriction A Y Z g).raw ≅
      (o.restriction A X Z (g ≫ f)).raw
  restrictionComp_normalization (A : Type u) [Field A] [Algebra ℚ_[l] A]
      [FiniteDimensional ℚ_[l] A] (X Y Z : PerAdic.Base D.k)
      (f : Y.scheme ⟶ X.scheme) (g : Z.scheme ⟶ Y.scheme)
      [IsImmersion f] [IsImmersion g] :
    HEq (Functor.whiskerRight (restrictionComp A X Y Z f g).hom (s.finite A Z).modules)
      (Functor.whiskerLeft (o.restriction A X Y f).raw
          (o.restriction A Y Z g).ordinary.inv ≫
        Functor.whiskerRight (o.restriction A X Y f).ordinary.inv
          (LisseRealization.ordinaryPull l A g) ≫
        Functor.whiskerLeft (s.finite A X).modules
          (a.composition A (X := realizationBase D l hl Y)
            (Y := realizationBase D l hl X) (Z := realizationBase D l hl Z) f g).ordinary.inv ≫
        (o.restriction A X Z (g ≫ f)).ordinary.hom)

/-- The simultaneous scalar and restriction coherence datum.
Source: BS 6.8.15 (blueprint: def-zl-classical-raw-lisse-coherence). -/
structure Coherence (a : LisseRealization.Family D l hl)
    (b : ContinuousRational.Family.{u} l) (s : Family D l hl a b)
    (o : Operations D l hl a b s) extends ScalarCoherence D l hl a b s o,
      RestrictionCoherence D l hl a b s o

/-- Scalar extension commutes with locally closed restriction via the canonical
mixed balanced-tensor comparison. This fixes the comparison on every raw object.
Source: BS Remark 6.8.15
(blueprint: def-zl-classical-raw-lisse-coherence). -/
structure Mixed (a : LisseRealization.Family D l hl)
    (b : ContinuousRational.Family.{u} l) (s : Family D l hl a b)
    (o : Operations D l hl a b s) (i : E →ₐ[ℚ_[l]] F)
    (V : PerAdic.Base D.k) (f : V.scheme ⟶ W.scheme) [IsImmersion f] where
  comparison : (o.scalar E F W i).raw ⋙ (o.restriction F W V f).raw ≅
    (o.restriction E W V f).raw ⋙ (o.scalar E F V i).raw
  normalization :
    HEq (Functor.whiskerRight comparison.hom (s.finite F V).modules)
      (Functor.whiskerLeft (o.scalar E F W i).raw (o.restriction F W V f).ordinary.inv ≫
        Functor.whiskerRight (o.scalar E F W i).ordinary.inv
          (LisseRealization.ordinaryPull l F f) ≫
        Functor.whiskerLeft (s.finite E W).modules
          (a.mixed E F i (X := realizationBase D l hl V)
            (Y := realizationBase D l hl W) f).ordinary.hom ≫
        Functor.whiskerRight (o.restriction E W V f).ordinary.hom
          (pbcExtend (a.fieldChange E F i (realizationBase D l hl V)).coefficient) ≫
        Functor.whiskerLeft (o.restriction E W V f).raw (o.scalar E F V i).ordinary.hom)


end WeilConjectures.ClassicalRawLisse
