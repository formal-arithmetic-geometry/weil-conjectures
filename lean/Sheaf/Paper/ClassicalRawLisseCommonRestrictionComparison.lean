/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N9
-/
module

public import Sheaf.Paper.ClassicalRawLisseCommonRestrictionData

/-! # Coherent operations on classical raw lisse realizations

Source: BS 6.8.4, 6.8.14, 6.8.15
(blueprint: def-zl-classical-raw-lisse-common-restriction-comparison).
## Main definitions

* `CommonRestrictionComparison`: actual descended restriction comparison.
* `restrictionFiniteLeft`, `restrictionFiniteRight`: the two finite comparison maps.
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
attribute [local irreducible] rationalDerivedPullback commonStageDerivedPullback

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
variable (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (W : PerAdic.Base D.k)

variable (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]

/-- The descended completed pullback comparison.
Source: BS 6.8.15 (blueprint: def-zl-classical-raw-lisse-common-restriction-comparison). -/
structure CommonRestrictionComparison (a : LisseRealization.Family D l hl)
    (b : ContinuousRational.Family.{u} l) (s : Family D l hl a b)
    (o : Operations D l hl a b s) (c : ScalarCoherence D l hl a b s o)
    (V : PerAdic.Base D.k)
    (f : V.scheme ⟶ W.scheme) [IsImmersion f]
    (cW : Common D l hl W Ω a b s o c) (cV : Common D l hl V Ω a b s o c) extends
      CommonRestrictionData D l hl W Ω a b s o c V f cW cV where
  comparison : cW.realization.functor ⋙
      @commonStageDerivedPullback l _ Ω _ _ _ V.scheme W.scheme f
        (baseInvertible D l hl V) (baseInvertible D l hl W) ≅
    restriction.functor ⋙ cV.realization.functor

/-- The actual finite component of the descended comparison.
Source: BS 6.8.15 (blueprint: def-zl-classical-raw-lisse-common-restriction-comparison). -/
def restrictionFiniteLeft (a : LisseRealization.Family D l hl)
    (b : ContinuousRational.Family.{u} l) (s : Family D l hl a b)
    (o : Operations D l hl a b s) (c : ScalarCoherence D l hl a b s o)
    (V : PerAdic.Base D.k)
    (f : V.scheme ⟶ W.scheme) [IsImmersion f]
    (cW : Common D l hl W Ω a b s o c) (cV : Common D l hl V Ω a b s o c)
    (data : CommonRestrictionComparison D l hl W Ω a b s o c V f cW cV)
    (i : AlgebraicallyClosedCoefficients.Index l Ω) :=
  (Functor.whiskerLeft
        (C := Rational D l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω i) W)
        (D := cW.system.PairCategory)
        (E := generalAlgebraicallyClosedConstructibleCategory l Ω V.scheme)
        (cW.system.ι i)
        (G := cW.realization.functor ⋙
          @commonStageDerivedPullback l _ Ω _ _ _ V.scheme W.scheme f
            (baseInvertible D l hl V) (baseInvertible D l hl W))
        (H := data.restriction.functor ⋙ cV.realization.functor) data.comparison.hom)

/-- The inclusion of the prescribed finite raw comparison.
Source: BS 6.8.15 (blueprint: def-zl-classical-raw-lisse-common-restriction-comparison). -/
def restrictionFiniteRight (a : LisseRealization.Family D l hl)
    (b : ContinuousRational.Family.{u} l) (s : Family D l hl a b)
    (o : Operations D l hl a b s) (c : ScalarCoherence D l hl a b s o)
    (V : PerAdic.Base D.k)
    (f : V.scheme ⟶ W.scheme) [IsImmersion f]
    (_cW : Common D l hl W Ω a b s o c) (_cV : Common D l hl V Ω a b s o c)
    (i : AlgebraicallyClosedCoefficients.Index l Ω) :=
  (Functor.whiskerRight
        (C := Rational D l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω i) W)
        (D := sfRationalConstructibleCategory l
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω i) V.scheme)
        (E := generalAlgebraicallyClosedConstructibleCategory l Ω V.scheme)
        (G := (s.raw (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω i) W).raw ⋙
          (sfRationalHeartProperty l
            (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω i) W.scheme).ι ⋙
          @rationalDerivedPullback l _
            (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω i) _ _ _
            V.scheme W.scheme f (baseInvertible D l hl V) (baseInvertible D l hl W))
        (H := (o.restriction (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω i)
          W V f).raw ⋙
          (s.raw (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω i) V).raw ⋙
          (sfRationalHeartProperty l
            (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω i) V.scheme).ι)
        (o.restriction (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω i)
          W V f).comparison.hom
        ((GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω V.scheme).ι i))


end WeilConjectures.ClassicalRawLisse
