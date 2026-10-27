/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q23
-/
module
public import Sheaf.Paper.SixFunctorOrientationFamily

/-! # Orientation as a component of a coherent family
Source: main-20261015, sec-six-functors/sk-def-sf-orientation/_section.md
(blueprint: sk-def-sf-orientation).
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

/-- An orientation is the component of a full coherent datum at f and the
finite coefficient stage, with its pullback-unit and root-line identifications.
The datum parameter retains every geometric, coefficient and affine condition.
Source: the displayed gamma isomorphism (blueprint: sk-def-sf-orientation). -/
def SixFunctorOrientation
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum} {E : Type u}
    [Field E] [Algebra (Padic C.l) E] [FiniteDimensional (Padic C.l) E] {m : ℕ}
    {S : SixFunctorDatum D C E (m + 1) (Nat.succ_le_succ (Nat.zero_le m))}
    (O : SfOrientationDatum S) {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    [IsSeparated f.hom.left] (d : ℕ) [SmoothOfRelativeDimension d f.hom.left]
    (c : Compactification f.hom.left) :
    sfOrientationReducedLine D C E m X d ≅
      (S.finite.exceptional f c).obj (sfOrientationReducedLine D C E m Y 0) :=
  O.primary.component f d c

/-- Evaluation at completed integral coefficients.
Source: the displayed gamma isomorphism (blueprint: sk-def-sf-orientation). -/
def SixFunctorOrientation.integralComponent
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum} {E : Type u}
    [Field E] [Algebra (Padic C.l) E] [FiniteDimensional (Padic C.l) E] {m : ℕ}
    {S : SixFunctorDatum D C E (m + 1) (Nat.succ_le_succ (Nat.zero_le m))}
    (O : SfOrientationDatum S) {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    [IsSeparated f.hom.left] (d : ℕ) [SmoothOfRelativeDimension d f.hom.left]
    (c : Compactification f.hom.left) :=
  O.higher.higher.integral.component f d c

/-- Evaluation at rational coefficients.
Source: the displayed gamma isomorphism (blueprint: sk-def-sf-orientation). -/
def SixFunctorOrientation.rationalComponent
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum} {E : Type u}
    [Field E] [Algebra (Padic C.l) E] [FiniteDimensional (Padic C.l) E] {m : ℕ}
    {S : SixFunctorDatum D C E (m + 1) (Nat.succ_le_succ (Nat.zero_le m))}
    (O : SfOrientationDatum S) {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    [IsSeparated f.hom.left] (d : ℕ) [SmoothOfRelativeDimension d f.hom.left]
    (c : Compactification f.hom.left) :=
  O.higher.higher.rational.component f d c

/-- Evaluation in the common finite-extension interpretation of Qbar coefficients.
Source: the displayed gamma isomorphism (blueprint: sk-def-sf-orientation). -/
def SixFunctorOrientation.commonComponent
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum} {E : Type u}
    [Field E] [Algebra (Padic C.l) E] [FiniteDimensional (Padic C.l) E] {m : ℕ}
    {S : SixFunctorDatum D C E (m + 1) (Nat.succ_le_succ (Nat.zero_le m))}
    (O : SfOrientationDatum S) {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    [IsSeparated f.hom.left] (d : ℕ) [SmoothOfRelativeDimension d f.hom.left]
    (c : Compactification f.hom.left) :=
  O.higher.common.component f d c

/-- For a smooth separated structure morphism the integral component, read
backwards, is omega_X isomorphic to the shifted d-th Tate line. The same reversal
applies to each of the other evaluation maps above.
Source: the final displayed formula (blueprint: sk-def-sf-orientation). -/
def SixFunctorOrientation.integralStructure
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum} {E : Type u}
    [Field E] [Algebra (Padic C.l) E] [FiniteDimensional (Padic C.l) E] {m : ℕ}
    {S : SixFunctorDatum D C E (m + 1) (Nat.succ_le_succ (Nat.zero_le m))}
    (O : SfOrientationDatum S) (X : SixFunctorSpace D) [IsSeparated X.obj.hom]
    (d : ℕ) [SmoothOfRelativeDimension d (sixFunctorStructure X).hom.left]
    (c : Compactification (sixFunctorStructure X).hom.left) :=
  letI : IsSeparated (sixFunctorStructure X).hom.left :=
    inferInstanceAs (IsSeparated X.obj.hom)
  (SixFunctorOrientation.integralComponent O (sixFunctorStructure X) d c).symm

/-- The finite structure-morphism orientation read backwards.
Source: the final displayed formula (blueprint: sk-def-sf-orientation). -/
def SixFunctorOrientation.finiteStructure
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum} {E : Type u}
    [Field E] [Algebra (Padic C.l) E] [FiniteDimensional (Padic C.l) E] {m : ℕ}
    {S : SixFunctorDatum D C E (m + 1) (Nat.succ_le_succ (Nat.zero_le m))}
    (O : SfOrientationDatum S) (X : SixFunctorSpace D) [IsSeparated X.obj.hom]
    (d : ℕ) [SmoothOfRelativeDimension d (sixFunctorStructure X).hom.left]
    (c : Compactification (sixFunctorStructure X).hom.left) :=
  letI : IsSeparated (sixFunctorStructure X).hom.left :=
    inferInstanceAs (IsSeparated X.obj.hom)
  (SixFunctorOrientation O (sixFunctorStructure X) d c).symm

/-- The rational structure-morphism orientation read backwards.
Source: the final displayed formula (blueprint: sk-def-sf-orientation). -/
def SixFunctorOrientation.rationalStructure
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum} {E : Type u}
    [Field E] [Algebra (Padic C.l) E] [FiniteDimensional (Padic C.l) E] {m : ℕ}
    {S : SixFunctorDatum D C E (m + 1) (Nat.succ_le_succ (Nat.zero_le m))}
    (O : SfOrientationDatum S) (X : SixFunctorSpace D) [IsSeparated X.obj.hom]
    (d : ℕ) [SmoothOfRelativeDimension d (sixFunctorStructure X).hom.left]
    (c : Compactification (sixFunctorStructure X).hom.left) :=
  letI : IsSeparated (sixFunctorStructure X).hom.left :=
    inferInstanceAs (IsSeparated X.obj.hom)
  (SixFunctorOrientation.rationalComponent O (sixFunctorStructure X) d c).symm

/-- The common structure-morphism orientation read backwards.
Source: the final displayed formula (blueprint: sk-def-sf-orientation). -/
def SixFunctorOrientation.commonStructure
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum} {E : Type u}
    [Field E] [Algebra (Padic C.l) E] [FiniteDimensional (Padic C.l) E] {m : ℕ}
    {S : SixFunctorDatum D C E (m + 1) (Nat.succ_le_succ (Nat.zero_le m))}
    (O : SfOrientationDatum S) (X : SixFunctorSpace D) [IsSeparated X.obj.hom]
    (d : ℕ) [SmoothOfRelativeDimension d (sixFunctorStructure X).hom.left]
    (c : Compactification (sixFunctorStructure X).hom.left) :=
  letI : IsSeparated (sixFunctorStructure X).hom.left :=
    inferInstanceAs (IsSeparated X.obj.hom)
  (SixFunctorOrientation.commonComponent O (sixFunctorStructure X) d c).symm

end WeilConjectures
