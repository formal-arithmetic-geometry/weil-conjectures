/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F9
-/
module

public import Sheaf.Paper.ConstructibleExceptionalCompositor

/-! # The finite compact-support coefficient square

The left-adjoint square underlying exceptional coefficient compatibility.
Source: the finite coefficient clause of Verdier exchange, expanded Step 1
(blueprint: lem-sf-finite-compact-support-coefficient-square).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Functor
namespace WeilConjectures.FiniteCompactSupportCoefficientSquare
open ConstructibleExceptionalCoefficients ConstructibleExceptionalCompositor

attribute [local instance] ConstructibleExceptionalCoefficients.Scalar.commShift

/-- The normalized compact-support coefficient maps commute with the normalized
finite compactification compositor, before taking exceptional right mates.
Source: current blueprint, Verdier exchange, finite coefficient clause, expanded Step 1
(blueprint: lem-sf-finite-compact-support-coefficient-square).

Proof: include the finite-Tor categories fully faithfully into the ordinary derived
categories. The definitions of finiteAlpha and finiteLeft, together with
SixFunctorOperationDatum.finiteCompositionNormalization, identify their components
with the specified proper/open origin compositor, for every retained etale origin
of the input. QNormalized identifies each q with the proper counit mate followed
by the open tensor comparison; Scalar.realization identifies its scalar functor
with actual derived extension along a.map. For a quotient apply
lem-sf-compact-coefficient-composition. Transport its universal tensor presentations
through those three scalar realizations and the compactification comparisons;
naturality cancels the intermediate realization isomorphisms. For retained ramified
extension apply the finite-level clause of lem-coef-finite-free-compact-composition,
using the equality of the extended uniformizer ideal with the level-en ideal.
For successive changes use the scalar associator and the left coefficient cocycle
of lem-sf-constructible-exceptional-adjunction-coefficients. Substitute the two
already established squares; naturality of the second g comparison interchanges
the middle factors, giving the direct square. Identity scalar extension is the
unit-normalized tensor comparison. Thus induction over Allowed proves the result,
including identity changes and mixed finite changes. The full inclusions reflect
the equality. This argument uses derived tensor throughout, and retains all finite
Tor intervals; no flatness of a quotient is invoked. -/
theorem finiteCompactSupportCoefficientSquare
    {D : FiniteFieldDatum.{u}} (B : D.CoefficientDatum)
    {X Y Z : SixFunctorSpace D}
    [IsSeparated X.obj.hom] [IsSeparated Y.obj.hom] [IsSeparated Z.obj.hom]
    (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsSeparated f.hom.left] [LocallyOfFiniteType f.hom.left] [QuasiCompact f.hom.left]
    [IsSeparated g.hom.left] [LocallyOfFiniteType g.hom.left] [QuasiCompact g.hom.left]
    (P : System.{u} B.l B.Qbar D B.different (f := f.hom.left))
    (Q : System.{u} B.l B.Qbar D B.different (f := g.hom.left))
    (R : System.{u} B.l B.Qbar D B.different (f := (f ≫ g).hom.left))
    (cf : Compactification f.hom.left) (cg : Compactification g.hom.left)
    (cx : Compactification (f ≫ g).hom.left)
    (E L : FieldStage.{u} B.l) (n m : ℕ+)
    (S : SixFunctorOperationDatum D B E.carrier n n.pos)
    (S' : SixFunctorOperationDatum D B L.carrier m m.pos)
    (a : PurCompactSupport.Change ((RingStage.finite E n).coefficients B.l)
      ((RingStage.finite L m).coefficients B.l))
    (_ha : Allowed B.l (s := .finite E n) (t := .finite L m) a)
    (TX : Scalar.{u} B.l B.Qbar a X.obj.left) (TY : Scalar.{u} B.l B.Qbar a Y.obj.left)
    (TZ : Scalar.{u} B.l B.Qbar a Z.obj.left)
    (df : @Comparison.{u} B.l _ B.Qbar _ _ _ X.obj.left Y.obj.left
      (.finite E n) (.finite L m) (P.ring.operation cf (.finite E n))
      (P.ring.operation cf (.finite L m)) TX.functor TY.functor
      TX.commShift TY.commShift)
    (dg : @Comparison.{u} B.l _ B.Qbar _ _ _ Y.obj.left Z.obj.left
      (.finite E n) (.finite L m) (Q.ring.operation cg (.finite E n))
      (Q.ring.operation cg (.finite L m)) TY.functor TZ.functor
      TY.commShift TZ.commShift)
    (dx : @Comparison.{u} B.l _ B.Qbar _ _ _ X.obj.left Z.obj.left
      (.finite E n) (.finite L m) (R.ring.operation cx (.finite E n))
      (R.ring.operation cx (.finite L m)) TX.functor TZ.functor
      TX.commShift TZ.commShift)
    (_hf : QNormalized.{u} B.l B.Qbar cf a TX TY
      (P.ring.left cf (.finite E n)) (P.ring.left cf (.finite L m)) df)
    (_hg : QNormalized.{u} B.l B.Qbar cg a TY TZ
      (Q.ring.left cg (.finite E n)) (Q.ring.left cg (.finite L m)) dg)
    (_hx : QNormalized.{u} B.l B.Qbar cx a TX TZ
      (R.ring.left cx (.finite E n)) (R.ring.left cx (.finite L m)) dx) :
    @LeftCoefficientEquation D B X.obj.left Y.obj.left Z.obj.left
      (.finite E n) (.finite L m)
      (P.ring.operation cf (.finite E n)) (P.ring.operation cf (.finite L m))
      (Q.ring.operation cg (.finite E n)) (Q.ring.operation cg (.finite L m))
      (R.ring.operation cx (.finite E n)) (R.ring.operation cx (.finite L m))
      TX.functor TY.functor TZ.functor
      (Scalar.q B.l B.Qbar TX TY df) (Scalar.q B.l B.Qbar TY TZ dg)
      (Scalar.q B.l B.Qbar TX TZ dx)
      (finiteAlpha B f g P Q R E n S cf cg cx)
      (finiteAlpha B f g P Q R L m S' cf cg cx) := by
  sorry

end WeilConjectures.FiniteCompactSupportCoefficientSquare
