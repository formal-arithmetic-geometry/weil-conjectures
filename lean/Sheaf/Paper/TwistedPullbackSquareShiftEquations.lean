/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NH
-/
module
public import Sheaf.Paper.TwistedPullbackShiftCoherence

/-! # Shift equations of z, t and m in the twisted pullback square

Source: blueprint sec-smooth-purity/sk-thm-purity-transport, purity transport,
shifts of the whole base-change square
(blueprint: def-pur-twisted-pullback-square-shift-equations).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genCtorIdx false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.TwistedPullbackScalars

/-- The component shift equation for a fixed comparison, with both structures explicit.
Source: purity transport, shifts of the whole square
(blueprint: def-pur-twisted-pullback-square-shift-equations). -/
def ShiftNatural {A B : Type (u + 2)} [Category.{u + 2} A] [Category.{u + 2} B]
    [HasShift A ℤ] [HasShift B ℤ] {F G : A ⥤ B} (sF : F.CommShift ℤ) (sG : G.CommShift ℤ)
    (w : ∀ K : A, F.obj K ≅ G.obj K) : Prop :=
  ∀ (n : ℤ) (K : A), (w (K⟦n⟧)).hom ≫
      (Functor.commShiftIso G (self := sG) n).hom.app K =
    (Functor.commShiftIso F (self := sF) n).hom.app K ≫ (w K).hom⟦n⟧'

variable (l : ℕ) [Fact l.Prime]
  (Ω : Type u) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
  {X X' Y Y' : Scheme.{u}}
  [∀ x : X, Invertible (l : X.residueField x)]
  [∀ x : X', Invertible (l : X'.residueField x)]
  [∀ y : Y, Invertible (l : Y.residueField y)]
  [∀ y : Y', Invertible (l : Y'.residueField y)]
attribute [local irreducible] D rationalDerivedPullback

set_option maxHeartbeats 1000000 in
-- The three dependent component equations compare several nested pullback functors.
/-- Shift compatibility of z, the compositor square t, and the middle comparison m.
Together with the seven family shift equations these are the shift identifications
of (Z), (C), and (M), for every integer shift and with the common even shift 2d.
Source: purity transport, degree-zero line and no-extra-sign clause
(blueprint: def-pur-twisted-pullback-square-shift-equations). -/
def SquareShiftEquations (u : X' ⟶ X) (f : X ⟶ Y) (f' : X' ⟶ Y') (v : Y' ⟶ Y)
    (sq : u ≫ f = f' ≫ v) (d : ℕ) (s : ShiftCoherence l Ω u f f' v d) : Prop :=
  ∀ R : Fields l Ω,
    ShiftNatural
      (F := D l R.val X d ⋙ rationalDerivedPullback l R.val u)
      (G := rationalDerivedPullback l R.val u ⋙ D l R.val X' d)
      (composeShift (D l R.val X d) (rationalDerivedPullback l R.val u)
        (s.atX R).rationalShift (fieldRationalPullShift l R.val u))
      (twistedPullShift l R.val u d (s.atX' R).rationalShift) (z l R.val u d) ∧
    ShiftNatural (F := U l R.val u f) (G := V l R.val f' v)
      (twoPullShift l R.val u f) (twoPullShift l R.val f' v)
      (fun K ↦ (t l R.val u f f' v sq).app K) ∧
    ShiftNatural
      (F := H l R.val f d ⋙ rationalDerivedPullback l R.val u)
      (G := rationalDerivedPullback l R.val v ⋙ H l R.val f' d)
      (leftRouteShift l R.val u f d (s.atX R).rationalShift)
      (rightRouteShift l R.val f' v d (s.atX' R).rationalShift)
      (m l R.val u f f' v sq d)

end WeilConjectures.TwistedPullbackScalars
