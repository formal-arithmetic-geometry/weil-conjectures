/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.TwistedPullbackScalarShifts

/-! # Composite canonical shifts of the twisted pullback routes

Source: blueprint sec-smooth-purity/sk-thm-purity-transport, purity transport,
shift clause of the base-change coherence
(blueprint: def-pur-twisted-pullback-composite-shifts).
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
open CategoryTheory CategoryTheory.Limits CategoryTheory.Endofunctor AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures.TwistedPullbackScalars
variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
  (i : E →ₐ[Padic l] L)
variable {X X' Y Y' : Scheme.{u}}
  [∀ x : X, Invertible (l : X.residueField x)]
  [∀ x : X', Invertible (l : X'.residueField x)]
  [∀ y : Y, Invertible (l : Y.residueField y)]
  [∀ y : Y', Invertible (l : Y'.residueField y)]



attribute [local irreducible] D rationalDerivedPullback

section Final
variable (Ω : Type u) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]

/-- Composed canonical shifts on two ordinary pullbacks.
Source: purity transport, shift clause
(blueprint: def-pur-twisted-pullback-composite-shifts). -/
@[instance_reducible] def twoPullShift (u : X' ⟶ X) (f : X ⟶ Y) : (U l E u f).CommShift ℤ :=
  composeShift (rationalDerivedPullback l E f) (rationalDerivedPullback l E u)
    (fieldRationalPullShift l E f) (fieldRationalPullShift l E u)

/-- Composed canonical shifts on the twisted pullback.
Source: purity transport, shift clause
(blueprint: def-pur-twisted-pullback-composite-shifts). -/
@[instance_reducible] def twistedPullShift (f : X ⟶ Y) (d : ℕ) (s : (D l E X d).CommShift ℤ) :
    (H l E f d).CommShift ℤ :=
  composeShift (rationalDerivedPullback l E f) (D l E X d)
    (fieldRationalPullShift l E f) s

/-- The shift on the upper-left route, with the canonical structures retained.
Source: purity transport, shift clause
(blueprint: def-pur-twisted-pullback-composite-shifts). -/
@[instance_reducible] def leftRouteShift (u : X' ⟶ X) (f : X ⟶ Y) (d : ℕ)
    (s : (D l E X d).CommShift ℤ) :
    (H l E f d ⋙ rationalDerivedPullback l E u).CommShift ℤ :=
  composeShift (H l E f d) (rationalDerivedPullback l E u)
    (twistedPullShift l E f d s) (fieldRationalPullShift l E u)

/-- The shift on the lower-right route, with the canonical structures retained.
Source: purity transport, shift clause
(blueprint: def-pur-twisted-pullback-composite-shifts). -/
@[instance_reducible] def rightRouteShift (f' : X' ⟶ Y') (v : Y' ⟶ Y) (d : ℕ)
    (s : (D l E X' d).CommShift ℤ) :
    (rationalDerivedPullback l E v ⋙ H l E f' d).CommShift ℤ :=
  composeShift (rationalDerivedPullback l E v) (H l E f' d)
    (fieldRationalPullShift l E v) (twistedPullShift l E f' d s)

end Final
end WeilConjectures.TwistedPullbackScalars
