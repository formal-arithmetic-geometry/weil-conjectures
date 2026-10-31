/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Group.Affine
public import Mathlib.RingTheory.HopfAlgebra.MonoidAlgebra
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over

/-! # Split tori over commutative rings

Source: Alper--Halpern-Leistner--Heinloth, Cartan--Iwahori--Matsumoto decompositions,
Remark 3.5, p.5 (blueprint: def-sfb-split-torus-over-ring).

The Laurent Hopf algebra has coordinate z with comultiplication z ↦ z ⊗ z,
counit z ↦ 1 and antipode z ↦ z⁻¹. Its spectrum is the multiplicative group.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.MonoidalCategory

namespace AlgebraicGeometry.RingGroupSchemes

/-- The multiplicative group over a commutative ring, with its Laurent Hopf group law.
Source: AHLH, Remark 3.5, p.5 (blueprint: def-sfb-split-torus-over-ring). -/
def multiplicative (R : Type u) [CommRing R] : Grp (Over (Spec (.of R))) :=
  Grp.mk ((Spec (.of (LaurentPolynomial R))).asOver (Spec (.of R)))

/-- The product of r copies of the multiplicative group; rank zero is the trivial group.
Source: AHLH, Remark 3.5, p.5 (blueprint: def-sfb-split-torus-over-ring). -/
def splitTorus (R : Type u) [CommRing R] (r : ℕ) : Grp (Over (Spec (.of R))) :=
  Nat.rec (𝟙_ _) (fun _ T ↦ multiplicative R ⊗ T) r

end AlgebraicGeometry.RingGroupSchemes
