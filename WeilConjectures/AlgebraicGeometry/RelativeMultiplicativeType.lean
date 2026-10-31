/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RingDiagonalizableGroup
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
public import Mathlib.GroupTheory.Finiteness

/-! # Groups of multiplicative type over arbitrary bases

Source: Conrad, Reductive group schemes, Definition B.1.1, printed p.280.
(blueprint: def-sfb-relative-multiplicative-type).

We use affine refinements of the fppf splitting cover, so that each diagonalizable
model is exactly the previously defined ringDiagonalizableGroup.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A group scheme of multiplicative type admits an fppf affine splitting cover,
with finitely generated abelian character groups. Affine refinement gives precisely
Conrad's fppf-local definition, and imposes no affineness assumption on the base.
Each isomorphism preserves multiplication, unit and inverse, since it is in Grp.
Source: Conrad, Reductive group schemes, Definition B.1.1, printed p.280
(blueprint: def-sfb-relative-multiplicative-type). -/
def IsRelativeMultiplicativeType {S : Scheme.{u}} (P : Grp (Over S)) : Prop :=
  ∃ (I : Type u) (R : I → CommRingCat.{u}) (f : ∀ i, Spec (R i) ⟶ S),
    Presieve.ofArrows (fun i ↦ Spec (R i)) f ∈ Scheme.fppfPrecoverage S ∧
    ∀ i : I, ∃ (M : Type u) (_ : AddCommGroup M) (_ : AddGroup.FG M),
      Nonempty ((Over.pullback (f i)).mapGrp.obj P ≅ ringDiagonalizableGroup (R i) M)

end AlgebraicGeometry
