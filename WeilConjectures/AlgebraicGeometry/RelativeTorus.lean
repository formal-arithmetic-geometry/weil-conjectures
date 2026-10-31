/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
public import Mathlib.Algebra.Category.Grp.Adjunctions
public import Mathlib.Algebra.Category.Grp.Limits

/-! # Tori over arbitrary scheme bases

Source: the relative torus convention in the independently formulated Raynaud quotient
lemma, Chapter IX, section 2; Stacks, Tag 022U, for the multiplicative group.
(blueprint: def-sfb-relative-torus).

The split group functor is a finite product of the units of global functions.
Its local identification is an isomorphism of group-valued functors, not just of sets.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- The rank-r split multiplicative group functor over an arbitrary scheme. Its sections
on V are r-tuples of units of Gamma(V, O_V), with componentwise multiplication; rank zero
is the terminal group. Source: Stacks, Tag 022U, and the relative torus convention
(blueprint: def-sfb-relative-torus). -/
def relativeSplitTorusFunctor (S : Scheme.{u}) (r : ℕ) : (Over S)ᵒᵖ ⥤ GrpCat.{u} :=
  ∏ᶜ fun _ : Fin r ↦
    (Over.forget S).op ⋙ Scheme.Γ ⋙ forget₂ CommRingCat CommMonCat ⋙
      CommMonCat.units ⋙ forget₂ CommGrpCat GrpCat

/-- A relative torus is fppf locally a split multiplicative group of finite rank.
The ranks may differ between covering members, so no constant-rank condition on the
whole base is imposed. Source: relative torus convention of the Raynaud quotient lemma,
Chapter IX, section 2; Stacks, Tag 022U (blueprint: def-sfb-relative-torus). -/
def IsRelativeTorus {S : Scheme.{u}} (T : Over S) [GrpObj T] : Prop :=
  ∃ (I : Type u) (U : I → Over S) (r : I → ℕ),
    Presieve.ofArrows (fun i ↦ (U i).left) (fun i ↦ (U i).hom) ∈
      Scheme.fppfPrecoverage S ∧
    ∀ i : I, Nonempty ((Over.map (U i).hom).op ⋙ yonedaGrpObj T ≅
      relativeSplitTorusFunctor (U i).left (r i))

end AlgebraicGeometry
