/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q5
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective

/-! # Affine shrinking downstairs under a finite radicial map

Source: Stacks Project, More on Morphisms, Tag 0GK7, shrinking finite base covers.
-/

@[expose] public section
universe u
open CategoryTheory
namespace AlgebraicGeometry

/-- An open neighbourhood on a finite radicial cover contains the inverse image of an
affine open neighbourhood downstairs.
Source: Stacks Project, Tag 0GK7, the shrinking of finite radicial base covers.
(blueprint: lem-weil-pbc-finite-radicial-affine-shrinking)

Proof: The image of the closed complement of O is closed because g is finite.
It misses g(x), since g is injective and x lies in O. Choose an affine open
neighbourhood U of g(x) inside its open complement. Every point over U lies in O,
by the definition of that complement. No Noetherian or irreducibility assumption
is used, and g need not be surjective. -/
theorem exists_affine_shrinking_under_finite_radicial
    {V S : Scheme.{u}} (g : V ⟶ S) [IsFinite g] [UniversallyInjective g]
    (x : V) (O : V.Opens) (hx : x ∈ O) :
    ∃ U : S.Opens, IsAffineOpen U ∧ g x ∈ U ∧ g ⁻¹ᵁ U ≤ O := by
  let W : S.Opens := ⟨(g '' (O : Set V)ᶜ)ᶜ,
    (g.isClosedMap _ O.isOpen.isClosed_compl).isOpen_compl⟩
  have hxW : g x ∈ W := by
    rintro ⟨y, hy, heq⟩
    exact hy ((g.injective heq).symm ▸ hx)
  obtain ⟨U, hU, hxU, hUW⟩ := exists_isAffineOpen_mem_and_subset
    (X := S) (x := g x) (U := W) hxW
  refine ⟨U, hU, hxU, ?_⟩
  intro y hy
  by_contra hn
  exact (hUW hy) ⟨y, hn, rfl⟩

end AlgebraicGeometry
