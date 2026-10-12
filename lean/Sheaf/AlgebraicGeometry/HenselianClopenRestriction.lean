/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N1
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.RingTheory.Henselian

/-!
# Clopen restriction to a proper henselian closed fibre

Source: Stacks Project, Tag 0A0B, applied to locally constant two-valued functions.
(blueprint: lem-weil-pbc-henselian-clopen-restriction)
-/

@[expose] public section
universe u
open CategoryTheory Limits
namespace AlgebraicGeometry

/-- Restriction to the closed fibre is injective and surjective on clopen subsets.
Source: Stacks Project, Etale Cohomology, Lemma 59.91.1, Tag 0A0B.
(blueprint: lem-weil-pbc-henselian-clopen-restriction)

Proof: The quotient spectrum morphism is a closed immersion, and so is its base change
`i`. Thus it identifies `Y₀` with the closed subset `T` of `Y`. Apply Tag 0A0B to the
sheaf of locally constant functions into the discrete set `{0,1}` on `Y`. Its global
sections are the characteristic functions of clopen subsets. Its inverse image to `T`
is the same sheaf of locally constant two-valued functions: locally any such function
is constant, extends by that constant near each point, and the local extensions agree
as germs and glue after sheafification. The bijection on sections is restriction of
functions, hence intersection of clopens with `T`. Transport by the homeomorphism
`Y₀ ≃ T` gives inverse image along `i`. Injectivity gives the first clause, while
surjectivity gives the clopen lift in the second. Empty schemes and empty clopens are
included: the unique characteristic function on the empty space corresponds to its
unique clopen subset. -/
theorem Scheme.henselian_clopen_restriction
    {A : Type u} [CommRing A] (I : Ideal A) [HenselianRing A I]
    {Y Y₀ : Scheme.{u}} (f : Y ⟶ Spec (.of A)) [IsProper f] (i : Y₀ ⟶ Y)
    (f₀ : Y₀ ⟶ Spec (.of (A ⧸ I)))
    (h : IsPullback i f₀ f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))) :
    (∀ U V : Set Y, IsOpen U ∧ IsClosed U → IsOpen V ∧ IsClosed V →
      i.base ⁻¹' U = i.base ⁻¹' V → U = V) ∧
    (∀ V : Set Y₀, IsOpen V ∧ IsClosed V →
      ∃ U : Set Y, (IsOpen U ∧ IsClosed U) ∧ i.base ⁻¹' U = V) := by sorry

end AlgebraicGeometry
