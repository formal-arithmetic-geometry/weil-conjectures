/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K2
-/
module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-!
# Spreading a closed immersion of a finite fibre

Source: Stacks Project, Tag 04DG, proof, the Nakayama and spreading-out steps.
(blueprint: lem-weil-pbc-finite-closed-immersion-near-fibre).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A finite morphism whose fibre at `s` is a closed immersion is a closed immersion
on some open neighbourhood of `s`.
Source: Stacks Project, Tag 04DG, proof, last two sentences (Nakayama and localization).
(blueprint: lem-weil-pbc-finite-closed-immersion-near-fibre).

Proof: Choose an affine neighbourhood `Spec A` of `s`, corresponding to a prime `p`.
The inverse image is `Spec B`, where `B` is finite as an `A`-module. The closed-immersion
hypothesis on the fibre says that `κ(p) → κ(p) ⊗[A] B` is surjective. Write `N` for the
image of `A → B` as an `A`-submodule of `B` and `Q = B / N`. Right exactness of tensor
product gives `κ(p) ⊗[A] Q = 0`. The module `Q` is finite, so Nakayama over the local ring
`A_p` gives `Q_p = 0`. Choose finitely many generators of `Q`. For each generator,
vanishing after localization gives an element outside `p` annihilating that generator.
Their product `a` is outside `p` and annihilates all of `Q`, so `Q_a = 0`. Thus `A_a → B_a`
is surjective. The principal open `D(a)` contains `s`, and the corresponding restriction
of the morphism is a closed immersion by the affine surjective-ring-map criterion.
This argument also handles an empty fibre: its ring is zero, the tensor product of `Q`
still vanishes, and Nakayama gives the same conclusion. -/
theorem exists_isClosedImmersion_restrict_of_fiber
    {X S : Scheme.{u}} (f : X ⟶ S) (s : S) [IsFinite f]
    (hf : IsClosedImmersion (f.fiberToSpecResidueField s)) :
    ∃ U : S.Opens, s ∈ U ∧ IsClosedImmersion (f ∣_ U) := by sorry

end AlgebraicGeometry
