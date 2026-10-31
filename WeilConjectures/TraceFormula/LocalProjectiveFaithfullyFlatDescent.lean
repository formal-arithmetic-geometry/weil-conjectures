/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import Mathlib.Algebra.Module.Projective
public import Mathlib.LinearAlgebra.TensorProduct.Basic
import WeilConjectures.LinearAlgebra.CountableSubmoduleAdaptedToBaseChangeSum
import WeilConjectures.RingTheory.CountableProjectiveFaithfullyFlatDescent
import WeilConjectures.RingTheory.ProjectiveCountableDecomposition

/-!
# Projectivity descends along faithfully flat maps

Source: literature/stacks-project/algebra.tex, Tag 05A9, theorem-ffdescent-projectivity
(blueprint: lem-trf-local-projective-faithfully-flat-descent)

## Main statement

* `Module.projective_of_faithfullyFlat`: projectivity of a scalar extension descends
  along a faithfully flat ring map.
-/

@[expose] public section

set_option autoImplicit false

open scoped TensorProduct

namespace Module

universe u v w

/--
Projectivity descends along a faithfully flat ring homomorphism.

Source: literature/stacks-project/algebra.tex, Tag 05A9, theorem-ffdescent-projectivity
(blueprint: lem-trf-local-projective-faithfully-flat-descent).
The proof uses the countable projective decomposition and adapted-submodule lemmas
`lem-trf-projective-countable-decomposition` and
`lem-trf-countable-submodule-adapted-to-base-change-sum`, flat tensor exactness and
right exactness, the projective splitting and direct-summand lemmas, and the
well-ordering theorem.  A transfinite filtration of the module has countably
generated projective successive quotients; splitting these quotients expresses the
module as a direct sum of projectives, hence as a projective module.
-/
theorem projective_of_faithfullyFlat (A : Type u) (B : Type v) (M : Type w)
    [CommRing A] [CommRing B] [AddCommGroup M]
    [Algebra A B] [Module A M]
    (hff : (algebraMap A B).FaithfullyFlat)
    (hproj : Module.Projective B (B ⊗[A] M)) : Module.Projective A M := by
  sorry

end Module
