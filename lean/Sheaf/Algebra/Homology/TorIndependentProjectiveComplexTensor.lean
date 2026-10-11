/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J1
-/
import Sheaf.Algebra.Homology.BaseDerivedTensorCohomologyModel
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import Mathlib.Algebra.Module.Projective
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.CategoryTheory.Monoidal.Tor
import Mathlib.RingTheory.Localization.Basic
/-!
# Tor-independent tensor comparison for a bounded projective complex

Source: Stacks Project, perfect.tex, Tag 08IB, lemma-compare-base-change
(blueprint: lem-pc-tor-independent-projective-complex-tensor).
-/

set_option autoImplicit false

universe uR₁ uA₁ uB₁ uD₁ v₁ w₁

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace ModuleCat

/-- (blueprint: lem-pc-tor-independent-projective-complex-tensor) Stacks Project,
Tag 08IB, local affine Tor-independent tensor comparison.

Proof: finite projective A-modules are summands of finite free modules. By
`lem-pc-finite-projective-tor-acyclic`, Tor-independence of A and B therefore
implies higher Tor vanishing for each term of Q. Apply
`lem-pc-termwise-tor-acyclic-derived-tensor` to identify the derived-to-ordinary
comparison on cohomology. Localization is flat by
`lem-weil-pbc-localization-flat`. By `lem-weil-pbc-flat-tensor-exact`, tensoring
with D preserves the kernel/image sequences defining ordinary cohomology.
Consequently cohomology commutes with this tensor. Tensor associativity identifies
(Q tensor_R B) tensor_E D with Q tensor_A D, compatibly with differentials.
The equations in `BaseDerivedTensorCohomologyModel` identify the displayed map
with precisely the composite of these isomorphisms, so it is an isomorphism. -/
theorem torIndependent_projectiveComplex_tensor
    {R : Type uR₁} {A : Type uA₁} {B : Type uB₁} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B]
    [HasDerivedCategory.{w₁} (ModuleCat.{max uR₁ uA₁ uB₁ uD₁ v₁} R)]
    [HasDerivedCategory.{w₁} (ModuleCat.{max uR₁ uA₁ uB₁ uD₁ v₁} B)]
    (hTor : ∀ i : ℕ, 0 < i →
      IsZero (((CategoryTheory.Tor'
        (ModuleCat.{max uR₁ uA₁ uB₁ uD₁ v₁} (ULift.{max uR₁ uA₁ uB₁ uD₁ v₁} R)) i).obj
          (ModuleCat.of (ULift.{max uR₁ uA₁ uB₁ uD₁ v₁} R)
            (ULift.{max uR₁ uA₁ uB₁ uD₁ v₁} A))).obj
          (ModuleCat.of (ULift.{max uR₁ uA₁ uB₁ uD₁ v₁} R)
            (ULift.{max uR₁ uA₁ uB₁ uD₁ v₁} B))))
    (Q : CochainComplex (ModuleCat.{max uR₁ uA₁ uB₁ uD₁ v₁} A) ℤ)
    (hbounded : ∃ m n : ℤ, ∀ i : ℤ, i < m ∨ n < i → IsZero (Q.X i))
    (hprojective : ∀ i : ℤ, Module.Finite A (Q.X i) ∧ Module.Projective A (Q.X i))
    (D : Type uD₁) [CommRing D] [Algebra (A ⊗[R] B) D]
    (hlocalization : ∃ S : Submonoid (A ⊗[R] B), IsLocalization S D) :
    ∀ i : ℤ, IsIso ((baseDerivedTensorCohomologyModel R A B Q D).localizedComparison i) := by
  sorry

end ModuleCat
