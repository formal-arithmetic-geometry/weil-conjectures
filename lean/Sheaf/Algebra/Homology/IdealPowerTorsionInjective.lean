/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q04
-/
module

public import Sheaf.Algebra.Homology.IdealPowerTorsionFunctor
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.Algebra.Category.ModuleCat.Injective
import Mathlib.RingTheory.Filtration

/-!
# Ideal-power torsion of an injective module

Source: Stacks Project, dualizing.tex, Tag 08XW, assertion (2)
(blueprint: lem-per-ideal-torsion-preserves-injectives).
-/

@[expose] public section

universe u

namespace ModuleCat

/-- Over a commutative Noetherian ring, the ideal-power torsion submodule of any
injective module is injective. There is no finiteness assumption on the module.
The torsion object is the recorded functor, whose underlying submodule is
`Ideal.primaryComponent E K`: membership means that some natural-number power
of `K` annihilates the element, by `Ideal.primaryComponent_mem` and
`Submodule.mem_torsionBySet_iff`.

Source: Stacks Project, dualizing.tex, Tag 08XW (lemma-injective-module-divide), (2).
The following Baer--Artin--Rees argument is the node's agent-written proof plan.

Proof:
1. Put `T = Γ_K(E)`, using def-sbc-ideal-power-torsion-functor. By
   lem-sf-baer-criterion (`Module.Baer.iff_injective`), it suffices to extend each
   linear map `f : J → T` from an arbitrary ideal `J` to `A → T`. The equivalence
   `Module.injective_iff_injective_object` identifies module and categorical injectivity.
2. By def-weil-pbc-noetherian-ring, choose generators `j₁, ..., jᵣ` of `J`.
   Each `f(jᵢ)` is killed by `K ^ mᵢ`. Set `m = 1 + ∑ i, mᵢ`, also for an empty
   generating family. Then `K ^ m` annihilates every `f(j)` by linearity and
   `K ^ m ≤ K ^ mᵢ`. No finite generation of `E` is used.
3. Apply lem-weil-pbc-artin-rees (`Ideal.exists_pow_inf_eq_pow_smul`) to `J ≤ A`,
   with finite module `A` and ideal `K`. For its constant `c`, take `n = m + c`.
   It gives `J ∩ K ^ n ≤ K ^ m J`. The map `f` vanishes on the right by Step 2,
   hence on the intersection.
4. Compose `f` with `T → E`. On the sum ideal define `h(j + k) = f(j)` for
   `j ∈ J` and `k ∈ K ^ n`. Two decompositions differ by an element of
   `J ∩ K ^ n`, so Step 3 makes this well defined. Addition and scalar
   multiplication of decompositions show that `h` is linear; it extends `f`
   and is zero on `K ^ n`.
5. Injectivity of `E` and lem-sf-baer-criterion extend `h` to `g : A → E`.
   Put `e = g(1)`. For `a ∈ K ^ n`, `a e = g(a) = 0`, so `e ∈ T` by
   def-sbc-ideal-power-torsion-functor. Commutativity gives `b e ∈ T` for
   every `b ∈ A`. Thus `b ↦ b e` is a linear map `A → T` extending `f`.
6. Apply the converse direction of lem-sf-baer-criterion and the module/object
   injectivity equivalence to conclude that `T` is injective.
(blueprint: lem-per-ideal-torsion-preserves-injectives) -/
theorem idealPowerTorsion_obj_injective
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    (K : Ideal A) (E : ModuleCat.{u} A) [CategoryTheory.Injective E] :
    CategoryTheory.Injective ((idealPowerTorsion K).obj E) := by
  sorry

end ModuleCat
