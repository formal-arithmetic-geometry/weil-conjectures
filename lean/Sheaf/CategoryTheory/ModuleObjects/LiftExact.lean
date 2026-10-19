/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NE
-/
module

public import WeilConjectures.CategoryTheory.Monoidal.Mod.Abelian
public import Mathlib.CategoryTheory.Limits.ExactFunctor

/-!
# Exactness of lifts to module objects

Source: the Weil conjectures blueprint, main-20261015, chapter `sec-proetale-coefficients`,
unit `sk-prop-sfb-module-pullback-exact`, detail lemma
`det-prop-sfb-module-pullback-exact-lifted`
(blueprint: det-prop-sfb-module-pullback-exact-lifted).
-/

@[expose] public section

universe v₁ v₂ u₁ u₂

open CategoryTheory MonoidalCategory Limits

namespace CategoryTheory.Mod

/-- Source: main-20261015 blueprint, `sec-proetale-coefficients`,
`sk-prop-sfb-module-pullback-exact`, detail lemma on lifts of exact functors
(blueprint: det-prop-sfb-module-pullback-exact-lifted).
A lift commuting with the forgetful functors of an additive exact functor is additive and exact.

Proof plan:
1. Right exactness of `tensorLeft R` and `tensorLeft S` gives abelian module categories by
   lem-sfb-modobj-abelian. Sums, zero and negatives of module maps are inherited from the
   ambient categories because tensoring is additive. Thus both forgetful functors are additive.
   The equality of composites and additivity of `F` show that the underlying maps of
   `G.map (a + b)` and `G.map a + G.map b` agree. Faithfulness
   (lem-sfb-modobj-forget-faithful) gives additivity of `G`, hence preservation of zero maps.
2. By lem-sfb-modobj-kernels and lem-sfb-modobj-cokernels the source forgetful functor
   preserves kernels and cokernels: compare any chosen module kernel or cokernel with the
   constructed one by their universal properties. The comparison is a module isomorphism,
   hence also an underlying isomorphism.
3. The target forgetful functor reflects kernels. Given a factorization `k ≫ phi = 0` with
   underlying `k` a kernel, an underlying lift `u` of a module map `psi` satisfies the module
   equation after postcomposition with `k`. Use the module equations of `k` and `psi` and
   cancel the monomorphism `k`. The lift is linear, and underlying uniqueness gives uniqueness.
4. It reflects cokernels as well. For an underlying factorization through a cokernel `q`,
   the module equation for its factor `u` holds after precomposition with `S ◁ q`.
   Right exactness preserves the finite coequalizer of the original map and zero, and
   additivity identifies its image with a cokernel. Hence `S ◁ q` is epic. Cancel it to
   obtain linearity of `u`; underlying uniqueness gives the module cokernel property.
5. Apply exactness of `F` to the underlying kernels and cokernels from step 2. The equality
   of composites identifies their images with the underlying images under `G`. The zero
   composites follow from step 1, so steps 3 and 4 show that `G` preserves kernels and cokernels.
6. Apply lem-sfb-kernel-cokernel-finite-exactness to the additive functor `G` between the
   abelian module categories. It preserves finite limits and finite colimits, which is exactly
   exactness in def-galois-exact-functor. Together with step 1 this proves all the clauses. -/
theorem lift_additive_exact
    {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
    [Abelian C] [Abelian D] [MonoidalCategory C] [MonoidalCategory D]
    [MonoidalPreadditive C] [MonoidalPreadditive D]
    (R : C) (S : D) [MonObj R] [MonObj S]
    [PreservesFiniteColimits (tensorLeft R)] [PreservesFiniteColimits (tensorLeft S)]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (G : Mod C R ⥤ Mod D S)
    (h : G ⋙ Mod.forget S = Mod.forget R ⋙ F) :
    G.Additive ∧ PreservesFiniteLimits G ∧ PreservesFiniteColimits G := by
  have : (G ⋙ Mod.forget S).Additive := by
    rw [h]
    infer_instance
  have : PreservesFiniteLimits (G ⋙ Mod.forget S) := by
    rw [h]
    infer_instance
  have : PreservesFiniteColimits (G ⋙ Mod.forget S) := by
    rw [h]
    infer_instance
  exact ⟨Functor.additive_of_comp_faithful G (Mod.forget S),
    preservesFiniteLimits_of_reflects_of_preserves G (Mod.forget S),
    preservesFiniteColimits_of_reflects_of_preserves G (Mod.forget S)⟩

end CategoryTheory.Mod

