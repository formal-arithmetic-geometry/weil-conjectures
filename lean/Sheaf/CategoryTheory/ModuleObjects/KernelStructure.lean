/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q152
-/
module

public import WeilConjectures.CategoryTheory.Monoidal.Mod.Abelian

/-!
# The unique module structure on an underlying kernel

Source: Weil conjectures blueprint, main-20261015, `sec-proetale-coefficients`,
`sk-prop-sfb-module-category/lem-sfb-modobj-kernels.md` and its proof, paragraphs 1–2
(blueprint: lem-sfb-modobj-kernels).
-/

@[expose] public section

universe v u

open CategoryTheory MonoidalCategory Limits

namespace CategoryTheory.Mod

/-- An arbitrary underlying kernel of a module morphism has a unique compatible action,
and its inclusion is a kernel in the module category.

Source: Weil conjectures blueprint, main-20261015, `sec-proetale-coefficients`,
`sk-prop-sfb-module-category/lem-sfb-modobj-kernels.md`, proof paragraphs 1–2
(blueprint: lem-sfb-modobj-kernels).

Proof:
1. The underlying kernel universal property implies that its inclusion is monic: two
   arrows with equal composites are the unique lifts of that common composite.
2. Preadditivity (def-weil-preadditive-category) and additivity of tensoring
   (def-weil-pbc-additive-functor) give zero module maps. By the module-map equation
   (sk-def-sfb-module-objects), the composite of `R ◁ ι` with the action on `M`, then
   with `f.hom`, is the action on `N` after `R ◁ (ι ≫ f.hom)`, hence zero.
   The kernel property therefore gives a unique action arrow on `K` satisfying the equation.
3. Compose its unit equation with `ι`. Naturality of tensoring with the monoid unit,
   the unit law on `M`, and naturality of the left unitor identify the two sides.
   Cancel `ι` to obtain the unit law on `K` (sk-def-sfb-module-objects).
4. For associativity, compose with `ι`, move multiplication past `ι` by naturality,
   apply associativity on `M`, and move the associator past `ι` by naturality.
   Substitute the action equation and use functoriality of `R ◁ -`. Cancel `ι`.
   This proves associativity on `K`; the defining equation makes `ι` a module map.
5. Any module map `g` killed by `f` has a unique underlying lift through `ι`.
   Compose the proposed module-map equation for this lift with `ι`: the module-map
   equations for `g` and `ι`, and functoriality of tensoring, give equality. Cancel `ι`
   to show that the lift is linear. Underlying uniqueness and faithfulness of the
   forgetful functor give uniqueness as a module map, so the lifted fork is a kernel.
-/
theorem exists_kernel_module_structure
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [Preadditive C]
    [MonoidalPreadditive C] (R : C) [MonObj R]
    {M N : Mod C R} (f : M ⟶ N) {K : C} (ι : K ⟶ M.X)
    (w : ι ≫ f.hom = 0) (hK : IsLimit (KernelFork.ofι ι w)) :
    ∃ k : ModObj R K,
      k.smul ≫ ι = R ◁ ι ≫ ModObj.smul (M := R) (X := M.X) ∧
      (∀ a : R ⊗ K ⟶ K,
        a ≫ ι = R ◁ ι ≫ ModObj.smul (M := R) (X := M.X) → a = k.smul) ∧
      ∃ i : ({ X := K, mod := k } : Mod C R) ⟶ M,
        i.hom = ι ∧ ∃ hi : i ≫ f = 0, Nonempty (IsLimit (KernelFork.ofι i hi)) := by
  have : Mono ι := Fork.IsLimit.mono hK
  obtain ⟨γ, hγ⟩ := KernelFork.IsLimit.lift' hK (R ◁ ι ≫ act M.X) (by
    rw [Category.assoc, act_hom, ← whiskerLeft_comp_assoc, w,
      MonoidalPreadditive.whiskerLeft_zero, zero_comp])
  change γ ≫ ι = R ◁ ι ≫ act M.X at hγ
  let k : ModObj R K := ModObj.mk' R γ (by
    rw [← cancel_mono ι]
    simp [Category.assoc, hγ, ← whisker_exchange_assoc]) (by
    rw [← cancel_mono ι]
    simp only [Category.assoc, hγ]
    rw [← whisker_exchange_assoc, mul_act, associator_naturality_right_assoc,
      ← whiskerLeft_comp_assoc R γ, hγ, whiskerLeft_comp_assoc])
  let i : ({ X := K, mod := k } : Mod C R) ⟶ M := homMk ι hγ
  have hi : i ≫ f = 0 := hom_ext _ _ w
  refine ⟨k, hγ, ?_, i, rfl, hi, ⟨?_⟩⟩
  · intro a ha
    exact (cancel_mono ι).1 (ha.trans hγ.symm)
  · refine KernelFork.IsLimit.ofι i hi (fun {L} g hg ↦ ?_) ?_ ?_
    · obtain ⟨h, hh⟩ := KernelFork.IsLimit.lift' hK g.hom (by
        rw [← comp_hom', hg, zero_hom])
      change h ≫ ι = g.hom at hh
      exact homMk h (by
        change act L.X ≫ h = R ◁ h ≫ γ
        rw [← cancel_mono ι, Category.assoc, hh, act_hom, Category.assoc, hγ,
          ← whiskerLeft_comp_assoc, hh])
    · intro L g hg
      apply hom_ext
      exact (KernelFork.IsLimit.lift' hK g.hom (by
        rw [← comp_hom', hg, zero_hom])).2
    · intro L g hg m hm
      apply hom_ext
      apply (cancel_mono ι).1
      exact (congrArg Hom.hom hm).trans
        (KernelFork.IsLimit.lift' hK g.hom (by
          rw [← comp_hom', hg, zero_hom])).2.symm

end CategoryTheory.Mod
