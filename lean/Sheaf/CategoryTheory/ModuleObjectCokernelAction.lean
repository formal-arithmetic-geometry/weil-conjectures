/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Q153
-/
module

public import Mathlib.CategoryTheory.Monoidal.Mod
public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import WeilConjectures.CategoryTheory.Monoidal.Mod.Abelian

/-!
# The induced action on an underlying cokernel of module objects

Source: blueprint main-20261015, sec-proetale-coefficients,
sk-prop-sfb-module-category/lem-sfb-modobj-cokernels.md
(blueprint: lem-sfb-modobj-cokernels).
-/

@[expose] public section

universe v u

open CategoryTheory MonoidalCategory Limits

namespace CategoryTheory.Mod

/-- An underlying cokernel of a module morphism has a unique compatible action map.
That map satisfies the module axioms, and the given projection is a cokernel in the
category of module objects.

Source: blueprint main-20261015, sec-proetale-coefficients,
sk-prop-sfb-module-category/lem-sfb-modobj-cokernels.md
(blueprint: lem-sfb-modobj-cokernels).

Proof:
1. Write `T = R ⊗ -`. Additivity gives `T(0) = 0`. Preservation of finite colimits
   makes `Tπ` a cokernel of `Tf` and `T²π` a cokernel of `T²f`; only these existing
   cokernels are used.
2. Cokernel projections `π`, `Tπ` and `T²π` are epimorphisms by uniqueness of their
   factorizations. Naturality of the unitors and associator also makes
   `𝟙 ⊗ π` and `(R ⊗ R) ⊗ π` epimorphisms.
3. Module linearity of `f` from `sk-def-sfb-module-objects` gives
   `Tf ≫ γ_N ≫ π = γ_M ≫ f ≫ π = 0`. Factor `γ_N ≫ π` through `Tπ` to obtain
   the action `a.smul`, unique among all underlying maps with this factorization.
4. Precompose the desired unit equation with `𝟙 ⊗ π`. Naturality and the unit
   equation for `N` identify both composites; cancel this epimorphism.
5. Precompose the desired associativity equation with `(R ⊗ R) ⊗ π`.
   Naturality of the associator, the factorization equation and associativity for
   `N` identify both composites. Cancel this epimorphism to obtain associativity.
6. The defining equation says exactly that `π` is a module morphism, as in
   `sk-def-sfb-module-objects`. Its composite with `f` is zero. For any module map
   `g` killing `f`, the underlying cokernel gives a unique factorization `h`.
7. Compare the two sides of the linearity equation for `h` after precomposing
   with `Tπ`; use linearity of `g` and the defining equation, then cancel `Tπ`.
   Thus `h` is a module map. Uniqueness on underlying maps gives uniqueness as
   a module map, proving the cokernel universal property. -/
theorem exists_cokernel_action
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [Preadditive C]
    [MonoidalPreadditive C] {R : C} [MonObj R]
    [PreservesFiniteColimits (tensorLeft R)]
    {M N : Mod C R} (f : M ⟶ N) {Q : C} (π : N.X ⟶ Q)
    (w : f.hom ≫ π = 0) (hπ : IsColimit (CokernelCofork.ofπ π w)) :
    ∃ (a : ModObj R Q),
      R ◁ π ≫ a.smul = ModObj.smul (M := R) (X := N.X) ≫ π ∧
      (∀ (γ : R ⊗ Q ⟶ Q),
        R ◁ π ≫ γ = ModObj.smul (M := R) (X := N.X) ≫ π → γ = a.smul) ∧
      ∃ (p : N ⟶ ({ X := Q, mod := a } : Mod C R)), p.hom = π ∧
        ∃ (wp : f ≫ p = 0), Nonempty (IsColimit (CokernelCofork.ofπ p wp)) := by
  let c := CokernelCofork.ofπ π w
  have hT := CokernelCofork.mapIsColimit c hπ (tensorLeft R)
  have hTT := CokernelCofork.mapIsColimit _ hT (tensorLeft R)
  have : Epi π := Cofork.IsColimit.epi hπ
  have : Epi (R ◁ π) := Cofork.IsColimit.epi hT
  have : Epi (R ◁ R ◁ π) := Cofork.IsColimit.epi hTT
  obtain ⟨s, hs⟩ := CokernelCofork.IsColimit.desc' hT (act N.X ≫ π) (by
    change R ◁ f.hom ≫ act N.X ≫ π = 0
    rw [← act_hom_assoc, w, comp_zero])
  change R ◁ π ≫ s = act N.X ≫ π at hs
  have hs_assoc := reassoc_of% hs
  let a : ModObj R Q := ModObj.mk' R s
    (by
      have : Epi (𝟙_ C ◁ π) := by
        rw [id_whiskerLeft]
        infer_instance
      rw [← cancel_epi (𝟙_ C ◁ π), whisker_exchange_assoc, hs,
        one_act_assoc, leftUnitor_naturality])
    (by
      have : Epi ((R ⊗ R) ◁ π) := by
        rw [tensor_whiskerLeft]
        infer_instance
      rw [← cancel_epi ((R ⊗ R) ◁ π), whisker_exchange_assoc, hs,
        mul_act_assoc, tensor_whiskerLeft_assoc, Iso.inv_hom_id_assoc,
        ← whiskerLeft_comp_assoc, hs, whiskerLeft_comp_assoc, hs])
  refine ⟨a, hs, ?_, ?_⟩
  · intro γ hγ
    exact (cancel_epi (R ◁ π)).1 (hγ.trans hs.symm)
  · let p : N ⟶ ({ X := Q, mod := a } : Mod C R) := Hom.mk' π hs.symm
    have wp : f ≫ p = 0 := hom_ext _ _ w
    refine ⟨p, rfl, wp, ⟨?_⟩⟩
    refine CokernelCofork.IsColimit.ofπ p wp (fun {L} g hg ↦ ?_) ?_ ?_
    · have hg' : f.hom ≫ g.hom = 0 := by
        simpa only [comp_hom', zero_hom] using congrArg Hom.hom hg
      obtain ⟨h, hh⟩ := CokernelCofork.IsColimit.desc' hπ g.hom hg'
      change π ≫ h = g.hom at hh
      refine Hom.mk' h ?_
      change s ≫ h = R ◁ h ≫ act L.X
      rw [← cancel_epi (R ◁ π), hs_assoc, hh,
        ← whiskerLeft_comp_assoc, hh, act_hom]
    · intro L g hg
      apply hom_ext
      exact (CokernelCofork.IsColimit.desc' hπ g.hom _).property
    · intro L g hg m hm
      apply hom_ext
      apply (cancel_epi π).1
      exact (congrArg Hom.hom hm).trans
        (CokernelCofork.IsColimit.desc' hπ g.hom _).property.symm

end CategoryTheory.Mod
