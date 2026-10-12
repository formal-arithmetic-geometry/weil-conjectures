/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T1
-/
module

public import Sheaf.CategoryTheory.Sites.SitePlusConstructionPresheaf

/-! # The plus construction is separated and injects into its double plus.

Source: Stacks Project, Sites, Theorem 00WB (parts (1) and (2)).
(blueprint: lem-weil-pbc-sheafification-plus-separated).
-/

@[expose] public section

universe u w

open CategoryTheory Opposite

namespace CategoryTheory.GrothendieckTopology

/-- For a presheaf of sets on a site, the first plus construction is separated,
and its canonical map into the second plus construction is injective.

Source: Stacks Project, Sites, Theorem 00WB (parts (1) and (2)).
(blueprint: lem-weil-pbc-sheafification-plus-separated).

Proof: separatedness follows from Mathlib's `GrothendieckTopology.Plus.sep`
for the generated covering sieve of each zero hypercover; `Sieve.mem_ofArrows_iff`
and functoriality reduce each sieve arrow to a hypercover arrow. Injectivity of
`toPlus` follows from the plus-construction equality criterion and separatedness.
-/
theorem plus_separated_and_injective
    {C : Type u} [SmallCategory C]
    (J : Precoverage C) [J.HasIsos] [J.IsStableUnderComposition]
    [J.IsStableUnderBaseChange] [J.HasPullbacks]
    (P : Cᵒᵖ ⥤ Type (max u w)) :
    (∀ (U : C) (E : Precoverage.ZeroHypercover.{max u w} J U)
      (s s' : (J.toGrothendieck.plusObj P).obj (op U)),
      (∀ i : E.toPreZeroHypercover.I₀,
        (J.toGrothendieck.plusObj P).map (E.toPreZeroHypercover.f i).op s =
          (J.toGrothendieck.plusObj P).map (E.toPreZeroHypercover.f i).op s') →
        s = s') ∧
      (∀ (U : C), Function.Injective
        ((J.toGrothendieck.toPlus (J.toGrothendieck.plusObj P)).app (op U))) := by
  have hsep : ∀ (U : C) (E : Precoverage.ZeroHypercover.{max u w} J U)
      (s s' : (J.toGrothendieck.plusObj P).obj (op U)),
      (∀ i : E.toPreZeroHypercover.I₀,
        (J.toGrothendieck.plusObj P).map (E.toPreZeroHypercover.f i).op s =
          (J.toGrothendieck.plusObj P).map (E.toPreZeroHypercover.f i).op s') → s = s' := by
    intro U E s s' h
    let S : (J.toGrothendieck).Cover U :=
      ⟨E.sieve₀, J.generate_mem_toGrothendieck E.mem₀⟩
    apply GrothendieckTopology.Plus.sep (J := J.toGrothendieck)
      (P := P) S s s'
    intro I
    have hmem : E.sieve₀ I.f := I.hf
    obtain ⟨i, g, hig⟩ :=
      (Sieve.mem_ofArrows_iff (Y := E.X) (f := E.f) I.f).mp hmem
    rw [hig]
    simpa only [op_comp, CategoryTheory.Functor.map_comp,
      CategoryTheory.ConcreteCategory.comp_apply] using
      congrArg (fun z => (J.toGrothendieck.plusObj P).map g.op z) (h i)
  refine ⟨hsep, ?_⟩
  intro U a b hab
  have hpc := plus_construction_presheaf J (J.toGrothendieck.plusObj P)
  rcases hpc with ⟨_, _, htiff, _⟩
  obtain ⟨E, he⟩ := (htiff (U := U) (a := a) (b := b)).mp hab
  exact hsep U E a b he

end CategoryTheory.GrothendieckTopology
