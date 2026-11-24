/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.CategoryTheory.Abelian.Images
import WeilConjectures.AlgebraicGeometry.ClosedImmersionUnitKernel
import Mathlib.CategoryTheory.Abelian.Basic

/-!
# Closed immersion unit and quotient

## References

* Stacks Project, Tags 04CJ and 08KS
-/

@[expose] public section

universe w

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules

noncomputable section

/-- For a closed immersion `i : Z ⟶ Y` with ideal sheaf `J = i.ker`, and every
`𝒪_Y`-module `F`, the unit `η_F : F ⟶ i_* i^* F` of `i^* ⊣ i_*` is an epimorphism
with kernel `JF`, and it induces an isomorphism `η̄_F : F/JF ≅ i_* i^* F`, natural in `F`.

Here `JF` is the image of the multiplication map `J ⊗ F ⟶ F`, and `F/JF` is its cokernel. -/
theorem closedImmersion_unit_quotient {Y Z : Scheme.{w}} (i : Z ⟶ Y)
    [IsClosedImmersion i] :
    let adj : tensorPullback i ⊣ pushforward i :=
      Classical.choice (nonempty_tensorPullbackAdjunction i)
    let J : Y.IdealSheafData := i.ker
    let μ : ∀ F : Y.Modules, J.toModules ⊗ F ⟶ F := fun F =>
      J.toModulesι ▷ F ≫ (λ_ F).hom
    ∃ η' : ∀ F : Y.Modules,
        cokernel (image.ι (μ F)) ⟶ (pushforward i).obj ((tensorPullback i).obj F),
      (∀ F : Y.Modules,
        Epi (adj.unit.app F) ∧
          (∃ w : image.ι (μ F) ≫ adj.unit.app F = 0,
            Nonempty (IsLimit (KernelFork.ofι (image.ι (μ F)) w))) ∧
          cokernel.π (image.ι (μ F)) ≫ η' F = adj.unit.app F ∧ IsIso (η' F)) ∧
      ∀ (F G : Y.Modules) (a : F ⟶ G),
        ∃ q : cokernel (image.ι (μ F)) ⟶ cokernel (image.ι (μ G)),
          cokernel.π (image.ι (μ F)) ≫ q = a ≫ cokernel.π (image.ι (μ G)) ∧
            q ≫ η' G = η' F ≫ (pushforward i).map ((tensorPullback i).map a) := by
  dsimp
  let adj : tensorPullback i ⊣ pushforward i :=
    Classical.choice (nonempty_tensorPullbackAdjunction i)
  let μ : ∀ F : Y.Modules, i.ker.toModules ⊗ F ⟶ F := fun F =>
    i.ker.toModulesι ▷ F ≫ (λ_ F).hom
  have h := closedImmersion_unit_kernel i
  dsimp at h
  have hex : ∀ F : Y.Modules,
      ∃ e : cokernel (image.ι (μ F)) ≅ (pushforward i).obj ((tensorPullback i).obj F),
        cokernel.π (image.ι (μ F)) ≫ e.hom = adj.unit.app F := by
    intro F
    obtain ⟨he, w, ⟨hk⟩⟩ := h F
    have : Epi (adj.unit.app F) := he
    let hc := Abelian.epiIsCokernelOfKernel (KernelFork.ofι _ w) hk
    let e := (cokernelIsCokernel (image.ι (μ F))).coconePointUniqueUpToIso hc
    refine ⟨e, ?_⟩
    exact IsColimit.comp_coconePointUniqueUpToIso_hom
      (cokernelIsCokernel (image.ι (μ F))) hc WalkingParallelPair.one
  choose e he using hex
  refine ⟨fun F => (e F).hom, ?_, ?_⟩
  · intro F
    exact ⟨(h F).1, (h F).2, he F, inferInstance⟩
  · intro F G a
    refine ⟨(e F).hom ≫ (pushforward i).map ((tensorPullback i).map a) ≫
      (e G).inv, ?_, ?_⟩
    · rw [← Category.assoc, he F]
      change adj.unit.app F ≫ (tensorPullback i ⋙ pushforward i).map a ≫
        (e G).inv = a ≫ cokernel.π (image.ι (μ G))
      rw [← adj.unit.naturality_assoc, ← he G]
      simp
    · simp

end
end AlgebraicGeometry.Scheme.Modules
