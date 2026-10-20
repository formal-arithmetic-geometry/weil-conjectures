/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.CategoryTheory.CompactObject
public import Mathlib.CategoryTheory.Triangulated.Yoneda
import Sheaf.CategoryTheory.BrownStageSequence
import Sheaf.CategoryTheory.BrownTelescopeAssembly
import Mathlib.CategoryTheory.ConcreteCategory.EpiMono

/-! The construction part of Brown representability.

Source: Stacks Project, Derived Categories, Tag 0A8F, Lemma `lemma-brown`
(blueprint: lem-pc-brown-generator-construction).
-/

@[expose] public section

universe v u

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Pretriangulated.Opposite

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [IsTriangulated C] [HasCoproducts.{v} C]

/-- Construct the Brown telescope map, with invertible components on shifted generators.

Source: Stacks Project, Derived Categories, Tag 0A8F, Lemma `lemma-brown`.
(blueprint: lem-pc-brown-generator-construction).

Proof: include all shifts of the given compact objects. Form the coproduct indexed by
pairs of a shifted generator and an element of its H-value. The product comparison for
H gives an element on this coproduct and additive Yoneda gives the first map. At each
stage form the coproduct of maps from shifted generators lying in the kernel. Complete
its map to the stage object to a distinguished triangle. Cohomological exactness lifts
the stage element across the cone, and the transition kills every kernel element.
Take the sequential telescope. The compatible stage elements lift to an element on
the telescope by exactness and the product comparison. Additive Yoneda gives α.
Compact Hom commutes with this telescope: surjectivity comes from the first stage,
and injectivity follows because every kernel element is killed at the next stage.
This works for every shifted generator. No generation assumption is needed here. -/
theorem brownRepresentabilityConstruction
    {I : Type v} (E : I → C) (hcompact : ∀ i : I, IsCompactObject (E i))
    (H : Cᵒᵖ ⥤ AddCommGrpCat.{v}) [H.IsHomological]
    (hH : ∀ (J : Type v), PreservesLimitsOfShape (Discrete J) H) :
    ∃ G : C, ∃ α : preadditiveYoneda.obj G ⟶ H,
      ∀ (i : I) (n : ℤ), IsIso (α.app (Opposite.op ((E i)⟦n⟧))) := by
  obtain ⟨X, β, hβ, hsurj, hkill⟩ := brownStageSequence E H hH
  obtain ⟨G, ι, α, hι, hα, hfactor⟩ := brownTelescopeAssembly X H hH β hβ
  refine ⟨G, α, fun i n ↦ ?_⟩
  apply (ConcreteCategory.isIso_iff_bijective _).2
  constructor
  · intro f g hfg
    have hzero : α.app (Opposite.op ((E i)⟦n⟧)) (f - g) = 0 := by
      rw [map_sub, hfg, sub_self]
    obtain ⟨j, k, hk⟩ := hfactor (E i) (hcompact i) n (f - g)
    have hstage : (β j).app (Opposite.op ((E i)⟦n⟧)) k = 0 := by
      rw [← hα j]
      change α.app (Opposite.op ((E i)⟦n⟧)) (k ≫ ι j) = 0
      rw [hk]
      exact hzero
    have hnext := hkill j i n k hstage
    apply sub_eq_zero.mp
    rw [← hk, ← hι j, ← Category.assoc, hnext, zero_comp]
  · intro a
    obtain ⟨f, hf⟩ := hsurj i n a
    refine ⟨f ≫ ι 0, ?_⟩
    rw [← hα 0] at hf
    exact hf

end CategoryTheory
