/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

import WeilConjectures.RingTheory.WellOrderedPresentationKernelProjectionData

public import Mathlib.CategoryTheory.Preadditive.Projective.Resolution
public import Mathlib.Order.RelClasses
public import Mathlib.LinearAlgebra.Quotient.Defs
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.Algebra.Category.ModuleCat.Abelian

/-!
# The kernel filtration of a well-ordered projective presentation

Given a well-ordered exhaustive filtration of a module together with projective resolutions
of its successive quotients, we build a projective presentation of the module whose kernel
carries a compatible exhaustive filtration with successive quotients the augmentation kernels.

## Implementation details

The projective presentations supplied by the quotient resolutions replace the free modules of
the Stacks argument. The direct sum is formed only over the indices with nonzero quotient;
these inject into `M` (choose an element of `F e` outside the predecessor supremum), so the sum
lives in universe `v` and is projective without assuming the ring is small.

## References

* Stacks Project, Algebra, Lemma 0D1U, successor argument.
-/

@[expose] public section

universe u v w

namespace ModuleCat

open CategoryTheory CategoryTheory.Limits

/-- The degree-zero presentations of the successive quotients give a projective
presentation of the union with a compatible exhaustive kernel filtration.
No dimension bound or induction hypothesis is used here.
Each successive kernel quotient is either zero or isomorphic to the kernel of the
augmentation of the corresponding resolution. -/
theorem exists_projective_presentation_kernel_filtration
    {R : Type u} [CommRing R] (M : ModuleCat.{v} R)
    {E : Type w} [LinearOrder E] [IsWellOrder E (· < ·)]
    (F : E → Submodule R M) (hF : Monotone F)
    (hcover : ∀ x : M, ∃ e : E, x ∈ F e)
    (P : ∀ e : E, ProjectiveResolution
      (ModuleCat.of R ((F e) ⧸
        ((⨆ i : {j : E // j < e}, F i.val).comap (F e).subtype)))) :
    ∃ S : ShortComplex (ModuleCat.{v} R), S.X₃ = M ∧ S.ShortExact ∧
      Projective S.X₂ ∧ ∃ G : E → Submodule R S.X₁,
        Monotone G ∧ (∀ x : S.X₁, ∃ e : E, x ∈ G e) ∧
        ∀ e : E,
          IsZero (ModuleCat.of R ((G e) ⧸
            ((⨆ i : {j : E // j < e}, G i.val).comap (G e).subtype))) ∨
          Nonempty (ModuleCat.of R ((G e) ⧸
            ((⨆ i : {j : E // j < e}, G i.val).comap (G e).subtype)) ≅
              kernel ((P e).π.f 0)) := by
  obtain ⟨S, hM, hS, hproj, H, hH, hHcover, hpieces⟩ :=
    exists_projective_presentation_kernel_projection_data M F hF hcover P
  let G : E → Submodule R S.X₁ := fun e ↦ (H e).comap S.f.hom
  refine ⟨S, hM, hS, hproj, G, ?_, ?_, ?_⟩
  · intro i j hij
    exact Submodule.comap_mono (hH hij)
  · intro x
    obtain ⟨e, he⟩ := hHcover (S.f.hom x)
    exact ⟨e, he⟩
  · intro e
    rcases hpieces e with hzero | ⟨q, hq, hker⟩
    · left
      change (⨆ i : {j : E // j < e}, G i.val).comap (G e).subtype = ⊤ at hzero
      rw [hzero]
      exact ModuleCat.isZero_of_subsingleton _
    · right
      exact ⟨((Submodule.quotEquivOfEq _ _ hker.symm).trans
        (q.quotKerEquivOfSurjective hq)).toModuleIso⟩

end ModuleCat
