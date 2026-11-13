/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.Order.Disjointed

/-!
# A finite surjective disjoint union of open immersions has a section

## References

* Stacks Project, Tag 09ZA.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A finite surjective morphism `p : V ⟶ Z` whose source is a finite disjoint union of
open-and-closed subschemes `Vᵢ`, on each of which `p` is an open immersion, has a section.
(Stacks, Tag 09ZA.) -/
theorem exists_section_of_finite_clopen_open_cover
    {n : ℕ} (Z V : Scheme.{u}) (p : V ⟶ Z)
    [IsFinite p] [Surjective p]
    (Vi : Fin n → Scheme.{u})
    (k : ∀ i, Vi i ⟶ V)
    (hk : ∀ i, IsOpenImmersion (k i) ∧ IsClosedImmersion (k i))
    (hcop : IsColimit (Cofan.mk V k))
    (pi : ∀ i, Vi i ⟶ Z)
    (hpi : ∀ i, pi i = k i ≫ p)
    [∀ i, IsOpenImmersion (pi i)] :
    ∃ s : Z ⟶ V, s ≫ p = 𝟙 Z := by
  classical
  have hkclosed (i : Fin n) : IsClosed (Set.range (k i)) := by
    let := (hk i).2
    exact (k i).isClosedEmbedding.isClosed_range
  have hclosed (i : Fin n) : IsClosed (Set.range (pi i)) := by
    rw [hpi i]
    change IsClosed (Set.range (p ∘ k i))
    rw [Set.range_comp]
    exact p.isClosedMap _ (hkclosed i)
  let U : Fin n → TopologicalSpace.Clopens Z := fun i ↦
    ⟨(pi i).opensRange, hclosed i, (pi i).opensRange.isOpen⟩
  have hcover : ⋃ i, (U i : Set Z) = Set.univ := by
    have : IsIso (Sigma.desc k) :=
      (Cofan.nonempty_isColimit_iff_isIso_sigmaDesc (Cofan.mk V k)).mp ⟨hcop⟩
    apply Set.eq_univ_of_forall
    intro z
    obtain ⟨v, rfl⟩ := p.surjective z
    obtain ⟨w, rfl⟩ := (Sigma.desc k).surjective v
    have hw : ∃ (i : Fin n) (x : Vi i), Sigma.ι Vi i x = w :=
      (sigmaOpenCover Vi).exists_eq w
    obtain ⟨i, x, hx⟩ := hw
    rw [← hx]
    apply Set.mem_iUnion.mpr
    refine ⟨i, ?_⟩
    change _ ∈ Set.range (pi i)
    refine ⟨x, ?_⟩
    rw [← Scheme.Hom.comp_apply (Sigma.ι Vi i) (Sigma.desc k), Sigma.ι_comp_desc, hpi i]
    rfl
  -- Group the subset strata by their first chosen image.
  obtain ⟨W, hWle, hWsup, hWdisj⟩ := Fintype.exists_disjointed_le U
  have hWcover : ⋃ i, (W i : Set Z) = Set.univ := by
    have heq := congrArg (fun T : TopologicalSpace.Clopens Z ↦ (T : Set Z)) hWsup
    simp only [TopologicalSpace.Clopens.coe_finset_sup, Finset.mem_univ,
      Set.iUnion_true] at heq
    exact heq.trans hcover
  let O : Fin n → Z.Opens := fun i ↦ (W i).toOpens
  have hOcover : ⨆ i, O i = ⊤ := by
    apply TopologicalSpace.Opens.ext
    simpa [O] using hWcover
  have hOdisj : Pairwise (fun i j ↦ Disjoint (O i) (O j)) := by
    intro i j hij
    apply TopologicalSpace.Opens.coe_disjoint.mp
    exact TopologicalSpace.Clopens.coe_disjoint.mpr (hWdisj hij)
  -- A disjoint open cover is a coproduct, so there are no overlap equations to check.
  obtain ⟨hZ⟩ := nonempty_isColimit_cofanMk_of (fun i ↦ (O i).ι)
    (by simpa using hOcover) (by simpa using hOdisj)
  have hle (i : Fin n) : O i ≤ (pi i).opensRange := hWle i
  let t : ∀ i, (O i).toScheme ⟶ V := fun i ↦
    Z.homOfLE (hle i) ≫ (pi i).isoOpensRange.inv ≫ k i
  refine ⟨Cofan.IsColimit.desc hZ t, ?_⟩
  apply Cofan.IsColimit.hom_ext hZ
  intro i
  change (O i).ι ≫ Cofan.IsColimit.desc hZ t ≫ p = (O i).ι ≫ 𝟙 Z
  have ht : (O i).ι ≫ Cofan.IsColimit.desc hZ t = t i :=
    Cofan.IsColimit.fac hZ t i
  rw [← Category.assoc, ht]
  dsimp only [t]
  simp only [Category.assoc, ← hpi i, Scheme.Hom.isoOpensRange_inv_comp,
    Category.comp_id]
  simp

end AlgebraicGeometry
