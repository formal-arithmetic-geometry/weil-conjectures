/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.GroupTheory.CosetCover
public import WeilConjectures.Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.Mathlib.AlgebraicGeometry.Over

/-!
# A global section avoiding the associated points of a coherent sheaf

placeholder
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite SheafOfModules TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-- A global section `s` of a sheaf of modules `F` **vanishes at** a point `x` of `X` if its
germ at `x` lies in `𝔪ₓ Fₓ`, equivalently if its image in the fibre `Fₓ / 𝔪ₓ Fₓ` is zero. -/
def VanishesAt (F : X.Modules) (s : Γ(F, ⊤)) (x : X) : Prop :=
  germₗ F (⟨x, trivial⟩ : (⊤ : X.Opens)) s ∈
    IsLocalRing.maximalIdeal (X.presheaf.stalk x) •
      (⊤ : Submodule (X.presheaf.stalk x) (F.presheaf.stalk x))

/-- The global sections vanishing at a point `x` form a `Γ(X, 𝒪ₓ)`-submodule of `Γ(X, F)`. -/
noncomputable def vanishingSubmodule (F : X.Modules) (x : (⊤ : X.Opens)) :
    Submodule Γ(X, ⊤) Γ(F, ⊤) :=
  Submodule.comap (germₗ F x)
    (Submodule.restrictScalars Γ(X, ⊤)
      (IsLocalRing.maximalIdeal (X.presheaf.stalk x.1) •
        (⊤ : Submodule (X.presheaf.stalk x.1) (F.presheaf.stalk x.1))))

lemma mem_vanishingSubmodule_iff (F : X.Modules) (s : Γ(F, ⊤)) (x : X) :
    s ∈ F.vanishingSubmodule ⟨x, trivial⟩ ↔ F.VanishesAt s x := Iff.rfl

/-- **A vector space over an infinite field is not the union of finitely many proper
subspaces**, in the form used below: if each of finitely many subspaces misses some vector,
then a single vector misses all of them. -/
private theorem exists_forall_notMem {k M ι : Type*} [Field k] [Infinite k] [AddCommGroup M]
    [Module k M] {Z : Set ι} (hZ : Z.Finite) (W : ι → Submodule k M)
    (hW : ∀ i ∈ Z, ∃ m : M, m ∉ W i) : ∃ m : M, ∀ i ∈ Z, m ∉ W i := by
  by_contra h
  push Not at h
  have hcov : ⋃ p ∈ hZ.toFinset.image W, (p : Set M) = Set.univ := by
    refine Set.eq_univ_of_forall fun m ↦ ?_
    obtain ⟨i, hi, hm⟩ := h m
    exact Set.mem_biUnion (Finset.mem_image_of_mem W (hZ.mem_toFinset.2 hi)) hm
  obtain ⟨i, hi, hiW⟩ := Finset.mem_image.1 (Subspace.top_mem_of_biUnion_eq_univ hcov)
  obtain ⟨m, hm⟩ := hW i (hZ.mem_toFinset.1 hi)
  exact hm (hiW ▸ Submodule.mem_top)

variable (k : Type u) [Field k] [Infinite k]

/-- **A global section avoiding finitely many prescribed points.** -/
theorem exists_forall_not_vanishesAt [X.Over (Spec (.of k))] (F : X.Modules) {Z : Set X}
    (hZ : Z.Finite) (hF : ∀ x ∈ Z, ∃ s : Γ(F, ⊤), ¬ F.VanishesAt s x) :
    ∃ s : Γ(F, ⊤), ∀ x ∈ Z, ¬ F.VanishesAt s x := by
  let _ : Module k Γ(X, ⊤) := Module.compHom _ (Scheme.overRingHom k X)
  let _ : Module k Γ(F, ⊤) := Module.compHom _ (Scheme.overRingHom k X)
  have : IsScalarTower k Γ(X, ⊤) Γ(F, ⊤) := ⟨fun c r s ↦ mul_smul _ r s⟩
  obtain ⟨s, hs⟩ := exists_forall_notMem (k := k) hZ
    (fun x ↦ Submodule.restrictScalars k (F.vanishingSubmodule ⟨x, trivial⟩))
    fun x hx ↦ hF x hx
  exact ⟨s, hs⟩

end AlgebraicGeometry.Scheme.Modules
