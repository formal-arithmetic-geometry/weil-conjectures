/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Ample

/-! # A finite affine cover from an ample invertible module

Source: Stacks Project, Properties, Definition 01PS and the first paragraph of
Lemma 01Q1's proof.
-/

@[expose] public section

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- An ample invertible module admits finitely many positive tensor powers with global
sections whose affine nonvanishing loci cover the scheme.
Source: Stacks Project, Properties, Definition 01PS and Lemma 01Q1, first proof paragraph. -/
theorem IsAmple.exists_finite_affine_cover (X : Scheme.{u}) (L : X.Modules)
    [L.IsInvertible] (hL : IsAmple X L) :
    ∃ (m : ℕ) (n : Fin m → ℕ)
      (s : (i : Fin m) → (L.tensorPow (n i)).val.presheaf.obj (Opposite.op ⊤))
      (U : Fin m → X.Opens),
      (∀ i : Fin m, 0 < n i) ∧
      (∀ i : Fin m, IsAffineOpen (U i)) ∧
      (∀ (i : Fin m) (x : X), x ∈ U i ↔
        (TopCat.Presheaf.germ (L.tensorPow (n i)).val.presheaf ⊤ x trivial) (s i) ∉
          (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) •
            (⊤ : Submodule (X.presheaf.stalk x)
              ↑(TopCat.Presheaf.stalk (L.tensorPow (n i)).val.presheaf x))) ∧
      (∀ x : X, ∃ i : Fin m, x ∈ U i) := by
  classical
  have : CompactSpace X := hL.1
  choose n hn s U hx hU hmem using hL.2
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun x : X ↦ (U x : Set X)) (fun x ↦ (U x).isOpen) (by
      intro x _
      exact Set.mem_iUnion.mpr ⟨x, hx x⟩)
  let e := t.equivFin.symm
  refine ⟨t.card, (fun i ↦ n (e i)), (fun i ↦ s (e i)), (fun i ↦ U (e i)),
    (fun i ↦ hn (e i)), (fun i ↦ hU (e i)), (fun i x ↦ hmem (e i) x), ?_⟩
  intro x
  obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ x))
  refine ⟨t.equivFin ⟨y, hy⟩, ?_⟩
  simpa [e] using hxy

end AlgebraicGeometry.Scheme.Modules
