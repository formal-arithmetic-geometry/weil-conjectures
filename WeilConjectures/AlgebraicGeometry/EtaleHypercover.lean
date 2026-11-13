/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.AlgebraicTopology.SimplicialObject.Basic

/-!
# Étale hypercovers without finiteness or splitting

Source: Stacks Project, Hypercoverings, Definition 01G5 and Lemma 01GI.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- The all-degree hypercover condition, without splitting or finiteness requirements.
The matching object is the limit of the lower-simplex matching diagram, and the covering
condition is surjectivity of the matching arrow (Stacks, Tag 01G5). -/
def IsEtaleHypercover {X : Scheme.{u}} (U : SimplicialObject X.Etale) : Prop :=
  ∀ n : ℕ, ∃ (M : X.Etale)
    (π : ∀ (Δ : SimplexCategory), Δ.len < n →
      (Δ ⟶ SimplexCategory.mk n) → (M ⟶ U.obj (op Δ)))
    (μ : U.obj (op (SimplexCategory.mk n)) ⟶ M),
    (∀ (Δ Δ' : SimplexCategory) (h : Δ.len < n) (h' : Δ'.len < n)
      (α : Δ' ⟶ Δ) (θ : Δ ⟶ SimplexCategory.mk n),
      π Δ h θ ≫ U.map α.op = π Δ' h' (α ≫ θ)) ∧
    (∀ (T : Over X)
      (p : ∀ (Δ : SimplexCategory), Δ.len < n → (Δ ⟶ SimplexCategory.mk n) →
        (T ⟶ (Scheme.Etale.forget X).obj (U.obj (op Δ)))),
      (∀ (Δ Δ' : SimplexCategory) (h : Δ.len < n) (h' : Δ'.len < n)
        (α : Δ' ⟶ Δ) (θ : Δ ⟶ SimplexCategory.mk n),
        p Δ h θ ≫ (Scheme.Etale.forget X).map (U.map α.op) = p Δ' h' (α ≫ θ)) →
      ∃! f : T ⟶ (Scheme.Etale.forget X).obj M,
        ∀ (Δ : SimplexCategory) (h : Δ.len < n) (θ : Δ ⟶ SimplexCategory.mk n),
          f ≫ (Scheme.Etale.forget X).map (π Δ h θ) = p Δ h θ) ∧
    (∀ (Δ : SimplexCategory) (h : Δ.len < n) (θ : Δ ⟶ SimplexCategory.mk n),
      μ ≫ π Δ h θ = U.map θ.op) ∧ Surjective μ.left

end AlgebraicGeometry
