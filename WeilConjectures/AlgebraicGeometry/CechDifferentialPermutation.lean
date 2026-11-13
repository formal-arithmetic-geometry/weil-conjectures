/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Scheme
public import WeilConjectures.CategoryTheory.SiteCechComplex
public import Mathlib.GroupTheory.Perm.Sign
import WeilConjectures.Combinatorics.SignedFacePermutation

/-!
# Permutation compatibility of the Čech differential

## References

* Stacks Project, Tag 01FG
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

/-- The differential of a permutation-equivariant cochain is permutation-equivariant
(Stacks, Tags 01FG and 01FH). -/
theorem cechDifferential_permutation (X : Scheme.{u}) {I : Type v}
    (U : I → X.Opens) (F : X.Opensᵒᵖ ⥤ AddCommGrpCat.{w})
    (S : SiteCechComplex U (fun i ↦ homOfLE (le_top : U i ≤ ⊤)))
    (p : ℕ) (c : S.cochains F p)
    (hc : ∀ (t : Fin (p + 1) → I) (σ : Equiv.Perm (Fin (p + 1))),
      c t = (Equiv.Perm.sign σ : ℤ) • F.map (S.indexMap t σ).op (c (t ∘ σ)))
    (t : Fin (p + 2) → I) (σ : Equiv.Perm (Fin (p + 2))) :
    S.differentialValue F p c t =
      (Equiv.Perm.sign σ : ℤ) •
        F.map (S.indexMap t σ).op (S.differentialValue F p c (t ∘ σ)) := by
  classical
  have hcomp {a b d : ℕ} (s : Fin (a + 1) → I)
      (α : Fin (b + 1) → Fin (a + 1)) (β : Fin (d + 1) → Fin (b + 1)) :
      S.indexMap s (α ∘ β) = S.indexMap s α ≫ S.indexMap (s ∘ α) β :=
    Subsingleton.elim _ _
  simp only [SiteCechComplex.differentialValue, map_sum, map_zsmul, Finset.smul_sum]
  rw [← Equiv.sum_comp σ]
  apply Finset.sum_congr rfl
  intro k _
  obtain ⟨τ, hface, hsign⟩ := Fin.signed_face_permutation (p + 1) σ k
  have hface' : (σ k).succAbove ∘ τ = σ ∘ k.succAbove :=
    funext (fun a => (hface a).symm)
  rw [hc (t ∘ (σ k).succAbove) τ, map_zsmul, smul_smul, hsign]
  rw [← AddCommGrpCat.comp_apply, ← F.map_comp, ← op_comp, ← hcomp]
  change ((Equiv.Perm.sign σ : ℤ) * (-1 : ℤ) ^ k.val) •
    F.map (S.indexMap t ((σ k).succAbove ∘ τ)).op
      (c (t ∘ ((σ k).succAbove ∘ τ))) = _
  rw [hface', hcomp, op_comp, F.map_comp, AddCommGrpCat.comp_apply, smul_smul]
  rfl

end AlgebraicGeometry.Scheme
