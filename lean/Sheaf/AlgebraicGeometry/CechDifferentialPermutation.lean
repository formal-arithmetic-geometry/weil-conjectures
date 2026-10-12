/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Sheaf.CategoryTheory.SiteCechComplex
public import Mathlib.GroupTheory.Perm.Sign

/-!
# Permutation compatibility of the Čech differential

Source: Stacks Project, Cohomology of Sheaves, Tag 01FG.
(blueprint: lem-pc-cech-differential-permutation)
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

/-- The differential of a permutation-equivariant cochain is permutation-equivariant.
Source: Stacks 01FG, differential stability of alternating cochains before Definition 01FH.

Proof: expand both differentials as signed face sums. For a permutation σ and a deleted
position j, put k = σ⁻¹(j), and let τ be the induced permutation of the remaining positions,
so σ ∘ k.succAbove = j.succAbove ∘ τ. Moving j and k to the last position shows
(-1)^j sign(τ) = sign(σ) (-1)^k. Apply the assumed transformation law to the jth face,
then reindex the sum by k. The two restriction composites agree since opens form a
poset. Restriction preserves finite sums and integer scalar multiplication, giving
exactly the asserted equality. This proof does not require the tuple to be injective,
nor division by two; it also works for p = 0 and for an empty index type.
(blueprint: lem-pc-cech-differential-permutation) -/
theorem cechDifferential_permutation (X : Scheme.{u}) {I : Type v}
    (U : I → X.Opens) (F : X.Opensᵒᵖ ⥤ AddCommGrpCat.{w})
    (S : SiteCechComplex U (fun i ↦ homOfLE (le_top : U i ≤ ⊤)))
    (p : ℕ) (c : S.cochains F p)
    (hc : ∀ (t : Fin (p + 1) → I) (σ : Equiv.Perm (Fin (p + 1))),
      c t = (Equiv.Perm.sign σ : ℤ) • F.map (S.indexMap t σ).op (c (t ∘ σ)))
    (t : Fin (p + 2) → I) (σ : Equiv.Perm (Fin (p + 2))) :
    S.differentialValue F p c t =
      (Equiv.Perm.sign σ : ℤ) •
        F.map (S.indexMap t σ).op (S.differentialValue F p c (t ∘ σ)) := by sorry

end AlgebraicGeometry.Scheme
