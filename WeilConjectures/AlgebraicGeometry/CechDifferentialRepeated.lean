/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Scheme
public import WeilConjectures.CategoryTheory.SiteCechComplex
public import Mathlib.GroupTheory.Perm.Sign
import WeilConjectures.AlgebraicGeometry.CechDifferentialRepeatedDecomposition
import WeilConjectures.AlgebraicGeometry.CechDifferentialRepeatedCancellation

/-!
# Cancellation of repeated Čech tuples

Source: Stacks Project, Cohomology of Sheaves, Tag 01FG.
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

/-- The differential of an alternating cochain vanishes on tuples with repetitions.
Source: Stacks 01FG, differential stability of alternating cochains before Definition 01FH. -/
theorem cechDifferential_repeated (X : Scheme.{u}) {I : Type v}
    (U : I → X.Opens) (F : X.Opensᵒᵖ ⥤ AddCommGrpCat.{w})
    (S : SiteCechComplex U (fun i ↦ homOfLE (le_top : U i ≤ ⊤)))
    (p : ℕ) (c : S.cochains F p)
    (hc : ∀ (t : Fin (p + 1) → I) (σ : Equiv.Perm (Fin (p + 1))),
      c t = (Equiv.Perm.sign σ : ℤ) • F.map (S.indexMap t σ).op (c (t ∘ σ)))
    (hz : ∀ t : Fin (p + 1) → I, ¬ Function.Injective t → c t = 0)
    (t : Fin (p + 2) → I) (ht : ¬ Function.Injective t) :
    S.differentialValue F p c t = 0 := by
  obtain ⟨a, b, htab, hab⟩ := Function.not_injective_iff.mp ht
  rw [cechDifferential_repeated_decomposition X U F S p c t a b hab htab hz]
  exact cechDifferential_repeated_cancellation X U F S p c t a b hab htab hc

end AlgebraicGeometry.Scheme
