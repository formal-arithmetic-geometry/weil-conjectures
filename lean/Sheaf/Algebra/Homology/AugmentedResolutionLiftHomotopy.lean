/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.CategoryTheory.Abelian.Projective.Resolution

/-! # Homotopy independence of augmented resolution lifts

Source: Stacks Project, Tag 00LS(2), projective lifting proof.
(blueprint: new-t4-augmented-resolution-lift-homotopy). -/

@[expose] public section
set_option autoImplicit false
open CategoryTheory

namespace ModuleCat

/-- Augmented lifts from a projective resolution into an exact augmented complex
are homotopic. The terms of the target complex need not be projective.

Source: Stacks Project, Tag 00LS(2), projective lifting proof.
(blueprint: new-t4-augmented-resolution-lift-homotopy).

Proof: Subtract the two lifts. Lift the degree-zero difference through the
augmentation kernel using projectivity of the source. At each following degree,
subtract the homotopy term already constructed. The chain-map equation makes
this residual morphism a cycle, and exactness and projectivity lift it through
the next differential. Homotopy.mkInductive assembles these lifts. -/
theorem augmented_lift_homotopy
    {D : Type*} [Category D] [Abelian D] {M N : D}
    (P : ProjectiveResolution M) (K : ChainComplex D ℕ) (π : K.X 0 ⟶ N)
    (hz : K.d 1 0 ≫ π = 0)
    (hzero : (ShortComplex.mk (K.d 1 0) π hz).Exact)
    (hsucc : ∀ n : ℕ,
      (ShortComplex.mk (K.d (n + 2) (n + 1)) (K.d (n + 1) n)
        (K.d_comp_d _ _ _)).Exact)
    (a a' : P.complex ⟶ K) (haug : a.f 0 ≫ π = a'.f 0 ≫ π) :
    Nonempty (Homotopy a a') := by
  let f := a - a'
  have hf : f.f 0 ≫ π = 0 := by
    change (a.f 0 - a'.f 0) ≫ π = 0
    rw [Preadditive.sub_comp, haug, sub_self]
  let s₀ := hzero.liftFromProjective (f.f 0) hf
  have hs₀ : s₀ ≫ K.d 1 0 = f.f 0 := hzero.liftFromProjective_comp _ _
  have h₁ : (f.f 1 - P.complex.d 1 0 ≫ s₀) ≫ K.d 1 0 = 0 := by
    rw [Preadditive.sub_comp, Category.assoc, hs₀, f.comm, sub_self]
  let s₁ := (hsucc 0).liftFromProjective (f.f 1 - P.complex.d 1 0 ≫ s₀) h₁
  have hs₁ : s₁ ≫ K.d 2 1 = f.f 1 - P.complex.d 1 0 ≫ s₀ :=
    (hsucc 0).liftFromProjective_comp _ _
  refine ⟨Homotopy.equivSubZero.invFun
    (Homotopy.mkInductive f s₀ hs₀.symm s₁ ?_ ?_)⟩
  · exact (sub_eq_iff_eq_add.mp hs₁.symm).trans (add_comm _ _)
  · intro n data
    rcases data with ⟨g, g', hg⟩
    have hnext : (f.f (n + 2) - P.complex.d (n + 2) (n + 1) ≫ g') ≫
        K.d (n + 2) (n + 1) = 0 := by
      simp [hg]
    refine ⟨(hsucc (n + 1)).liftFromProjective _ hnext, ?_⟩
    have hc := (hsucc (n + 1)).liftFromProjective_comp _ hnext
    exact (sub_eq_iff_eq_add.mp hc.symm).trans (add_comm _ _)

end ModuleCat
