/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.KoszulComplex
public import Mathlib.CategoryTheory.Preadditive.Projective.Resolution
public import Mathlib.Algebra.Homology.Homotopy
import Mathlib.CategoryTheory.Abelian.Projective.Resolution
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.LinearAlgebra.ExteriorPower.Basis

/-! # Homotopy uniqueness of Koszul augmentation lifts

Two chain maps from the Koszul complex of a tuple in `I` to a projective resolution of `A/I`
with the same augmentation are homotopic.

## Implementation details

The inductive construction is that of Mathlib's `ProjectiveResolution.liftHomotopyZero`, with
the free Koszul complex in place of a source resolution.

## References

* [Stacks, Tag 00LS]
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- Two Koszul chain maps with the same augmentation into a projective resolution
are homotopic. No exactness of the Koszul complex or regularity of the sequence is used. -/
theorem koszul_augmentation_lifts_homotopic (A : Type u) [CommRing A]
    (I : Ideal A) (r : ℕ) (g : Fin r → I)
    (P : ProjectiveResolution (ModuleCat.of A (A ⧸ I)))
    (a b : ExteriorAlgebra.koszulComplex A r (fun j ↦ (g j : A)) ⟶ P.complex)
    (hab : a.f 0 ≫ P.π.f 0 = b.f 0 ≫ P.π.f 0) : Nonempty (Homotopy a b) := by
  classical
  let K := ExteriorAlgebra.koszulComplex A r (fun j ↦ (g j : A))
  have (i : ℕ) : Projective (K.X i) := by
    change Projective (ModuleCat.of A (⋀[A]^i (Fin r →₀ A)))
    infer_instance
  let e : K ⟶ P.complex := a - b
  have he : e.f 0 ≫ P.π.f 0 = 0 := by
    simp [e, Preadditive.sub_comp, hab]
  let h₀ : K.X 0 ⟶ P.complex.X 1 := P.exact₀.liftFromProjective (e.f 0) he
  have hh₀ : h₀ ≫ P.complex.d 1 0 = e.f 0 :=
    P.exact₀.liftFromProjective_comp _ _
  have hz₁ : (e.f 1 - K.d 1 0 ≫ h₀) ≫ P.complex.d 1 0 = 0 := by
    rw [Preadditive.sub_comp, Category.assoc, HomologicalComplex.Hom.comm, hh₀, sub_self]
  let h₁ : K.X 1 ⟶ P.complex.X 2 :=
    (P.exact_succ 0).liftFromProjective (e.f 1 - K.d 1 0 ≫ h₀) hz₁
  have hh₁ : h₁ ≫ P.complex.d 2 1 = e.f 1 - K.d 1 0 ≫ h₀ :=
    (P.exact_succ 0).liftFromProjective_comp _ _
  refine ⟨Homotopy.equivSubZero.invFun ?_⟩
  refine Homotopy.mkInductive e h₀ hh₀.symm h₁ ?_ ?_
  · rw [hh₁]
    abel
  · intro n p
    obtain ⟨h, h', w⟩ := p
    have hz : (e.f (n + 2) - K.d (n + 2) (n + 1) ≫ h') ≫
        P.complex.d (n + 2) (n + 1) = 0 := by
      simp [w]
    refine ⟨(P.exact_succ (n + 1)).liftFromProjective _ hz, ?_⟩
    rw [(P.exact_succ (n + 1)).liftFromProjective_comp]
    abel

end AlgebraicGeometry
