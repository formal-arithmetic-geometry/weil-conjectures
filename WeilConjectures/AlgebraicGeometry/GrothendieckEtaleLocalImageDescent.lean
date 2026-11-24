/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GrothendieckEtaleLocalImage
import WeilConjectures.AlgebraicGeometry.GrothendieckEtaleLocalImageDetection

/-! # Finite-cover descent for the categorical local image

## References

* [Stacks Project, Tag 00WL]
-/

@[expose] public section

universe u' u
open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.FiniteSplitEtaleHypercover.Grothendieck

variable {X : Scheme.{u}} (A : Type u') [Category.{u + 1} A] [Abelian A]
  [IsGrothendieckAbelian.{u + 1} A]

/-- Factoring through the categorical local image can be checked on a finite covering
family. No projectivity or presentability of the source object is assumed.
(Stacks, Tag 00WL) -/
theorem localImage_factors_of_finite_cover
    {F G : Sheaf X.smallEtaleTopology A} (p : F ⟶ G)
    (W : X.Etale) (B : A) (x : B ⟶ G.obj.obj (op W))
    (n : ℕ) (U : Fin n → X.Etale) (f : ∀ i, U i ⟶ W)
    (hf : Sieve.ofArrows U f ∈ X.smallEtaleTopology W)
    (hx : ∀ i, (localImage p (U i)).Factors (x ≫ G.obj.map (f i).op)) :
    (localImage p W).Factors x := by
  classical
  let c := cokernel.π (localImage p W).arrow
  have hkill : ∀ (s : Finset (Fin n)) (B' : A) (π : B' ⟶ B),
      (∀ i, i ∉ s → LocallyLifts p (U i) (π ≫ x ≫ G.obj.map (f i).op)) →
        π ≫ x ≫ c = 0 := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro B' π hl
      have hh := locallyLifts_of_cover p (π ≫ x) U f hf
        (fun i ↦ by simpa [Category.assoc] using hl i (by simp))
      have hfactor : (localImage p W).Factors (π ≫ x) :=
        (Subobject.imageSubobject_le_iff _ _).1
          (le_sSup (localImageMember_image p hh))
      rw [← Category.assoc, ← Subobject.factorThru_arrow _ _ hfactor]
      simp only [Category.assoc, c, cokernel.condition, comp_zero]
    | @insert i s hi ih =>
      intro B' π hl
      apply eq_zero_of_factors_localImage A p (U i) B' _
        (π ≫ x ≫ G.obj.map (f i).op) (π ≫ x ≫ c)
        (Subobject.factors_of_factors_right π (hx i))
      intro B'' τ R hR hlocal
      have h := ih B'' (τ ≫ π) (by
        intro j hj
        by_cases hji : j = i
        · subst j
          refine ⟨R, hR, fun Z a ha ↦ ?_⟩
          obtain ⟨l, hl⟩ := hlocal Z a ha
          exact ⟨l, by simpa [Category.assoc] using hl⟩
        · simpa [Category.assoc] using
            locallyLifts_precomp p (hl j (by simp [hj, hji])) τ)
      simpa [Category.assoc] using h
  have hz : x ≫ c = 0 := by
    simpa using hkill Finset.univ B (𝟙 B) (by simp)
  refine (Subobject.factors_iff _ _).2 ⟨Abelian.monoLift _ x hz, ?_⟩
  exact Abelian.monoLift_comp _ _ _

end AlgebraicGeometry.FiniteSplitEtaleHypercover.Grothendieck
