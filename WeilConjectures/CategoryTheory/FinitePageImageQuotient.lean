/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.ExactCoupleConvergence
import WeilConjectures.CategoryTheory.FiniteCycleKernelPresentation
import WeilConjectures.CategoryTheory.NormalizedGradedFiniteKernel

/-!
# The finite derived-couple quotient in a half-plane

Source: Stacks Project, Tags 011R, 011T and 0AMJ.
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.BigradedExactCouple

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- A finite page whose next D term vanishes is the quotient of consecutive diagonal images,
with the comparison prescribed by the original `g`. -/
theorem finitePage_image_quotient (X : BigradedExactCouple C 0)
    (hE : ∀ p q : ℤ, p < 0 → IsZero (X.E p q))
    (A : ∀ n : ℤ, AlphaColimit X n)
    (hA : ∀ n : ℤ, (A n).obj = X.D 0 n)
    (hι : ∀ n : ℤ, (A n).ι 0 ≫ eqToHom (hA n) =
      eqToHom (by congr 1; omega))
    (r : ℕ) (p q : ℤ) (hp : p ≤ (r : ℤ))
    (hnext : IsZero ((X.pageCouple r).D (p + 2) (q - 1)))
    (hg : (X.cycleBoundaryTower.Z r p q).Factors (X.initialG p q)) :
    ∃ e : (X.pageCouple r).E p q ≅
      (X.imageFiltration (p + q) (A (p + q))).gradedPiece p,
      (X.cycleBoundaryTower.Z r p q).factorThru (X.initialG p q) hg ≫
        X.cycleBoundaryTower.projection r p q ≫ e.hom = X.toGradedPiece A p q := by
  let f := (X.cycleBoundaryTower.Z r p q).factorThru (X.initialG p q) hg ≫
    X.cycleBoundaryTower.projection r p q
  let g := X.toGradedPiece A p q
  obtain ⟨hf, hk⟩ := finiteCycle_kernel_presentation X r p q hnext hg
  have : Epi f := hf
  have : Epi g := by
    dsimp [g, toGradedPiece]
    infer_instance
  have hker : kernelSubobject f = kernelSubobject g :=
    hk.trans (normalizedGraded_finite_kernel X hE A hA hι r p q hp).symm
  have hfg : kernel.ι f ≫ g = 0 := by
    apply (kernelSubobject_factors_iff g _).mp
    rw [← hker]
    exact kernelSubobject_factors f _ (kernel.condition f)
  have hgf : kernel.ι g ≫ f = 0 := by
    apply (kernelSubobject_factors_iff f _).mp
    rw [hker]
    exact kernelSubobject_factors g _ (kernel.condition g)
  let e : (X.pageCouple r).E p q ≅
      (X.imageFiltration (p + q) (A (p + q))).gradedPiece p :=
    { hom := Abelian.epiDesc f g hfg
      inv := Abelian.epiDesc g f hgf
      hom_inv_id := by
        apply (cancel_epi f).1
        simp
      inv_hom_id := by
        apply (cancel_epi g).1
        simp }
  refine ⟨e, ?_⟩
  simpa only [f, g, e, Category.assoc] using Abelian.comp_epiDesc f g hfg

end CategoryTheory.BigradedExactCouple
