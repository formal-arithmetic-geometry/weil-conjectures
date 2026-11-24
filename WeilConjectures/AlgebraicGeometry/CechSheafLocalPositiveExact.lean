/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech
public import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf
import WeilConjectures.AlgebraicGeometry.CechSheafLocalPositiveSections
/-! # Positive-degree exactness of a locally restricted Cech complex -/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- The restricted Cech-model complex is exact in every positive degree. -/
theorem cech_sheaf_restrict_exact_positive
    {X : Scheme.{u}} {ι : Type u} (U : ι → X.Opens) (F : X.Modules)
    (D : CochainComplex X.Modules ℕ)
    (e : ∀ p : ℕ, (PresheafOfModules.forgetToPresheafModuleCat (op ⊤) isTerminalTop.op).obj
          (D.X p).val ≅
        ((cechComplexFunctor U).obj
          ((prod.functor (C := X.Opens)).op ⋙ Functor.opHom _ _ ⋙
            (Functor.whiskeringRight _ _ _).obj F.presheafModuleCat)).X p)
    (hd : ∀ p : ℕ,
        (PresheafOfModules.forgetToPresheafModuleCat (op ⊤) isTerminalTop.op).map
            (D.d p (p + 1)).val ≫ (e (p + 1)).hom =
          (e p).hom ≫ ((cechComplexFunctor U).obj
            ((prod.functor (C := X.Opens)).op ⋙ Functor.opHom _ _ ⋙
              (Functor.whiskeringRight _ _ _).obj F.presheafModuleCat)).d p (p + 1))
    (i : ι) (p : ℕ) :
    (((Scheme.Modules.restrictFunctor (U i).ι).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj D).ExactAt (p + 1) := by
  let K := ((Scheme.Modules.restrictFunctor (U i).ι).mapHomologicalComplex
    (ComplexShape.up ℕ)).obj D
  change (K.sc (p + 1)).Exact
  rw [ShortComplex.exact_iff_kernel_ι_comp_cokernel_π_zero]
  apply Scheme.Modules.hom_ext
  intro W
  ext y
  let x := (kernel.ι (K.sc (p + 1)).g).app W y
  have hx : (K.sc (p + 1)).g.app W x = 0 := by
    have h := congrArg (fun f ↦ f.app W y) (kernel.condition (K.sc (p + 1)).g)
    simpa [x, Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply] using h
  obtain ⟨z, hz⟩ := cech_sheaf_restrict_positive_section_boundary U F D e hd i p W x hx
  change (cokernel.π (K.sc (p + 1)).f).app W x = 0
  rw [← hz]
  have h := congrArg (fun f ↦ f.app W z) (cokernel.condition (K.sc (p + 1)).f)
  simp only [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply,
    Scheme.Modules.Hom.zero_app] at h
  exact h

end AlgebraicGeometry
