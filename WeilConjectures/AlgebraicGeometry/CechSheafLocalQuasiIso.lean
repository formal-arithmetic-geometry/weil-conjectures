/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech
public import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf
import WeilConjectures.AlgebraicGeometry.CechSheafLocalAugmentationKernel
import WeilConjectures.AlgebraicGeometry.CechSheafLocalPositiveExact
/-! # Local exactness of the augmented module-sheaf Čech complex

Source: blueprint `lem-pc-cech-resolution`, displayed complex and proof paragraph 1.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- Any augmented complex with the usual Čech sections and restriction augmentation
is a quasi-isomorphism after restricting to one member of the family of opens.
Source: blueprint `lem-pc-cech-resolution`, proof paragraph 1 (insertion homotopy). -/
theorem augmented_cech_sheaf_quasiIso_restrict
    {X : Scheme.{u}} {ι : Type u} (U : ι → X.Opens) (F : X.Modules)
    (D : CochainComplex X.Modules ℕ)
    (ε : (CochainComplex.single₀ X.Modules).obj F ⟶ D)
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
    (hε : ∀ (y : Fin 1 → ι) (V : X.Opens),
        ((PresheafOfModules.forgetToPresheafModuleCat (op ⊤) isTerminalTop.op).map
            ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0 F).inv ≫ ε.f 0).val ≫
          (e 0).hom ≫
            Pi.π (fun y : Fin 1 → ι =>
              ((prod.functor (C := X.Opens)).op ⋙ Functor.opHom _ _ ⋙
                (Functor.whiskeringRight _ _ _).obj F.presheafModuleCat).obj
                  (op (∏ᶜ fun l => U (y l)))) y).app (op V) =
          F.presheafModuleCat.map (prod.snd : (∏ᶜ fun l => U (y l)) ⨯ V ⟶ V).op) (i : ι) :
    QuasiIso (((Scheme.Modules.restrictFunctor (U i).ι).mapHomologicalComplex
      (ComplexShape.up ℕ)).map ε) := by
  let R := (Scheme.Modules.restrictFunctor (U i).ι).mapHomologicalComplex (ComplexShape.up ℕ)
  let K := R.obj ((CochainComplex.single₀ X.Modules).obj F)
  let L := R.obj D
  let f : K ⟶ L := R.map ε
  change QuasiIso f
  refine ⟨fun n ↦ ?_⟩
  cases n with
  | zero =>
    obtain ⟨hk⟩ := augmented_cech_sheaf_restrict_kernel U F D ε e hd hε i
    rw [CochainComplex.quasiIsoAt₀_iff]
    rw [ShortComplex.quasiIso_iff_of_zeros _ (by simp [K, R])
      (by simp [K, R]) (by simp [L, R])]
    exact ⟨ShortComplex.exact_of_f_is_kernel _ hk, mono_of_isLimit_fork hk⟩
  | succ p =>
    have hK : K.ExactAt (p + 1) := by
      apply ShortComplex.exact_of_isZero_X₂
      exact (Scheme.Modules.restrictFunctor (U i).ι).map_isZero
        (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℕ) 0 F (p + 1) (by omega))
    rw [quasiIsoAt_iff_exactAt f (p + 1) hK]
    exact cech_sheaf_restrict_exact_positive U F D e hd i p

end AlgebraicGeometry
