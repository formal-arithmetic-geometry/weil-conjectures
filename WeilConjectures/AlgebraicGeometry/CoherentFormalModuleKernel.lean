/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule
public import WeilConjectures.AlgebraicGeometry.Modules.QuasiCoherentCokernelImage
import WeilConjectures.AlgebraicGeometry.CoherentFormalModuleKernelConstruction
import WeilConjectures.AlgebraicGeometry.CoherentFormalModuleKernelFactorization
import Mathlib.CategoryTheory.Preadditive.FunctorCategory

/-!
# Kernels in coherent formal modules

Source: Stacks Project, Cohomology of Schemes, proof of Lemma 087X.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

private theorem formalMono_of_kernel_transition_zero {X : Scheme.{u}} [IsNoetherian X]
    {I : X.IdealSheafData} {K F : CoherentFormalModule X I} (ι : K ⟶ F) (c : ℕ)
    (hz : ∀ n : ℕ, kernel.ι (ι.hom.app (op (n + c))) ≫
      K.obj.map (homOfLE (Nat.le_add_right n c)).op = 0) : Mono ι := by
  apply (Preadditive.mono_iff_cancel_zero ι).mpr
  intro T γ hγ
  apply ObjectProperty.hom_ext
  apply NatTrans.ext
  funext a
  obtain ⟨n⟩ := a
  change γ.hom.app (op n) = 0
  have hcomp : γ.hom.app (op (n + c)) ≫ ι.hom.app (op (n + c)) = 0 := by
    exact congrArg (fun f => f.hom.app (op (n + c))) hγ
  have hzero : γ.hom.app (op (n + c)) ≫
      K.obj.map (homOfLE (Nat.le_add_right n c)).op = 0 := by
    calc
      _ = kernel.lift (ι.hom.app (op (n + c))) (γ.hom.app (op (n + c))) hcomp ≫
          kernel.ι (ι.hom.app (op (n + c))) ≫
            K.obj.map (homOfLE (Nat.le_add_right n c)).op := by simp
      _ = 0 := by rw [hz n, comp_zero]
  have := formalTransition_epi T (Nat.le_add_right n c)
  apply (cancel_epi (T.obj.map (homOfLE (Nat.le_add_right n c)).op)).mp
  simpa only [NatTrans.naturality, comp_zero] using hzero

/--
Source: Stacks Project, Cohomology of Schemes, proof of Lemma 087X, claims (a)--(d). -/
theorem coherentFormalModule_kernel {X : Scheme.{u}} [IsNoetherian X]
    (I : X.IdealSheafData) (F H : CoherentFormalModule X I)
    (α : F ⟶ H) :
    ∃ c : ℕ,
      (∀ (l m : ℕ) (h : m + c ≤ l),
        Subobject.mk
          (Abelian.image.ι (kernel.ι (α.hom.app (op l)) ≫
            F.obj.map (homOfLE (Nat.le_trans (Nat.le_add_right m c) h)).op)) =
        Subobject.mk
          (Abelian.image.ι (kernel.ι (α.hom.app (op (m + c))) ≫
            F.obj.map (homOfLE (Nat.le_add_right m c)).op))) ∧
      ∃ (S : ℕᵒᵖ ⥤ X.Modules) (j : S ⟶ F.obj),
        (∀ m : ℕ, ∃ e : S.obj (op m) ≅
            Abelian.image (kernel.ι (α.hom.app (op (m + c))) ≫
              F.obj.map (homOfLE (Nat.le_add_right m c)).op),
          e.hom ≫ Abelian.image.ι (kernel.ι (α.hom.app (op (m + c))) ≫
            F.obj.map (homOfLE (Nat.le_add_right m c)).op) = j.app (op m)) ∧
        ∃ (K : CoherentFormalModule X I) (ι : K ⟶ F)
          (e : ∀ n : ℕ, formalModuleQuotient I (n + 1) (S.obj (op (n + c))) ≅
            K.obj.obj (op n)),
          (∀ n : ℕ,
            formalModuleQuotientπ I (n + 2) (S.obj (op (n + 1 + c))) ≫
                (e (n + 1)).hom ≫ K.obj.map (homOfLE (Nat.le_succ n)).op =
              S.map (homOfLE (Nat.add_le_add_right (Nat.le_succ n) c)).op ≫
                formalModuleQuotientπ I (n + 1) (S.obj (op (n + c))) ≫ (e n).hom) ∧
          (∀ n : ℕ,
            formalModuleQuotientπ I (n + 1) (S.obj (op (n + c))) ≫
                (e n).hom ≫ ι.hom.app (op n) =
              j.app (op (n + c)) ≫ F.obj.map (homOfLE (Nat.le_add_right n c)).op) ∧
          ι ≫ α = 0 ∧
          (∀ (T : CoherentFormalModule X I) (γ : T ⟶ F),
            γ ≫ α = 0 → ∃! δ : T ⟶ K, δ ≫ ι = γ) := by
  obtain ⟨c, hstab, S, j, hS, K, ι, e, htrans, hcomp, hzero⟩ :=
    coherentFormalModule_kernel_construction I F H α
  have hjzero (m : ℕ) : j.app (op m) ≫ α.hom.app (op m) = 0 := by
    obtain ⟨a, ha⟩ := hS m
    let f := kernel.ι (α.hom.app (op (m + c))) ≫
      F.obj.map (homOfLE (Nat.le_add_right m c)).op
    have hf : f ≫ α.hom.app (op m) = 0 := by
      dsimp only [f]
      rw [Category.assoc, α.hom.naturality, ← Category.assoc, kernel.condition, zero_comp]
    have himage : Abelian.image.ι f ≫ α.hom.app (op m) = 0 := by
      apply (cancel_epi (Abelian.factorThruImage f)).mp
      simpa only [← Category.assoc, Abelian.image.fac, comp_zero] using hf
    rw [← ha, Category.assoc]
    exact (congrArg (a.hom ≫ ·) himage).trans comp_zero
  have hιzero : ι ≫ α = 0 := by
    apply ObjectProperty.hom_ext
    apply NatTrans.ext
    funext a
    obtain ⟨n⟩ := a
    change ι.hom.app (op n) ≫ α.hom.app (op n) = 0
    have : Epi (formalModuleQuotientπ I (n + 1) (S.obj (op (n + c)))) := by
      dsimp only [formalModuleQuotientπ]
      infer_instance
    apply (cancel_epi (e n).hom).mp
    apply (cancel_epi (formalModuleQuotientπ I (n + 1) (S.obj (op (n + c))))).mp
    simp only [comp_zero]
    rw [← Category.assoc _ _ (α.hom.app (op n)),
      ← Category.assoc _ _ (α.hom.app (op n)), hcomp n, Category.assoc,
      α.hom.naturality, ← Category.assoc, hjzero, zero_comp]
  have : Mono ι := formalMono_of_kernel_transition_zero ι c hzero
  refine ⟨c, hstab, S, j, hS, K, ι, e, htrans, hcomp, hιzero, ?_⟩
  intro T γ hγ
  obtain ⟨δ, hδ⟩ := coherentFormalModule_kernel_factorization
    I F H α c S j hS K ι e htrans hcomp T γ hγ
  refine ⟨δ, hδ, ?_⟩
  intro δ' hδ'
  exact (cancel_mono ι).mp (hδ'.trans hδ.symm)

end AlgebraicGeometry
