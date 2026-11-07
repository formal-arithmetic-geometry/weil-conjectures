/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.Data.List.TFAE
public import Mathlib.RingTheory.Ideal.Operations
public import Submission.WeilConjectures.AlgebraicGeometry.CoherentFormalModule
import Submission.WeilConjectures.AlgebraicGeometry.CoherentFormalModuleAnnihilatedLimit
import Submission.WeilConjectures.AlgebraicGeometry.CoherentFormalModuleAnnihilatedFormalCover
import Mathlib.Tactic.TFAE
import Submission.WeilConjectures.AlgebraicGeometry.CoherentFormalModuleAnnihilatedDoubleKernel
import Submission.WeilConjectures.AlgebraicGeometry.CoherentFormalModuleAnnihilatedDoubleCokernel
import Submission.WeilConjectures.AlgebraicGeometry.CoherentFormalModulesAbelian
import Submission.WeilConjectures.RingTheory.KernelCokernelAnnihilatedModIdeal

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-! # Annihilation of kernels and cokernels of coherent formal module maps

Source: Stacks Project, Cohomology of Schemes, Remark 0888; Lemmas 087W and 087X
(blueprint: lem-weil-pbc-formal-systems-annihilated-by-power).
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- The four annihilation conditions are equivalent. The affine map is the limit of
section maps, regarded as linear over Γ(U, O_X); Lemma 087W identifies this with the
underlying map of finite modules over the completion. `op n` denotes level `n+1`.
Kernel forks and cokernel coforks express condition (4) without choosing an abelian
structure or particular representatives of the kernel and cokernel.
Source: Stacks, Remark 0888 and Lemmas 087W, 087X
(blueprint: lem-weil-pbc-formal-systems-annihilated-by-power).
Proof:
1. The fixed-exponent affine-limit lemma gives (1) implies (2), with exponent 2t.
2. Quasi-compactness gives a finite affine subcover. The maximum of its finitely many
   exponents, bounded below by 1, proves (2) implies (3), including the empty scheme.
3. The existing double-exponent kernel and cokernel lemmas give (3) implies (1).
4. Abelianness supplies canonical formal kernel and cokernel forks. The fixed-exponent
   formal-cover criterion on the finite cover gives (3) implies (4).
5. Apply that criterion on the cover of all affine opens to give (4) implies (2).
These five implications assemble the TFAE. The two geometric criteria remain named
open theorems in their own modules; this is a decomposition of the equivalence.
-/
theorem coherentFormalModule_annihilated_iff (X : Scheme.{u}) [IsNoetherian X]
    (I K : X.IdealSheafData) (F G : CoherentFormalModule X I) (α : F ⟶ G) :
    List.TFAE
      [(∃ t : ℕ, 1 ≤ t ∧ ∀ n : ℕ,
      IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower K.toModulesι t).2
        (kernel (α.hom.app (op n)))) ∧
      IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower K.toModulesι t).2
        (cokernel (α.hom.app (op n))))),
       (∀ U : X.affineOpens, ∃ t : ℕ, 1 ≤ t ∧
      K.ideal U ^ t ≤ Module.annihilator Γ(X, U.1) (LinearMap.ker
        (lim.map (Functor.whiskerRight α.hom
          (SheafOfModules.evaluation X.ringCatSheaf (op U.1)))).hom) ∧
      K.ideal U ^ t ≤ Module.annihilator Γ(X, U.1)
        (↥(limit (G.obj ⋙
          SheafOfModules.evaluation X.ringCatSheaf (op U.1)) :
          ModuleCat Γ(X, U.1)) ⧸ LinearMap.range
          (lim.map (Functor.whiskerRight α.hom
          (SheafOfModules.evaluation X.ringCatSheaf (op U.1)))).hom)),
       (∃ (r : ℕ) (U : Fin r → X.affineOpens) (t : ℕ),
      (⨆ i, (U i).1) = ⊤ ∧ 1 ≤ t ∧ ∀ i : Fin r,
      K.ideal (U i) ^ t ≤ Module.annihilator Γ(X, (U i).1) (LinearMap.ker
        (lim.map (Functor.whiskerRight α.hom
          (SheafOfModules.evaluation X.ringCatSheaf (op (U i).1)))).hom) ∧
      K.ideal (U i) ^ t ≤ Module.annihilator Γ(X, (U i).1)
        (↥(limit (G.obj ⋙
          SheafOfModules.evaluation X.ringCatSheaf (op (U i).1)) :
          ModuleCat Γ(X, (U i).1)) ⧸ LinearMap.range
          (lim.map (Functor.whiskerRight α.hom
          (SheafOfModules.evaluation X.ringCatSheaf (op (U i).1)))).hom)),
       (∃ (k : KernelFork α) (c : CokernelCofork α),
      Nonempty (IsLimit k) ∧ Nonempty (IsColimit c) ∧
      ∃ t : ℕ, 1 ≤ t ∧ ∀ n : ℕ,
        IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower K.toModulesι t).2
          (k.pt.obj.obj (op n))) ∧
        IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower K.toModulesι t).2
          (c.pt.obj.obj (op n))))] := by
  classical
  tfae_have 1 → 2 := by
    rintro ⟨t, ht, h⟩ U
    refine ⟨2 * t, by omega, ?_⟩
    exact coherentFormalModule_annihilated_affine_limit X I K F G α t ht h U
  tfae_have 2 → 3 := by
    intro h
    obtain ⟨s, hs, hcover⟩ :=
      (isCompact_iff_finite_and_eq_biUnion_affineOpens (U := (⊤ : X.Opens))).mp
        (by simpa using (isCompact_univ (X := X)))
    let S := hs.toFinset
    let e := S.equivFin
    let U : Fin S.card → X.affineOpens := fun i ↦ (e.symm i).1
    choose t ht hkill using h
    let b := max 1 (S.sup t)
    refine ⟨S.card, U, b, ?_, le_max_left _ _, ?_⟩
    · apply le_antisymm le_top
      rw [hcover]
      refine iSup_le fun V ↦ iSup_le fun hV ↦ ?_
      have hVS : V ∈ S := hs.mem_toFinset.mpr hV
      exact le_iSup_of_le (e ⟨V, hVS⟩) (by simp [U])
    · intro i
      have hle : t (U i) ≤ b :=
        (Finset.le_sup (e.symm i).2).trans (le_max_right _ _)
      exact ⟨(Ideal.pow_le_pow_right hle).trans (hkill (U i)).1,
        (Ideal.pow_le_pow_right hle).trans (hkill (U i)).2⟩
  tfae_have 3 → 1 := by
    rintro ⟨r, U, t, hcover, ht, h⟩
    refine ⟨2 * t, by omega, ?_⟩
    intro n
    exact ⟨coherentFormalModule_annihilated_double_kernel X I K F G α r U t hcover ht h n,
      coherentFormalModule_annihilated_double_cokernel X I K F G α r U t hcover ht h n⟩
  tfae_have 3 → 4 := by
    rintro ⟨r, U, t, hcover, ht, h⟩
    have : Abelian (CoherentFormalModule X I) :=
      (coherentFormalModule_abelian X I).1.some
    let k := KernelFork.ofι (kernel.ι α) (kernel.condition α)
    let c := CokernelCofork.ofπ (cokernel.π α) (cokernel.condition α)
    refine ⟨k, c, ⟨kernelIsKernel α⟩, ⟨cokernelIsCokernel α⟩, t, ht, ?_⟩
    exact (coherentFormalModule_annihilated_formal_cover X I K F G α k c
      (kernelIsKernel α) (cokernelIsCokernel α) (Fin r) U hcover t ht).mpr h
  tfae_have 4 → 2 := by
    rintro ⟨k, c, ⟨hk⟩, ⟨hc⟩, t, ht, h⟩ U
    refine ⟨t, ht, ?_⟩
    exact (coherentFormalModule_annihilated_formal_cover X I K F G α k c hk hc
      X.affineOpens id (iSup_affineOpens_eq_top X) t ht).mp h U
  tfae_finish


end AlgebraicGeometry

namespace LinearMap


end LinearMap
