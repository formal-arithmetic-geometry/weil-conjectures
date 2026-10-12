/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
module

public import Sheaf.AlgebraicGeometry.CoherentFormalModulesAffine
public import Sheaf.AlgebraicGeometry.CoherentFormalModulesAbelian
public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.Data.List.TFAE
public import Mathlib.RingTheory.Ideal.Operations
import Sheaf.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import Sheaf.AlgebraicGeometry.CoherentFormalModule
import Sheaf.AlgebraicGeometry.CoherentFormalModulesLocalExactness
import Sheaf.AlgebraicGeometry.Modules.IdealTimesQuasiCoherentAffineSections
import Sheaf.AlgebraicGeometry.Modules.QuasiCoherentCokernelImage
import Sheaf.RingTheory.AdicCompletionNoetherian
import Sheaf.RingTheory.KernelCokernelAnnihilatedModIdeal
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel

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
Proof, following the seven steps of the node:
1. The affine equivalence (lem-weil-pbc-coherent-formal-modules-affine) identifies the
limit projections and reductions modulo I^n with the component maps.
2. Ideal products of quasi-coherent modules are computed on affine sections
(lem-weil-pbc-ideal-times-quasi-coherent-affine-sections); annihilation is local.
3. The reduction fact (lem-weil-pbc-kernel-cokernel-annihilated-mod-ideal) gives
(3) implies (1), with exponent 2t on each member of the cover.
4. Its natural scalar quasi-inverses pass to the inverse limit and show (1) implies (2).
5. Quasi-compactness gives a finite affine subcover. The maximum of its finitely many
exponents proves (2) implies (3); on the empty scheme choose exponent 1.
6. Exact affine restriction and the equivalence carry formal kernels and cokernels to
module kernels and cokernels (lem-weil-pbc-coherent-formal-modules-abelian and
lem-weil-pbc-coherent-formal-modules-local-exactness).
7. Those finite completed modules are separated. Thus killing all their reductions
is equivalent to killing the modules, giving (4) equivalent to (2) and (3).
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
  sorry

/-- The exponent t on a finite affine cover gives exponent 2t for every component.
Source: Stacks, Remark 0888 (blueprint: lem-weil-pbc-formal-systems-annihilated-by-power).
Proof: apply the reduction-modulo-ideal fact to the limit map on each affine with J=I^n
(node step 3). The affine equivalence identifies the reductions with component maps
(step 1), and local checking of ideal products gives the global result (step 2).
-/
theorem coherentFormalModule_annihilated_double (X : Scheme.{u}) [IsNoetherian X]
    (I K : X.IdealSheafData) (F G : CoherentFormalModule X I) (α : F ⟶ G)
    (r : ℕ) (U : Fin r → X.affineOpens) (t : ℕ)
    (hcover : (⨆ i, (U i).1) = ⊤) (ht : 1 ≤ t)
    (h : ∀ i : Fin r,
      K.ideal (U i) ^ t ≤ Module.annihilator Γ(X, (U i).1) (LinearMap.ker
        (lim.map (Functor.whiskerRight α.hom
          (SheafOfModules.evaluation X.ringCatSheaf (op (U i).1)))).hom) ∧
      K.ideal (U i) ^ t ≤ Module.annihilator Γ(X, (U i).1)
        (↥(limit (G.obj ⋙
          SheafOfModules.evaluation X.ringCatSheaf (op (U i).1)) :
          ModuleCat Γ(X, (U i).1)) ⧸ LinearMap.range
          (lim.map (Functor.whiskerRight α.hom
          (SheafOfModules.evaluation X.ringCatSheaf (op (U i).1)))).hom)) :
    ∀ n : ℕ,
      IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower K.toModulesι (2 * t)).2
        (kernel (α.hom.app (op n)))) ∧
      IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower K.toModulesι (2 * t)).2
        (cokernel (α.hom.app (op n)))) := by
  sorry

end AlgebraicGeometry

namespace LinearMap

/-- The commutative algebra fact underlying the four-way equivalence: reduce modulo
any ideal J. The kernel/cokernel hypothesis is the intrinsic form of the exact sequence
0 → T → M → N → Q → 0, which identifies T with ker u and Q with N/range u.
Source: Stacks, Remark 0888 (blueprint: lem-weil-pbc-formal-systems-annihilated-by-power).
Proof (node step 3): for f,g in K^t, lift fy to x and set h(y)=gx. The kernel
hypothesis makes this independent of x, and linearity gives a linear map. The two
composites with u are multiplication by fg. Reduce these identities modulo J; every
product fg kills the reduced kernel and cokernel. Such products generate K^(2t).
-/
theorem ker_coker_reduction_annihilated_double
    {A : Type u} [CommRing A] {M : Type v} {N : Type w}
    [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    (K J : Ideal A) (t : ℕ) (ht : 1 ≤ t) (u : M →ₗ[A] N)
    (hker : K ^ t ≤ Module.annihilator A (ker u))
    (hcoker : K ^ t ≤ Module.annihilator A (N ⧸ range u)) :
    K ^ (2 * t) ≤ Module.annihilator A
      (ker ((J • ⊤ : Submodule A M).mapQ (J • ⊤ : Submodule A N) u
        (Submodule.smul_top_le_comap_smul_top J u))) ∧
    K ^ (2 * t) ≤ Module.annihilator A
      ((N ⧸ (J • ⊤ : Submodule A N)) ⧸
        range ((J • ⊤ : Submodule A M).mapQ (J • ⊤ : Submodule A N) u
          (Submodule.smul_top_le_comap_smul_top J u))) := by
  sorry

end LinearMap
