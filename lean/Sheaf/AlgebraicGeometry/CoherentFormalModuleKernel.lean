/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J1
-/
module

public import Sheaf.AlgebraicGeometry.CoherentFormalModule
public import Sheaf.AlgebraicGeometry.Modules.QuasiCoherentCokernelImage

/-!
# Kernels in coherent formal modules

Source: Stacks Project, Cohomology of Schemes, proof of Lemma 087X
(blueprint: lem-weil-pbc-coherent-formal-module-kernel).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/--
Source: Stacks Project, Cohomology of Schemes, proof of Lemma 087X, claims (a)--(d)
(blueprint: lem-weil-pbc-coherent-formal-module-kernel).
Proof:
1. Transitions of a coherent formal module are epimorphisms and identify every lower
   level with the appropriate quotient of a higher level. Choose a finite affine
   Noetherian cover (pqf-def-locnoeth). On each affine, the tilde/Gamma adjunction and
   lem-weil-pbc-coherent-formal-modules-affine identify the systems with M/I^n M and
   N/I^n N for finite modules over the Noetherian adic completion, and alpha with f.
2. Apply lem-weil-pbc-artin-rees to K = ker f inside M and to im f inside N; take the
   maximum of the bounds on the finite cover. Then f⁻¹(I^l N) lies in K + I^(l-c) M,
   so the image of the levelwise kernel in level m is (K + I^m M)/I^m M for l ≥ m+c.
   Kernels and images are quasi-coherent by lem-weil-pbc-quasi-coherent-module-kernel
   and lem-weil-pbc-quasi-coherent-module-cokernel-image; coherence follows from
   lem-weil-pbc-coherent-kernel-cokernel-locnoeth. Equality on the cover gives (1).
3. The transition restrictions on stabilized images give the inverse system S.
   By lem-weil-pbc-ideal-times-quasi-coherent-affine-sections, its reductions have
   affine sections K/(K ∩ I^m M + I^n K) = K/I^n K for m ≥ n+c. Thus the indicated
   quotients are coherent, killed by I^n, and their reductions give the next lower
   level: they form K in Coh(X,I), with the displayed induced transition maps.
4. The inclusion of stabilized images followed by the transitions factors through
   each quotient, giving iota. On affines it is K/I^n K → M/I^n M, hence alpha iota
   vanishes. Any compatible gamma killed by alpha factors through each stabilized
   image, since higher-level transitions of its source are epi. Reducing at level
   n+c modulo I^n gives a compatible factorization through K (the affine adjunction
   and the ideal-product section formula identify the maps).
5. For uniqueness, ker(iota at level n+c) has affine sections
   (K ∩ I^(n+c) M)/I^(n+c) K, contained in I^n K/I^(n+c) K by Artin--Rees. Its
   transition to level n vanishes. A map to K killed by iota is therefore zero at
   level n after precomposition with the epi transition from level n+c of its
   source. Apply this to the difference of two factorizations. No termwise
   injectivity of iota is asserted.
-/
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
  sorry

end AlgebraicGeometry
