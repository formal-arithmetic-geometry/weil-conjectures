module

public import Sheaf.AlgebraicGeometry.CoherentFormalModule
import Sheaf.AlgebraicGeometry.CoherentFormalModulesAffine
import Sheaf.AlgebraicGeometry.CoherentKernelCokernelLocallyNoetherian
import Sheaf.AlgebraicGeometry.Modules.IdealTimesQuasiCoherentAffineSections
import Sheaf.AlgebraicGeometry.Modules.QuasiCoherentCokernelImage
import Sheaf.RingTheory.AdicCompletionNoetherian
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel
import Mathlib.RingTheory.Filtration

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

/-- Quotient coherent formal-module system associated to stabilized kernel images.

Source: Stacks Project, Lemma 087X, claim (c) and the eventual kernel calculation,
under the stabilized-image equality supplied by claims (a)--(b).
The proof is deferred to the corresponding DAG node.
(blueprint: lem-weil-pbc-formal-kernel-quotient-aux).
-/
theorem coherentFormalModule_kernel_quotient_aux {X : Scheme.{u}} [IsNoetherian X]
    (I : X.IdealSheafData) (F H : CoherentFormalModule X I) (α : F ⟶ H)
    (c : ℕ) (S : ℕᵒᵖ ⥤ X.Modules) (j : S ⟶ F.obj)
    (hc : ∀ (l m : ℕ) (h : m + c ≤ l),
      Subobject.mk
          (Abelian.image.ι (kernel.ι (α.hom.app (op l)) ≫
            F.obj.map (homOfLE (Nat.le_trans (Nat.le_add_right m c) h)).op)) =
        Subobject.mk
          (Abelian.image.ι (kernel.ι (α.hom.app (op (m + c))) ≫
            F.obj.map (homOfLE (Nat.le_add_right m c)).op)))
    (hS : ∀ m : ℕ, ∃ e : S.obj (op m) ≅
      Abelian.image (kernel.ι (α.hom.app (op (m + c))) ≫
        F.obj.map (homOfLE (Nat.le_add_right m c)).op),
      e.hom ≫ Abelian.image.ι (kernel.ι (α.hom.app (op (m + c))) ≫
        F.obj.map (homOfLE (Nat.le_add_right m c)).op) = j.app (op m)) :
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
      (∀ n : ℕ, kernel.ι (ι.hom.app (op (n + c))) ≫
        K.obj.map (homOfLE (Nat.le_add_right n c)).op = 0) := by
  sorry

end AlgebraicGeometry
