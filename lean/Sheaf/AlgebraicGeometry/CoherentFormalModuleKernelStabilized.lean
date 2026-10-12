module

public import Sheaf.AlgebraicGeometry.CoherentFormalModule
import Sheaf.AlgebraicGeometry.CoherentFormalModuleKernelStabilizedBound
import Sheaf.AlgebraicGeometry.CoherentFormalModuleKernelStabilizedSystem

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

/-- Stabilized kernel-image data used in the formal-kernel construction.

Source: Stacks Project, Lemma 087X, claims (a)--(b), via the affine
Artin--Rees argument. The proof is deferred to the corresponding DAG node.
(blueprint: lem-weil-pbc-formal-kernel-stabilized-aux).
-/
theorem coherentFormalModule_kernel_stabilized_aux {X : Scheme.{u}} [IsNoetherian X]
    (I : X.IdealSheafData) (F H : CoherentFormalModule X I) (α : F ⟶ H) :
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
            F.obj.map (homOfLE (Nat.le_add_right m c)).op) = j.app (op m)) := by
  obtain ⟨c, hc⟩ := coherentFormalModule_kernel_stabilized_bound I F H α
  obtain ⟨S, j, hS⟩ := coherentFormalModule_kernel_stabilized_system I F H α c hc
  exact ⟨c, hc, S, j, hS⟩

end AlgebraicGeometry
