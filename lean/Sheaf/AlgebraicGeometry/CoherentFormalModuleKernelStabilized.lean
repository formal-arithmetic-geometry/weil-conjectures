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
  sorry

end AlgebraicGeometry
