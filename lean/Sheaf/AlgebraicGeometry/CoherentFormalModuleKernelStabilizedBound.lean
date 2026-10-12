module

public import Sheaf.AlgebraicGeometry.CoherentFormalModule

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

/-- A uniform bound for stabilization of the kernel images.

Source: Stacks Project, Lemma 087X, claims (a)--(b), affine Artin--Rees argument.
(blueprint: new-kernel-stabilized-bound).
The proof chooses a finite affine cover, applies Artin--Rees to the kernel on each
affine, and takes the maximum of the resulting bounds; equality of the resulting
quasi-coherent submodules is checked on the cover.
-/
theorem coherentFormalModule_kernel_stabilized_bound {X : Scheme.{u}} [IsNoetherian X]
    (I : X.IdealSheafData) (F H : CoherentFormalModule X I) (α : F ⟶ H) :
    ∃ c : ℕ, ∀ (l m : ℕ) (h : m + c ≤ l),
      Subobject.mk
          (Abelian.image.ι (kernel.ι (α.hom.app (op l)) ≫
            F.obj.map (homOfLE (Nat.le_trans (Nat.le_add_right m c) h)).op)) =
        Subobject.mk
          (Abelian.image.ι (kernel.ι (α.hom.app (op (m + c))) ≫
            F.obj.map (homOfLE (Nat.le_add_right m c)).op)) := by
  sorry

end AlgebraicGeometry
