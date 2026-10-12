module

public import Sheaf.AlgebraicGeometry.CoherentFormalModule

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

/-- The stabilized kernel images admit a compatible system of representatives.

Source: Stacks Project, Lemma 087X, construction of claims (a)--(b).
(blueprint: new-kernel-stabilized-system).
The proof restricts the stabilized image inclusions on a finite affine cover and
glues the resulting compatible quasi-coherent systems.
-/
theorem coherentFormalModule_kernel_stabilized_system {X : Scheme.{u}} [IsNoetherian X]
    (I : X.IdealSheafData) (F H : CoherentFormalModule X I) (α : F ⟶ H)
    (c : ℕ)
    (hc : ∀ (l m : ℕ) (h : m + c ≤ l),
      Subobject.mk
          (Abelian.image.ι (kernel.ι (α.hom.app (op l)) ≫
            F.obj.map (homOfLE (Nat.le_trans (Nat.le_add_right m c) h)).op)) =
        Subobject.mk
          (Abelian.image.ι (kernel.ι (α.hom.app (op (m + c))) ≫
            F.obj.map (homOfLE (Nat.le_add_right m c)).op))) :
    ∃ (S : ℕᵒᵖ ⥤ X.Modules) (j : S ⟶ F.obj),
      ∀ m : ℕ, ∃ e : S.obj (op m) ≅
        Abelian.image (kernel.ι (α.hom.app (op (m + c))) ≫
          F.obj.map (homOfLE (Nat.le_add_right m c)).op),
        e.hom ≫ Abelian.image.ι (kernel.ι (α.hom.app (op (m + c))) ≫
          F.obj.map (homOfLE (Nat.le_add_right m c)).op) = j.app (op m) := by
  sorry

end AlgebraicGeometry
