/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebraCyclicChain

/-!
# The first piece of a twisted algebra for a cyclic decomposition

Let `P` be a decomposition of `C` into pieces `J₀, …, J_m : C ⥤ D` permuted cyclically by
`F : C ⥤ C` up to `G : D ⥤ D` (`CategoryTheory.Endofunctor.IsoAlgebra.CyclicDecomposition`), and
let `σ_X : X ≅ X` and `τⁿ_Y : Y ≅ Y` be central automorphisms of the objects of `C` and `D` (such
as multiplication by a scalar `b` and by `bⁿ`), compatible with the pieces. Twisting the structure
isomorphism of an algebra `(A, φ)` by `σ` twists the structure isomorphism of its first piece by
`τ^{m+1}`, the first piece being reached after `m + 1` applications of `F`
(`CategoryTheory.Endofunctor.IsoAlgebra.CyclicDecomposition.functorObjTwistIso`).
-/

@[expose] public section

noncomputable section

universe v v' u u'

open CategoryTheory

namespace CategoryTheory.Endofunctor.IsoAlgebra.CyclicDecomposition

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D] {F : C ⥤ C}
  {G : D ⥤ D} {m : ℕ} (P : CyclicDecomposition F G m) (A : IsoAlgebra F)
  (σ : ∀ X : C, X ≅ X) (τ : ℕ → ∀ Y : D, Y ≅ Y)
  (hJ : ∀ i X, (P.J i).map (σ X).hom = (τ 1 ((P.J i).obj X)).hom)
  (hτ : ∀ n Y, (τ (n + 1) Y).hom = (τ 1 Y).hom ≫ (τ n Y).hom)
  (hτnat : ∀ n {Y Y' : D} (f : Y ⟶ Y'), (τ n Y).hom ≫ f = f ≫ (τ n Y').hom)
  (hτ0 : ∀ Y, (τ 0 Y).hom = 𝟙 Y)

include hJ hτ hτnat in
lemma twist_compat (k : Fin m) :
    (P.J k.castSucc).map (IsoAlgebra.mk A.carrier (A.str ≪≫ σ A.carrier)).str.hom ≫
        (P.chain A k.castSucc ≪≫ τ k.castSucc ((P.J 0).obj A.carrier)).hom =
      (P.α k).hom.app A.carrier ≫
        (P.chain A k.succ ≪≫ τ k.succ ((P.J 0).obj A.carrier)).hom := by
  simp only [mk_str, Iso.trans_hom, Functor.map_comp, hJ, chain_succ, Iso.symm_hom,
    Iso.app_inv, Functor.mapIso_hom, Category.assoc, Iso.hom_inv_id_app_assoc, Fin.val_succ,
    Fin.val_castSucc, hτ (k : ℕ)]
  rw [reassoc_of% (hτnat 1 (P.chain A k.castSucc).hom)]

include hJ hτ hτnat hτ0 in
lemma twist_compat_last :
    (P.J (Fin.last m)).map (IsoAlgebra.mk A.carrier (A.str ≪≫ σ A.carrier)).str.hom ≫
        (P.chain A (Fin.last m) ≪≫ τ (Fin.last m) ((P.J 0).obj A.carrier)).hom =
      P.β.hom.app A.carrier ≫
        G.map (P.chain A 0 ≪≫ τ (0 : Fin (m + 1)) ((P.J 0).obj A.carrier)).hom ≫
        (P.strZero A ≪≫ τ (m + 1) ((P.J 0).obj A.carrier)).hom := by
  simp only [mk_str, Iso.trans_hom, Functor.map_comp, hJ, chain_zero, Iso.refl_hom,
    Fin.val_zero, hτ0, Category.comp_id, CategoryTheory.Functor.map_id, strZero,
    Iso.symm_hom, Iso.app_inv, Functor.mapIso_hom, Category.assoc, Fin.val_last, hτ m]
  rw [reassoc_of% (hτnat 1 (P.chain A (Fin.last m)).hom)]
  erw [Category.id_comp, Iso.hom_inv_id_app_assoc]

/-- **The first piece of a twisted algebra**: twisting the structure isomorphism of `A` by the
central automorphisms `σ` twists the structure isomorphism of its first piece by `τ^{m+1}`. -/
def functorObjTwistIso :
    P.functor.obj (IsoAlgebra.mk A.carrier (A.str ≪≫ σ A.carrier)) ≅
      IsoAlgebra.mk (P.functor.obj A).carrier
        ((P.functor.obj A).str ≪≫ τ (m + 1) (P.functor.obj A).carrier) :=
  P.functorObjIsoMk (IsoAlgebra.mk A.carrier (A.str ≪≫ σ A.carrier))
      (fun i ↦ P.chain A i ≪≫ τ i ((P.J 0).obj A.carrier))
      (P.twist_compat A σ τ hJ hτ hτnat) (P.strZero A ≪≫ τ (m + 1) ((P.J 0).obj A.carrier))
      (P.twist_compat_last A σ τ hJ hτ hτnat hτ0) ≪≫
    IsoAlgebra.isoMk (Iso.refl _) (by
      rw [Iso.refl_hom, CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]
      rfl)

end CategoryTheory.Endofunctor.IsoAlgebra.CyclicDecomposition
