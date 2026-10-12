/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B2
-/
module

public import Sheaf.CategoryTheory.SiteCechComplex
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Abelian
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
import Sheaf.Paper.PowerSetComplexContractible

/-!
# Free module chains on chosen site Čech products

Source: Stacks Project, Cohomology on Sites, Tags 03AT and 03F5.
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.SiteCechComplex

variable {C : Type u} [Category.{v} C] {T : Type v} {U : C}
  {f : T → C} {hom : ∀ t, f t ⟶ U} (S : SiteCechComplex f hom)

/-- The coproduct of representables on the degree-p products, as a presheaf of sets.
Source: Stacks 03AT (blueprint: lem-weil-pbc-site-cech-free-complex-exact). -/
def tuplePresheaf (p : ℕ) : Cᵒᵖ ⥤ Type v where
  obj X := Σ t : Fin (p + 1) → T, X.unop ⟶ S.W p t
  map g := ↾fun x ↦ ⟨x.1, g.unop ≫ x.2⟩
  map_id X := by
    apply ConcreteCategory.hom_ext
    intro x
    change (⟨x.1, (𝟙 X.unop) ≫ x.2⟩ :
      Σ t : Fin (p + 1) → T, X.unop ⟶ S.W p t) = x
    rw [Category.id_comp]
  map_comp g h := by
    apply ConcreteCategory.hom_ext
    intro x
    change (⟨x.1, (h.unop ≫ g.unop) ≫ x.2⟩ :
      Σ t : Fin (p + 1) → T, _ ⟶ S.W p t) = ⟨x.1, h.unop ≫ (g.unop ≫ x.2)⟩
    rw [Category.assoc]

/-- A map of tuple indices induces a map of the corresponding representable sums.
Source: Stacks 03AT (blueprint: lem-weil-pbc-site-cech-free-complex-exact). -/
def tupleMap {p q : ℕ} (α : Fin (q + 1) → Fin (p + 1)) :
    S.tuplePresheaf p ⟶ S.tuplePresheaf q where
  app X := ↾fun x ↦ ⟨x.1 ∘ α, x.2 ≫ S.indexMap x.1 α⟩
  naturality X Y g := by
    apply ConcreteCategory.hom_ext
    intro x
    change (⟨x.1 ∘ α, (g.unop ≫ x.2) ≫ S.indexMap x.1 α⟩ :
      Σ t : Fin (q + 1) → T, Y.unop ⟶ S.W q t) =
      ⟨x.1 ∘ α, g.unop ≫ (x.2 ≫ S.indexMap x.1 α)⟩
    rw [Category.assoc]

/-- The simplicial representable sums; index-map laws follow from product uniqueness.
Source: Stacks 03AT (blueprint: lem-weil-pbc-site-cech-free-complex-exact). -/
abbrev tupleSimplicial : SimplicialObject (Cᵒᵖ ⥤ Type v) where
  obj n := S.tuplePresheaf n.unop.len
  map α := S.tupleMap α.unop.toOrderHom
  map_id n := by
    have hi (t : Fin (n.unop.len + 1) → T) : S.indexMap t id = 𝟙 _ := by
      obtain ⟨c, _, hu⟩ := S.universal n.unop.len t (S.W n.unop.len t)
        (S.pr n.unop.len t) (S.comm n.unop.len t)
      apply (hu _ ?_).trans (hu _ (fun k ↦ Category.id_comp _)).symm
      intro k
      exact S.indexMap_pr t id k
    apply NatTrans.ext
    funext X
    apply ConcreteCategory.hom_ext
    intro x
    change (⟨x.1 ∘ id, x.2 ≫ S.indexMap x.1 id⟩ :
      Σ t : Fin (n.unop.len + 1) → T, X.unop ⟶ S.W n.unop.len t) = x
    rw [hi, Category.comp_id]
    cases x
    rfl
  map_comp α β := by
    have hi (t) : S.indexMap t (α.unop.toOrderHom ∘ β.unop.toOrderHom) =
        S.indexMap t α.unop.toOrderHom ≫
          S.indexMap (t ∘ α.unop.toOrderHom) β.unop.toOrderHom := by
      let b := S.indexMap t α.unop.toOrderHom ≫
        S.indexMap (t ∘ α.unop.toOrderHom) β.unop.toOrderHom
      obtain ⟨c, _, hu⟩ := S.universal _ _ _
        (fun k ↦ b ≫ S.pr _ _ k)
        (fun k ↦ by simp only [Category.assoc, S.comm])
      apply (hu _ ?_).trans (hu b (fun _ ↦ rfl)).symm
      intro k
      dsimp [b]
      symm
      rw [Category.assoc]
      exact (congrArg (fun h ↦ S.indexMap t α.unop.toOrderHom ≫ h)
        (S.indexMap_pr (t ∘ α.unop.toOrderHom) β.unop.toOrderHom k)).trans
        ((S.indexMap_pr t α.unop.toOrderHom (β.unop.toOrderHom k)).trans
          (S.indexMap_pr t (α.unop.toOrderHom ∘ β.unop.toOrderHom) k).symm)
    apply NatTrans.ext
    funext X
    apply ConcreteCategory.hom_ext
    intro x
    change (⟨x.1 ∘ (α.unop.toOrderHom ∘ β.unop.toOrderHom),
      x.2 ≫ S.indexMap x.1 (α.unop.toOrderHom ∘ β.unop.toOrderHom)⟩ :
      Σ t : Fin (_ + 1) → T, X.unop ⟶ S.W _ t) =
      ⟨(x.1 ∘ α.unop.toOrderHom) ∘ β.unop.toOrderHom,
        (x.2 ≫ S.indexMap x.1 α.unop.toOrderHom) ≫
          S.indexMap (x.1 ∘ α.unop.toOrderHom) β.unop.toOrderHom⟩
    rw [hi, Category.assoc]
    rfl

/-- The actual alternating chain complex of free module presheaves on the tuple sums.
Source: Stacks 03F5 (blueprint: lem-weil-pbc-site-cech-free-complex-exact). -/
noncomputable abbrev freeComplex (R : Cᵒᵖ ⥤ RingCat.{v}) :
    ChainComplex (PresheafOfModules.{v} R) ℕ :=
  (AlgebraicTopology.alternatingFaceMapComplex _).obj
    (S.tupleSimplicial ⋙ PresheafOfModules.free R)

/-- The free Čech chain complex is exact in every positive degree, without a covering.
Source: Stacks Project, Cohomology on Sites, Tags 03AT and 03F5.
(blueprint: lem-weil-pbc-site-cech-free-complex-exact)

Proof: evaluate at an object X. A basis element is a pair (t,a), with t an
(n+1)-tuple of indices and a:X→W(n,t). Partition these elements by
φ = a ≫ pr(n,t,0) ≫ hom(t(0)). The product universal property identifies
that fibre with (n+1)-tuples from Lφ = Σ i, {b:X→f(i) | b≫hom(i)=φ}.
The inverse is the unique product lift of the component maps. The indexMap_pr
law says that each face deletes its indexed component, so this identification
respects the alternating boundary and the R(X)-linear extension to free modules.
The free module on this disjoint union is the direct sum of the tuple complexes
on Lφ. Empty Lφ contributes zero. For nonempty Lφ choose one lift and insert
it as the first coordinate; powerSetComplex_contractible gives exactness at
n+1, including n=0. Direct sums preserve exactness for modules. Finally
module-presheaf kernels and cokernels are objectwise, so evaluation jointly
reflects exactness. All basis sets and free module values lie in universe v;
no natural choice of a lift across objects is needed. -/
theorem freeComplex_exactAt (R : Cᵒᵖ ⥤ RingCat.{v}) (n : ℕ) :
    (S.freeComplex R).ExactAt (n + 1) := by sorry

end CategoryTheory.SiteCechComplex
