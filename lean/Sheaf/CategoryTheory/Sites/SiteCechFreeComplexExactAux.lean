module

public import Sheaf.CategoryTheory.SiteCechComplex
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
import Sheaf.Paper.PowerSetComplexContractible

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

/-- The evaluated free Čech complex has a contracting identity in each positive degree.
Source: Stacks Project, Cohomology on Sites, Tags 03AT and 03F5.
(blueprint: lem-weil-pbc-site-cech-free-complex-exact-fibrewise)

Proof: Fix X. Partition a basis pair (t,a) by φ = a ≫ pr(0) ≫ hom(t(0)).
For each φ let Lφ be the disjoint union of maps b:X→f(i) with b≫hom(i)=φ.
The chosen product universal property identifies basis pairs in degree p with
(p+1)-tuples in Lφ: project a to obtain the tuple; conversely take its unique
product lift. These inverse identifications commute with deleting coordinates
by indexMap_pr. Extend them R(X)-linearly to identify the evaluated complex
with the direct sum, over φ:X→U, of the power-set complexes on Lφ.
For each nonempty Lφ choose one element and prefix it to tuples. On an empty
Lφ every positive-length tuple module is zero, and take the zero map.
The power-set contracting identities say d h + h d = identity at degree n+1,
also when n=0. Taking the direct sum of the prefix maps (finite support stays
finite) and transporting through the basis identifications gives h and k.
These are maps only at the fixed X; no naturality in X is asserted. -/
theorem freeComplex_evaluation_contracting (R : Cᵒᵖ ⥤ RingCat.{v})
    (n : ℕ) (X : Cᵒᵖ) :
    ∃ h : ((S.freeComplex R).X (n + 1)).obj X ⟶
        ((S.freeComplex R).X (n + 2)).obj X,
      ∃ k : ((S.freeComplex R).X n).obj X ⟶
          ((S.freeComplex R).X (n + 1)).obj X,
        h ≫ ((S.freeComplex R).d (n + 2) (n + 1)).app X +
          ((S.freeComplex R).d (n + 1) n).app X ≫ k = 𝟙 _ := by sorry

end CategoryTheory.SiteCechComplex
