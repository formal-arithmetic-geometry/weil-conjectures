/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license.
-/
module

public import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.Algebra.Category.Grp.Adjunctions
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Homology.QuasiIso

/-!
# Small free abelian presheaf chains of a Čech family

Source: Stacks Project, Cohomology on Sites, Tags 03AS, 03AT and 03AU.
-/

@[expose] public section

universe u v

namespace CategoryTheory

open Limits Opposite

namespace SmallCech

variable {C : Type u} [Category.{v} C] (X : C)

/-- The sum of representables of a formal family over X, using only v-small Hom sets.
Source: Stacks 03AS and 03AT. -/
def tupleRepresentables (Y : FormalCoproduct.{v} (Over X)) : Cᵒᵖ ⥤ Type v where
  obj Z := Σ i : Y.I, Z.unop ⟶ (Y.obj i).left
  map g := ↾fun a ↦ ⟨a.1, g.unop ≫ a.2⟩
  map_id Z := by
    apply ConcreteCategory.hom_ext
    intro a
    simp
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    intro a
    simp [Category.assoc]

/-- A map of formal families induces a map between their representable sums.
Source: Stacks 03AS and 03AT. -/
def tupleRepresentablesMap {Y Y' : FormalCoproduct.{v} (Over X)} (f : Y ⟶ Y') :
    tupleRepresentables X Y ⟶ tupleRepresentables X Y' where
  app Z := ↾fun a ↦ ⟨f.f a.1, a.2 ≫ (f.φ a.1).left⟩
  naturality Z W g := by
    apply ConcreteCategory.hom_ext
    intro a
    simp [tupleRepresentables, Category.assoc]

/-- The functor sending a formal family to its coproduct of free abelian representables.
Source: Stacks 03AS and 03AT. -/
noncomputable def freePresheaf :
    FormalCoproduct.{v} (Over X) ⥤ (Cᵒᵖ ⥤ AddCommGrpCat.{v}) where
  obj Y := tupleRepresentables X Y ⋙ AddCommGrpCat.free
  map f := Functor.whiskerRight (tupleRepresentablesMap X f) AddCommGrpCat.free
  map_id Y := by
    apply NatTrans.ext
    funext Z
    change AddCommGrpCat.free.map _ = 𝟙 _
    rw [← AddCommGrpCat.free.map_id]
    congr 1
    apply ConcreteCategory.hom_ext
    intro a
    simp [tupleRepresentablesMap]
  map_comp f g := by
    apply NatTrans.ext
    funext Z
    change AddCommGrpCat.free.map _ =
      AddCommGrpCat.free.map _ ≫ AddCommGrpCat.free.map _
    rw [← AddCommGrpCat.free.map_comp]
    congr 1
    apply ConcreteCategory.hom_ext
    intro a
    simp [tupleRepresentablesMap, Category.assoc]

attribute [local instance] Over.ConstructProducts.over_finiteProducts_of_finiteWidePullbacks

variable [HasFiniteWidePullbacks C] {ι : Type v} (U : ι → C) (π : ∀ i, U i ⟶ X)

/-- The alternating chains of the free abelian representable sums on categorical products.
Source: Stacks 03AT. -/
noncomputable abbrev freeComplex : ChainComplex (Cᵒᵖ ⥤ AddCommGrpCat.{v}) ℕ :=
  (AlgebraicTopology.alternatingFaceMapComplex _).obj
    ((FormalCoproduct.mk ι (fun i ↦ Over.mk (π i))).cech ⋙ freePresheaf X)

/-- The free Čech presheaf chains are exact in positive degrees, for any family.
Source: Stacks Project, Cohomology on Sites, Tags 03AT and 03AU.
(blueprint: lem-sc-small-cech-free-exact)

Proof: Evaluate the chain complex at Z. Its basis in degree n consists of an
(n+1)-tuple of family indices together with a map from Z to the corresponding
product over X. Partition the basis by the composite Z -> X. The product universal
property identifies each fibre with (n+1)-tuples of lifts of that composite to the
family. Face maps delete coordinates. If the lift set is empty, every chain group
of that fibre is zero. Otherwise choose a lift and prepend it: the alternating
boundary satisfies d h + h d = id in positive degrees. Thus every fibre complex
is exact, and so is their direct sum. Kernels and cokernels in abelian presheaves
are evaluated objectwise, so objectwise exactness proves the assertion.
Only the basis and Hom sets must be v-small; Z ranges over C without being part
of a product indexing set. The argument uses no covering assumption. -/
theorem freeComplex_exactAt (q : ℕ) : (freeComplex X U π).ExactAt (q + 1) := by sorry

end SmallCech
end CategoryTheory
