/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NS
-/
module

public import Mathlib.CategoryTheory.Sites.Precoverage
public import Mathlib.CategoryTheory.Limits.FormalCoproducts.Basic
public import Sheaf.CategoryTheory.ProperFaceMatchingObject
import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers

/-!
# Hypercovers finite in each degree from a finite covering basis

Source: Stacks Project, Hypercoverings, Tag 094K (lemma-w-contractible), using the
split-skeleton construction of Tag 0DAV and the hypercover definition of Tag 01G5.
(blueprint: lem-weil-pbc-site-finite-basis-hypercover-existence)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

namespace CategoryTheory

/-- A finite covering basis gives a hypercover finite in every degree.
Source: Stacks Project, Hypercoverings, Tags 094K, 0DAV and 01G5.
(blueprint: lem-weil-pbc-site-finite-basis-hypercover-existence)

Proof: Work in the slice over `T`, whose terminal object is `id_T`, whose pullbacks
are those of `C`, and whose covers are the underlying covers. Choose a finite basis
cover in degree zero. Terminal objects and pullbacks give finite limits
[lem-weil-pbc-finite-limits-from-terminal-pullbacks]. The terminal formal family is
`{id_T}` and pullbacks of formal families have components the componentwise pullbacks,
indexed by pairs with equal target index [def-weil-pbc-formal-coproduct]. Finite-index
families are closed under these operations, so finite boundary limits have finite
index sets, with the same universal property against arbitrary formal families.
Inductively cover each component of the next boundary limit by a finite basis cover.
Attach those as the new nondegenerate simplices to the split truncation, retaining
the prescribed degenerate copies [lem-weil-pbc-site-hypercover-finite-extension].
Its terms remain finite basis families: only finitely many surjections between finite
ordered sets occur. The attachment theorem gives all operators and composition laws.
For each matching component, repeatedly adjoin the finitely many prescribed degenerate
arrows to the chosen cover; the adjoining hypothesis shows the resulting family covers.
This includes empty covers and empty matching families. Recursively choose extensions.
Each degree and each operator stabilizes; taking their permanent values gives a functor,
since each functor identity can be checked at a finite stage containing its degrees
[def-weil-pbc-simplicial-object]. The slice gives the augmentation and degree-zero
matching object. Every fixed degree retains its finite basis family and matching cover. -/
theorem exists_site_finite_basis_hypercover
    {C : Type u} [SmallCategory C] [HasPullbacks C]
    (J : Precoverage C) [J.HasIsos] [J.IsStableUnderComposition] [J.IsStableUnderBaseChange]
    (B : Set C)
    (hcover : ∀ T : C, ∃ (I : Type u) (U : I → C) (f : ∀ i : I, U i ⟶ T),
      Finite I ∧ (∀ i : I, U i ∈ B) ∧ Presieve.ofArrows U f ∈ J T)
    (hadjoin : ∀ (T : C) (I : Type u) [Finite I] (U : I → C)
      (f : ∀ i : I, U i ⟶ T), (∀ i : I, U i ∈ B) →
      Presieve.ofArrows U f ∈ J T → ∀ (V : C), V ∈ B → ∀ (g : V ⟶ T),
        Presieve.ofArrows U f ⊔ Presieve.singleton g ∈ J T)
    (T : C) :
    ∃ (K : SimplicialObject (FormalCoproduct.{u} (Over T)))
      (M : ∀ n : ℕ, Cone (K.properFaceDiagram n))
      (μ : ∀ n : ℕ, K _⦋n⦌ ⟶ (M n).pt),
      (∀ n : ℕ, Finite (K _⦋n⦌).I) ∧
      (∀ (n : ℕ) (i : (K _⦋n⦌).I), ((K _⦋n⦌).obj i).left ∈ B) ∧
      (M 0).pt = (FormalCoproduct.incl (Over T)).obj (Over.mk (𝟙 T)) ∧
      (∀ n : ℕ, Nonempty (IsLimit (M n))) ∧
      (∀ (n : ℕ) (a : SimplicialObject.ProperFaceCategory n),
        μ n ≫ (M n).π.app (op a) = K.map a.obj.hom.op) ∧
      (∀ (n : ℕ) (j : (M n).pt.I),
        Presieve.ofArrows
          (fun i : {i : (K _⦋n⦌).I // (μ n).f i = j} ↦ ((K _⦋n⦌).obj i.val).left)
          (fun i : {i : (K _⦋n⦌).I // (μ n).f i = j} ↦
            ((μ n).φ i.val).left ≫
              eqToHom (congrArg (fun k ↦ ((M n).pt.obj k).left) i.property)) ∈
          J ((M n).pt.obj j).left) := by
  sorry

end CategoryTheory
