/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B4
-/
module

public import Sheaf.Paper.ComponentLiftLisseSectionComparison
public import Sheaf.CategoryTheory.ProperFaceMatchingObject
public import WeilConjectures.CategoryTheory.Sites.WeaklyContractible

/-!
# Testing the derived section unit on compatible acyclic hypercovers

Source: Stacks Project, Tag 09A2, with the functorial normalization of
`Sheaf.Paper.AcyclicHypercoverPullbackNormalization`.
(blueprint: lem-sfb-component-hypercover-unit-criterion).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- Bijective section pullbacks on compatible weakly contractible hypercovers test
invertibility of derived sections applied to the actual derived adjunction unit.
There are no lisseness, affineness, or component-space assumptions in this criterion.

Source: Stacks Project, Tag 09A2; the functorial normalization in
`lem-sfb-acyclic-hypercover-pullback-normalization`, transported through
`lem-sfb-internal-module-operations-transport`, and weakly etale site localization
`lem-sfb-coefficient-sections-localization`.
(blueprint: lem-sfb-component-hypercover-unit-criterion).

Proof: regard U and V as simplicial objects over the terminal objects of their
pro-etale sites, using their structure maps. The displayed limiting cones are
proper-face matching objects; in degree zero their vertices are the specified
terminal objects. Uniqueness of limits transports the singleton covering property
to every proper-face matching arrow. The equations for g and its simplicial
operators give a map from V to the base change of U. Transport the internal module
M through the exact internal/sectionwise equivalence. Weakly etale localization
identifies evaluation at a site object with terminal evaluation after scheme
pullback, including the canonical coefficient transport. The unit compatibility of
that equivalence identifies section restriction with pullback of sections of M
along g_n, followed by the canonical pullback-composition isomorphism. Therefore
the assumed bijections make each nonnegative component of the alternating-face
section cochain map invertible; negative components are maps between zero objects.
The inverses commute with the differential by multiplying the cochain-map identity
on both sides by the degreewise inverses, so the map is an isomorphism of complexes.
Apply the derived-category localization functor. Acyclic hypercover pullback
normalization identifies it, through the augmentation-normalized comparison
isomorphisms, with the actual derived-unit section pullback. Exact equivalence
transports this square back to internal modules, including the unit and terminal
section maps. Finally cancel the terminal-section Leray comparison and the exact
single-degree pullback comparison, which are isomorphisms. This proves that derived
sections of the unit itself is invertible. This argument uses only bounded-below
section complexes of degree-zero modules, and also applies to empty hypercovers
and zero modules. -/
theorem componentHypercoverUnitCriterion
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (U : SimplicialObject Y.ProEt) (V : SimplicialObject X.ProEt)
    (g : ∀ n : ℕ, (V _⦋n⦌).left ⟶ (U _⦋n⦌).left)
    (hU : ∃ (C : ∀ n : ℕ, Cone (U.properFaceDiagram n))
        (μ : ∀ n : ℕ, U _⦋n⦌ ⟶ (C n).pt),
      (C 0).pt = Scheme.ProEt.mk (𝟙 Y) ∧
      (∀ n : ℕ, Nonempty (IsLimit (C n))) ∧
      (∀ (n : ℕ) (b : SimplicialObject.ProperFaceCategory n),
        μ n ≫ (C n).π.app (op b) = U.map b.obj.hom.op) ∧
      (∀ n : ℕ, Presieve.singleton (μ n) ∈ Scheme.ProEt.precoverage Y (C n).pt))
    (hV : ∃ (C : ∀ n : ℕ, Cone (V.properFaceDiagram n))
        (μ : ∀ n : ℕ, V _⦋n⦌ ⟶ (C n).pt),
      (C 0).pt = Scheme.ProEt.mk (𝟙 X) ∧
      (∀ n : ℕ, Nonempty (IsLimit (C n))) ∧
      (∀ (n : ℕ) (b : SimplicialObject.ProperFaceCategory n),
        μ n ≫ (C n).π.app (op b) = V.map b.obj.hom.op) ∧
      (∀ n : ℕ, Presieve.singleton (μ n) ∈ Scheme.ProEt.precoverage X (C n).pt))
    (wU : ∀ n : ℕ, (Scheme.ProEt.topology Y).IsWeaklyContractible.{u + 1} (U _⦋n⦌))
    (wV : ∀ n : ℕ, (Scheme.ProEt.topology X).IsWeaklyContractible.{u + 1} (V _⦋n⦌))
    (hg : ∀ n : ℕ, g n ≫ (U _⦋n⦌).hom = (V _⦋n⦌).hom ≫ f)
    (hnat : ∀ (m n : SimplexCategoryᵒᵖ) (a : m ⟶ n),
      (V.map a).left ≫ g n.unop.len = g m.unop.len ≫ (U.map a).left)
    (M : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ.X Y))
    (hbij : ∀ n : ℕ, Function.Bijective
      (componentLiftSectionPullback Λ (g n) ((upperStar Λ.X (U _⦋n⦌).hom).obj M))) :
    IsIso ((condensedModuleSections Λ.X Y).rightDerivedFunctor.map
      ((derivedUpperStarLowerStarAdjunction Λ.X f).unit.app
        ((DerivedCategory.singleFunctor _ 0).obj M))) := by sorry

end AlgebraicGeometry.ProEtale.CondensedRing
