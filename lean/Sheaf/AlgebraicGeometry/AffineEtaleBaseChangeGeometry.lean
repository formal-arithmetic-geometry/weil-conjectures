/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
module

public import Sheaf.AlgebraicGeometry.FullAffineEtaleSite
public import Mathlib.CategoryTheory.Sites.Continuous

/-!
# AffineEtaleBaseChangeGeometry

Source: Stacks Project, Étale Cohomology 0EYL; Sites 09YL.
(blueprint: lem-weil-pbc-affine-etale-base-change-system).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

/-- The categorical data occurring in an affine étale base-change system. -/
structure AffineEtaleBaseChangeSystemData
    {I : Type u} [Preorder I]
    (D : Iᵒᵖ ⥤ Scheme.{u}) (c : Cone D) where
  U : ∀ (i j : I), i ≤ j → (D.obj (op i)).FullAffineEtale ⥤
    (D.obj (op j)).FullAffineEtale
  v : ∀ i : I, (D.obj (op i)).FullAffineEtale ⥤ c.pt.FullAffineEtale
  p : ∀ (i j : I) (h : i ≤ j),
    U i j h ⋙ fullAffineEtaleInclusion (D.obj (op j)) ⋙
      Etale.forget (D.obj (op j)) ⋙ Over.forget (D.obj (op j)) ⟶
    fullAffineEtaleInclusion (D.obj (op i)) ⋙
      Etale.forget (D.obj (op i)) ⋙ Over.forget (D.obj (op i))
  q : ∀ i : I,
    v i ⋙ fullAffineEtaleInclusion c.pt ⋙ Etale.forget c.pt ⋙ Over.forget c.pt ⟶
    fullAffineEtaleInclusion (D.obj (op i)) ⋙ Etale.forget (D.obj (op i)) ⋙
      Over.forget (D.obj (op i))
  gamma : ∀ (i j k : I) (h : i ≤ j) (h' : j ≤ k),
    U i j h ⋙ U j k h' ≅ U i k (h.trans h')
  delta : ∀ (i j : I) (h : i ≤ j), U i j h ⋙ v j ≅ v i

/-- The normalized cartesian, cocycle, and covering clauses of a base-change system. -/
def affineEtaleBaseChangeGeometry
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : Iᵒᵖ ⥤ Scheme.{u})
    [∀ (i : Iᵒᵖ), CompactSpace (D.obj i)]
    [∀ (i : Iᵒᵖ), QuasiSeparatedSpace (D.obj i)]
    [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a)]
    (c : Cone D) (d : AffineEtaleBaseChangeSystemData D c) : Prop :=
      (∀ i : I, d.U i i le_rfl = 𝟭 _)
      ∧ (∀ (i j : I) (h : i ≤ j) (A : (D.obj (op i)).FullAffineEtale),
        IsPullback ((d.p i j h).app A) ((d.U i j h).obj A).obj.hom
          A.obj.hom (D.map (homOfLE h).op))
      ∧ (∀ (i : I) (A : (D.obj (op i)).FullAffineEtale),
        IsPullback ((d.q i).app A) ((d.v i).obj A).obj.hom A.obj.hom (c.π.app (op i)))
      ∧ (∀ (i k : I) (h : i ≤ k),
        HEq (d.gamma i i k le_rfl h) (Iso.refl (d.U i k h)))
      ∧ (∀ (i k : I) (h : i ≤ k),
        HEq (d.gamma i k k h le_rfl) (Iso.refl (d.U i k h)))
      ∧ (∀ i : I, HEq (d.delta i i le_rfl) (Iso.refl (d.v i)))
      ∧ (∀ (i j k : I) (h : i ≤ j) (h' : j ≤ k)
        (A : (D.obj (op i)).FullAffineEtale),
        ((d.gamma i j k h h').hom.app A).hom.left ≫ (d.p i k (h.trans h')).app A =
          (d.p j k h').app ((d.U i j h).obj A) ≫ (d.p i j h).app A)
      ∧ (∀ (i j : I) (h : i ≤ j) (A : (D.obj (op i)).FullAffineEtale),
        ((d.delta i j h).hom.app A).hom.left ≫ (d.q i).app A =
          (d.q j).app ((d.U i j h).obj A) ≫ (d.p i j h).app A)
      ∧ (∀ (i j k l : I) (h : i ≤ j) (h' : j ≤ k) (h'' : k ≤ l)
        (A : (D.obj (op i)).FullAffineEtale),
        (d.gamma j k l h' h'').hom.app ((d.U i j h).obj A) ≫
            (d.gamma i j l h (h'.trans h'')).hom.app A =
          (d.U k l h'').map ((d.gamma i j k h h').hom.app A) ≫
            (d.gamma i k l (h.trans h') h'').hom.app A)
      ∧ (∀ (i j k : I) (h : i ≤ j) (h' : j ≤ k)
        (A : (D.obj (op i)).FullAffineEtale),
        (d.v k).map ((d.gamma i j k h h').hom.app A) ≫
            (d.delta i k (h.trans h')).hom.app A =
          (d.delta j k h').hom.app ((d.U i j h).obj A) ≫ (d.delta i j h).hom.app A)
      ∧ (∀ (i j : I) (h : i ≤ j) (A : (D.obj (op i)).FullAffineEtale) (R : Presieve A),
        R ∈ fullAffineEtalePrecoverage (D.obj (op i)) A →
          R.map (d.U i j h) ∈ fullAffineEtalePrecoverage (D.obj (op j)) ((d.U i j h).obj A))
      ∧ (∀ (i j : I) (h : i ≤ j) (A B C : (D.obj (op i)).FullAffineEtale)
        (f : B ⟶ A) (g : C ⟶ A), PreservesLimit (cospan f g) (d.U i j h))
      ∧ (∀ (i : I) (A : (D.obj (op i)).FullAffineEtale) (R : Presieve A),
        R ∈ fullAffineEtalePrecoverage (D.obj (op i)) A →
          R.map (d.v i) ∈ fullAffineEtalePrecoverage c.pt ((d.v i).obj A))
      ∧ (∀ (i : I) (A B C : (D.obj (op i)).FullAffineEtale)
        (f : B ⟶ A) (g : C ⟶ A), PreservesLimit (cospan f g) (d.v i))
      ∧ (∀ (i j : I) (h : i ≤ j), (d.U i j h).IsContinuous
          (fullAffineEtaleTopology (D.obj (op i))) (fullAffineEtaleTopology (D.obj (op j))))
      ∧ (∀ i : I, (d.v i).IsContinuous
          (fullAffineEtaleTopology (D.obj (op i))) (fullAffineEtaleTopology c.pt))

/-- Source: Stacks Project 0EYL, the base-change system used in its qcqs proof,
and Sites 00X1 for continuity.

Proof: the limit projections are affine by `AlgebraicGeometry.isAffineHom_π_app`.
Pullback along an affine morphism preserves affine domains and étale structure maps.
Choose restricted pullback for transitions, except that on equal indices choose the
identity, with identity first projection; choose restricted pullback along each cone
projection for `v`. The functor laws follow from the two pullback projections.
Pullback pasting identifies iterated transition pullbacks and transition-cone pullbacks
with the single pullback. Its unique comparison isomorphisms define `gamma` and `delta`;
on diagonal indices choose identity comparisons. Their projection equations follow from
this definition. In each associativity or cone cocycle both composites have the same
first and structure projections, so pullback uniqueness gives equality. Base change
preserves finite jointly surjective étale families, including the empty family, and
pasting preserves every cospan pullback. These facts pass to the full affine subcategories.
Cover preservation and preservation of their pairwise pullbacks imply continuity for
the generated topologies. This proves precisely the geometric clauses, with no sheaf
adjunction assertion.
(blueprint: lem-weil-pbc-affine-etale-base-change-geometry). -/
theorem exists_affineEtale_baseChange_geometry
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : Iᵒᵖ ⥤ Scheme.{u})
    [∀ (i : Iᵒᵖ), CompactSpace (D.obj i)]
    [∀ (i : Iᵒᵖ), QuasiSeparatedSpace (D.obj i)]
    [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a)]
    (c : Cone D) (hc : IsLimit c) :
    ∃ d : AffineEtaleBaseChangeSystemData D c, affineEtaleBaseChangeGeometry D c d := by sorry

end AlgebraicGeometry.Scheme
