/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T3
-/
module

public import Sheaf.CategoryTheory.GrothendieckComposablePair
public import Sheaf.CategoryTheory.CartanEilenbergPresentation
public import Mathlib.Algebra.Homology.Embedding.ExtendHomology

/-! # CartanEilenbergAcyclicAugmentation

Source: Stacks Project, Derived Categories, Tags 015N and 015K.
(blueprint: lem-sp-ce-acyclic-augmentation).
-/

@[expose] public section

universe uA vA uB vB uC vC

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- The common augmentation into vertical-degree-zero total summands is natural
and a quasi-isomorphism under the injective acyclicity assumption. Its prescribed
components determine the map uniquely: in negative degrees the source is zero.
Source: Stacks Project, Derived Categories, Tags 015N and 015K.
(blueprint: lem-sp-ce-acyclic-augmentation).

Proof: In nonnegative degree n take the component displayed below, inserting the
mapped common augmentation into the (n,0) total summand. In negative degrees use
the unique map from the zero source. The horizontal differential equation is the
bicomplex augmentation square; the vertical differential kills the augmentation,
so the signed vertical total differential contributes zero. The comparison square
follows degreewise from comm_e and functoriality of extension and total inclusions;
negative source terms are zero. Each column resolves F(J^p) with injective terms.
Since J^p is injective, applying G gives zero positive column cohomology and
degree-zero cohomology GF(J^p), compatibly with the augmentation. Filter the cone
of the augmentation by horizontal degree. The resulting column complexes are
acyclic. The double complex has first-quadrant support, making the filtration
finite in every total degree. The column spectral sequence therefore has zero
abutment. The augmentation cone is acyclic, which is exactly that a is a
quasi-isomorphism. This argument includes degree zero and zero objects. -/
theorem exists_cartanEilenberg_acyclic_augmentation
    {A : Type uA} [Category.{vA} A] [Abelian A] [IsGrothendieckAbelian.{vA} A]
    {B : Type uB} [Category.{vB} B] [Abelian B] [IsGrothendieckAbelian.{vB} B]
    {C : Type uC} [Category.{vC} C] [Abelian C] [IsGrothendieckAbelian.{vC} C]
    [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C]
    (F : A ⥤ B) (G : B ⥤ C) [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteLimits G]
    (hFG : (⟨F, G⟩ : GrothendieckComposablePair A B C).SendsInjectivesToAcyclics) :
    ∃ a : ∀ P : CartanEilenbergPresentation F,
        (((F ⋙ G).mapHomologicalComplex (ComplexShape.up ℕ)).obj P.J.cocomplex).extend
          ComplexShape.embeddingUpNat ⟶ P.total G,
      (∀ P : CartanEilenbergPresentation F, (∀ n : ℕ, (a P).f (n : ℤ) =
            (HomologicalComplex.extendXIso
              (((F ⋙ G).mapHomologicalComplex (ComplexShape.up ℕ)).obj P.J.cocomplex)
              ComplexShape.embeddingUpNat (rfl : (n : ℤ) = n)).hom ≫
            G.map (F.map (P.J.cocomplex.extendXIso ComplexShape.embeddingUpNat
              (rfl : (n : ℤ) = n)).inv ≫ (P.e.f (n : ℤ)).f 0) ≫
            (HomologicalComplex.extendXIso
              ((G.mapHomologicalComplex (ComplexShape.up ℕ)).obj (P.I.X (n : ℤ)))
              ComplexShape.embeddingUpNat (rfl : (0 : ℤ) = 0)).inv ≫
            HomologicalComplex₂.ιTotalOrZero
              ((CartanEilenbergPresentation.mappedFunctor G).obj P.I)
              (ComplexShape.up ℤ) (n : ℤ) 0 (n : ℤ))) ∧
      (∀ P : CartanEilenbergPresentation F, QuasiIso (a P)) ∧
      (∀ (P Q : CartanEilenbergPresentation F) (c : P.Comparison Q),
        HomologicalComplex.extendMap
            (((F ⋙ G).mapHomologicalComplex (ComplexShape.up ℕ)).map c.β)
            ComplexShape.embeddingUpNat ≫ a Q =
          a P ≫ HomologicalComplex₂.total.map
            ((CartanEilenbergPresentation.mappedFunctor G).map c.α)
            (ComplexShape.up ℤ)) := by
  sorry

end CategoryTheory
