/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T3
-/
module

public import Sheaf.CategoryTheory.GrothendieckComposablePair
public import Sheaf.CategoryTheory.CartanEilenbergPresentation
import Sheaf.CategoryTheory.CartanEilenbergAcyclicAugmentation
public import Mathlib.Algebra.Homology.Embedding.ExtendHomology

/-! # CartanEilenbergAugmentationComparison

Source: Stacks Project, Derived Categories, Tags 015N and 015K.
(blueprint: lem-sp-ce-augmentation-comparison).
-/

@[expose] public section

universe uA vA uB vB uC vC

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- The acyclic column augmentation gives the total-cohomology comparison, naturally
in presentation comparisons, and fixes it by the canonical resolution computation.
Source: Stacks Project, Derived Categories, Tags 015N and 015K.
(blueprint: lem-sp-ce-augmentation-comparison).

Proof: Insert the common augmentation into vertical-degree-zero total summands using
the extension isomorphisms. The bicomplex augmentation squares verify the horizontal
differential equation; its vertical equation is zero, and the totalization sign
therefore introduces no extra term. Each column is an injective resolution of F(J^p).
Acyclicity gives zero positive G-cohomology and identifies degree zero with GF(J^p).
Filter the cone of the augmentation by horizontal degree. Its associated column
complexes are acyclic. In each total degree the first-quadrant filtration is finite,
so the spectral sequence of the cone has zero abutment. Hence the augmentation
induces isomorphisms on homology. Invert them and compose with extendHomologyIso
and the inverse of J.isoRightDerivedObj. This gives h and the augmentation equation.
The square for two augmentations commutes by the two comparison augmentation
squares. Applying homology, then cancelling the augmentation isomorphism and using
naturality of injective-resolution cohomology, gives the stated comparison square. -/
theorem exists_cartanEilenberg_augmentation_comparison
    {A : Type uA} [Category.{vA} A] [Abelian A] [IsGrothendieckAbelian.{vA} A]
    {B : Type uB} [Category.{vB} B] [Abelian B] [IsGrothendieckAbelian.{vB} B]
    {C : Type uC} [Category.{vC} C] [Abelian C] [IsGrothendieckAbelian.{vC} C]
    [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C]
    (F : A ⥤ B) (G : B ⥤ C) [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteLimits G]
    (hFG : (⟨F, G⟩ : GrothendieckComposablePair A B C).SendsInjectivesToAcyclics) :
    ∃ (h : ∀ (P : CartanEilenbergPresentation F) (n : ℕ),
        (P.total G).homology (n : ℤ) ≅ ((F ⋙ G).rightDerived n).obj P.X),
      (∀ (P Q : CartanEilenbergPresentation F) (c : P.Comparison Q) (n : ℕ),
        HomologicalComplex.homologyMap (HomologicalComplex₂.total.map
          ((CartanEilenbergPresentation.mappedFunctor G).map c.α)
            (ComplexShape.up ℤ)) (n : ℤ) ≫ (h Q n).hom =
          (h P n).hom ≫ ((F ⋙ G).rightDerived n).map c.f) ∧
      (∀ P : CartanEilenbergPresentation F,
        ∃ a : (((F ⋙ G).mapHomologicalComplex (ComplexShape.up ℕ)).obj P.J.cocomplex).extend
            ComplexShape.embeddingUpNat ⟶ P.total G,
          (∀ n : ℕ, a.f (n : ℤ) =
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
              (ComplexShape.up ℤ) (n : ℤ) 0 (n : ℤ)) ∧
          (∀ n : ℕ, HomologicalComplex.homologyMap a (n : ℤ) ≫ (h P n).hom =
            (HomologicalComplex.extendHomologyIso
              (((F ⋙ G).mapHomologicalComplex (ComplexShape.up ℕ)).obj P.J.cocomplex)
              ComplexShape.embeddingUpNat (rfl : (n : ℤ) = n)).hom ≫
              (P.J.isoRightDerivedObj (F ⋙ G) n).inv)) := by
  classical
  obtain ⟨a, ha, hqi, hanat⟩ := exists_cartanEilenberg_acyclic_augmentation F G hFG
  let (P : CartanEilenbergPresentation F) : QuasiIso (a P) := hqi P
  let h (P : CartanEilenbergPresentation F) (n : ℕ) :=
    (asIso (HomologicalComplex.homologyMap (a P) (n : ℤ))).symm ≪≫
      HomologicalComplex.extendHomologyIso
        (((F ⋙ G).mapHomologicalComplex (ComplexShape.up ℕ)).obj P.J.cocomplex)
        ComplexShape.embeddingUpNat (rfl : (n : ℤ) = n) ≪≫
      (P.J.isoRightDerivedObj (F ⋙ G) n).symm
  have heq (P : CartanEilenbergPresentation F) (n : ℕ) :
      HomologicalComplex.homologyMap (a P) (n : ℤ) ≫ (h P n).hom =
        (HomologicalComplex.extendHomologyIso
          (((F ⋙ G).mapHomologicalComplex (ComplexShape.up ℕ)).obj P.J.cocomplex)
          ComplexShape.embeddingUpNat (rfl : (n : ℤ) = n)).hom ≫
          (P.J.isoRightDerivedObj (F ⋙ G) n).inv := by
    simp [h]
  refine ⟨h, ?_, fun P ↦ ⟨a P, ha P, heq P⟩⟩
  intro P Q c n
  rw [← cancel_epi (HomologicalComplex.homologyMap (a P) (n : ℤ))]
  rw [← HomologicalComplex.homologyMap_comp_assoc, ← hanat P Q c,
    HomologicalComplex.homologyMap_comp_assoc, heq Q n]
  rw [← Category.assoc _ (h P n).hom, heq P n]
  rw [HomologicalComplex.extendHomologyIso_hom_naturality_assoc]
  rw [Category.assoc]
  congr 1
  exact (InjectiveResolution.isoRightDerivedObj_inv_naturality c.f P.J Q.J c.β
    c.comm_ι (F ⋙ G) n).symm

end CategoryTheory
