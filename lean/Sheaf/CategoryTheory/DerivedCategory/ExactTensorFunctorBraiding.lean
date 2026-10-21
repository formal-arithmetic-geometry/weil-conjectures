/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NM
-/
module

public import Sheaf.CategoryTheory.DerivedTensorComparison
public import Sheaf.Algebra.Homology.PreservesTotalTensorKFlatQuasiIso
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategory

import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Limits.HasLimits
import Sheaf.CategoryTheory.DerivedCategory.KFlatDerivability
import Sheaf.CategoryTheory.MultivariableDerivedCalculus

/-!
# Exact tensor functors preserve the native derived braiding

Source: Stacks Project, `sites-cohomology.tex`, Tags 0FPQ and 0FPT, and the
cross-functor calculation in the DAG proof
(blueprint: lem-sfb-exact-tensor-functor-derived-braiding).

The K-flat model isomorphism in the node is the inverse of the native localization
counit `Functor.LaxMonoidal.μ DerivedCategory.Q`. The hypothesis `hnormalized` writes
the same square after composing with the source and target counits. Those counits
are invertible on K-flat pairs. This avoids choosing another model comparison.
The two occurrences of `DerivedMonoidal.braiding'` are the independently constructed
native braidings, descended from the Koszul braidings of the homotopy categories.
-/

@[expose] public section

set_option autoImplicit false

universe uC vC wC uD vD wD

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace CategoryTheory.Functor

/-- The prescribed normalized exact tensor comparison intertwines the native braidings.
Source: Stacks Project, Tags 0FPQ (lemma-symmetric-monoidal-cat-complexes) and
0FPT (lemma-symmetric-monoidal-derived); agent extraction of the cross-functor square
(blueprint: lem-sfb-exact-tensor-functor-derived-braiding).

Proof: (1) Precompose the two complex-level braiding composites with each image of a
bidegree coproduct inclusion. The defining equation `hτ` reduces them to the ordinary
braiding square `hbraided`, multiplied by the same Koszul sign. Additivity moves the
sign through F, and the left-adjoint hypothesis gives coproduct uniqueness.
(2) For K-flat P,Q, conjugate the required square by E of the source model isomorphism
and by the tensor of the two exact-functor factorization isomorphisms. Use the native
source braiding normalization, `hnormalized` at Q,P, and naturality of the canonical
factorization to identify its first side with the localized first complex composite.
(3) Native target braiding naturality, `hnormalized` at P,Q, and the target model
normalization identify its second side with the localized second complex composite.
Step (1) identifies these, and cancellation of the two isomorphisms proves the square
on K-flat representatives; no invertibility of t is used.
(4) Closedness and symmetry give colimit preservation by tensoring on either side.
Apply lem-sfb-kflat-derivability, then the n=2 determination assertion of
lem-sfb-multivariable-derived-calculus to the two natural transformations. Agreement on
all localized K-flat pairs implies agreement on every pair of unbounded derived objects.
The complex and homotopy localizations agree through their canonical factorization. -/
theorem exactTensorFunctor_derived_braiding
    {C : Type uC} [Category.{vC} C] [Abelian C] [IsGrothendieckAbelian.{vC} C]
    [HasDerivedCategory.{wC} C] [MonoidalCategory C] [SymmetricCategory C]
    [MonoidalPreadditive C] [MonoidalClosed C] [Abelian.HasFunctorialFlatResolution C]
    {D : Type uD} [Category.{vD} D] [Abelian D] [IsGrothendieckAbelian.{vD} D]
    [HasDerivedCategory.{wD} D] [MonoidalCategory D] [SymmetricCategory D]
    [MonoidalPreadditive D] [MonoidalClosed D] [Abelian.HasFunctorialFlatResolution D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [F.IsLeftAdjoint] [F.PreservesFlat] (M : F.CoreMonoidal)
    (hKFlat : ∀ P : CochainComplex C ℤ, P.IsKFlatForTotalTensor →
      CochainComplex.IsKFlatForTotalTensor ((F.mapHomologicalComplex (.up ℤ)).obj P))
    (τ : (Functor.postcompose₂.obj (F.mapHomologicalComplex (.up ℤ))).obj
        (curriedTensor (CochainComplex C ℤ)) ≅
      (((Functor.whiskeringLeft₂ _).obj (F.mapHomologicalComplex (.up ℤ))).obj
        (F.mapHomologicalComplex (.up ℤ))).obj (curriedTensor (CochainComplex D ℤ)))
    (hτ : ∀ (P Q : CochainComplex C ℤ) (p q n : ℤ) (h : p + q = n),
      F.map (HomologicalComplex.ιTensorObj P Q p q n h) ≫
          ((τ.hom.app P).app Q).f n =
        (M.μIso (P.X p) (Q.X q)).inv ≫ HomologicalComplex.ιTensorObj
          ((F.mapHomologicalComplex (.up ℤ)).obj P)
          ((F.mapHomologicalComplex (.up ℤ)).obj Q) p q n h)
    (t : (Functor.postcompose₂.obj F.mapDerivedCategory).obj
        (curriedTensor (DerivedCategory C)) ⟶
      (((Functor.whiskeringLeft₂ _).obj F.mapDerivedCategory).obj
        F.mapDerivedCategory).obj (curriedTensor (DerivedCategory D)))
    (hnormalized : ∀ (P Q : CochainComplex C ℤ),
      P.IsKFlatForTotalTensor → Q.IsKFlatForTotalTensor →
      F.mapDerivedCategory.map (Functor.LaxMonoidal.μ DerivedCategory.Q P Q) ≫
          F.mapDerivedCategoryFactors.hom.app (P ⊗ Q) ≫
          DerivedCategory.Q.map ((τ.hom.app P).app Q) =
        (t.app (DerivedCategory.Q.obj P)).app (DerivedCategory.Q.obj Q) ≫
          (F.mapDerivedCategoryFactors.hom.app P ⊗ₘ
            F.mapDerivedCategoryFactors.hom.app Q) ≫
          Functor.LaxMonoidal.μ DerivedCategory.Q
            ((F.mapHomologicalComplex (.up ℤ)).obj P)
            ((F.mapHomologicalComplex (.up ℤ)).obj Q))
    (hbraided : ∀ A B : C,
      F.map (β_ A B).hom ≫ (M.μIso B A).inv =
        (M.μIso A B).inv ≫ (β_ (F.obj A) (F.obj B)).hom)
    (K L : DerivedCategory C) :
    F.mapDerivedCategory.map
        (DerivedMonoidal.braiding' DerivedCategory.Qh
          (HomotopyCategory.quasiIso C (.up ℤ)) K L).hom ≫ (t.app L).app K =
      (t.app K).app L ≫
        (DerivedMonoidal.braiding' DerivedCategory.Qh
          (HomotopyCategory.quasiIso D (.up ℤ))
          (F.mapDerivedCategory.obj K) (F.mapDerivedCategory.obj L)).hom := by
  sorry

end CategoryTheory.Functor
