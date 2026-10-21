/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q09
-/
module

public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
public import Mathlib.CategoryTheory.Adjunction.Whiskering
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
import Sheaf.CategoryTheory.KInjectiveTotalDerived
import Sheaf.SixFunctors.ResolvingDerivedAdjunction
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import WeilConjectures.Algebra.Homology.TowerEvaluationKInjective

/-!
# Normalized evaluation of a total derived tower functor

Source: Stacks Project, Sites Cohomology, Tag 0A07, lemma-Rf-commutes-with-Rlim,
diagram-topos proof, expanded using Derived Categories, Tags 070I, 070Y and 09T5
(blueprint: lem-weil-pbc-tower-derived-evaluation-normalization).

Natural number `n` denotes the positive tower level `n + 1`.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe uA vA uB vB wA wB wTA wTB

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- Package Mathlib's pointwise limit-preservation instances for a termwise exact functor.
Source: Stacks Project, Tag 0A07, diagram-topos proof; Mathlib functor-category limits
(blueprint: lem-weil-pbc-tower-derived-evaluation-normalization). -/
instance towerNormalization_preservesFiniteLimits
    {A : Type uA} {B : Type uB} [Category.{vA} A] [Category.{vB} B]
    [HasFiniteLimits B] (F : B ⥤ A) [PreservesFiniteLimits F] :
    PreservesFiniteLimits ((Functor.whiskeringRight ℕᵒᵖ B A).obj F) where
  preservesFiniteLimits _ _ _ := inferInstance

/-- Package Mathlib's pointwise colimit-preservation instances for a termwise exact functor.
Source: Stacks Project, Tag 0A07, diagram-topos proof; Mathlib functor-category colimits
(blueprint: lem-weil-pbc-tower-derived-evaluation-normalization). -/
instance towerNormalization_preservesFiniteColimits
    {A : Type uA} {B : Type uB} [Category.{vA} A] [Category.{vB} B]
    [HasFiniteColimits B] (F : B ⥤ A) [PreservesFiniteColimits F] :
    PreservesFiniteColimits ((Functor.whiskeringRight ℕᵒᵖ B A).obj F) where
  preservesFiniteColimits _ _ _ := inferInstance

/-- The canonical transition between derived evaluations, obtained by localizing the
ordinary transition of exact evaluation functors. This includes every transition,
including the identity. Source: Stacks Project, Tag 0A07, diagram-topos proof;
Derived Categories, Tag 05RU
(blueprint: lem-weil-pbc-tower-derived-evaluation-normalization). -/
def towerDerivedEvaluationTransition
    (A : Type uA) [Category.{vA} A] [Abelian A]
    [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wTA} (ℕᵒᵖ ⥤ A)]
    {m n : ℕᵒᵖ} (t : m ⟶ n) :
    ((evaluation ℕᵒᵖ A).obj m).mapDerivedCategory ⟶
      ((evaluation ℕᵒᵖ A).obj n).mapDerivedCategory :=
  Localization.liftNatTrans DerivedCategory.Q
    (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ A) (.up ℤ)) _ _
    ((evaluation ℕᵒᵖ A).obj m).mapDerivedCategory
    ((evaluation ℕᵒᵖ A).obj n).mapDerivedCategory
    (Functor.whiskerRight
      (NatTrans.mapHomologicalComplex ((evaluation ℕᵒᵖ A).map t) (.up ℤ))
      DerivedCategory.Q)

/-- The canonical exact-localization identification of evaluation after termwise `F`
with `F` after evaluation. It is the composite of the canonical composition comparisons;
its ordinary comparison is the strict evaluation identity. Source: Stacks Project,
Tag 0A07, diagram-topos proof, and Derived Categories, Tag 015F
(blueprint: lem-weil-pbc-tower-derived-evaluation-normalization). -/
def towerDerivedEvaluationInterchange
    {A : Type uA} {B : Type uB} [Category.{vA} A] [Category.{vB} B]
    [Abelian A] [Abelian B]
    [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wB} B]
    [HasDerivedCategory.{wTA} (ℕᵒᵖ ⥤ A)] [HasDerivedCategory.{wTB} (ℕᵒᵖ ⥤ B)]
    (F : B ⥤ A) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (n : ℕᵒᵖ) :
    ((Functor.whiskeringRight ℕᵒᵖ B A).obj F).mapDerivedCategory ⋙
        ((evaluation ℕᵒᵖ A).obj n).mapDerivedCategory ≅
      ((evaluation ℕᵒᵖ B).obj n).mapDerivedCategory ⋙ F.mapDerivedCategory :=
  (Functor.mapDerivedCategoryCompIso
    ((Functor.whiskeringRight ℕᵒᵖ B A).obj F) ((evaluation ℕᵒᵖ A).obj n)).symm ≪≫
    Functor.mapDerivedCategoryCompIso ((evaluation ℕᵒᵖ B).obj n) F

/-- Evaluation of a total right derived tower functor has a unique comparison normalized
by the universal derived units on K-injective towers. The family respects all transitions
and the counits of the canonical derived adjunctions. The two Hom formulas specify those
adjunctions, rather than merely choosing adjunctions with the same underlying functors.
Source: Stacks Project, Tag 0A07, lemma-Rf-commutes-with-Rlim, diagram-topos proof,
expanded by Derived Categories, Tags 070I, 070Y and 09T5
(blueprint: lem-weil-pbc-tower-derived-evaluation-normalization).

Proof plan:
1. Apply the ordinary adjunction levelwise to obtain the tower adjunction, with
   levelwise unit and counit. Exactness gives the localized left functors and evaluations
   (`lem-weil-tower-category-levelwise-abelian`,
   `lem-weil-pbc-exact-functor-derived-factorization`,
   `lem-weil-pbc-termwise-adjunction-homotopy`).
2. A K-injective tower J has K-injective evaluations. The two derived units on J and
   its evaluations are invertible. Define the comparison on QJ as b(J) a(J)⁻¹
   (`lem-weil-pbc-kinjective-functorial-existence`,
   `lem-weil-tower-evaluation-kinjective`, `lem-weil-pbc-kinjective-total-derived`).
3. Naturality of both units proves naturality of this formula on K-injective homotopy
   classes (`lem-weil-pbc-kinjective-total-derived`,
   `lem-weil-pbc-termwise-adjunction-homotopy`).
4. Represent every derived object M by an isomorphism M ≅ QJ. Conjugate the comparison
   by this isomorphism. Full faithfulness of localization on K-injectives proves
   independence, naturality and uniqueness (`lem-weil-pbc-kinjective-hom-derived`,
   `lem-weil-pbc-kinjective-functorial-existence`).
5. Naturality of the units with respect to each tower transition gives compatibility
   on QJ after cancelling a(J); transport along M ≅ QJ gives it on every object.
6. Apply `lem-sfb-resolving-derived-adjunction-normalization` with the left resolving
   class of all objects to both adjunctions. Its Hom formula, applied to the ordinary
   counit, gives εD F(η) = Q(εordinary), including the tower version.
7. Evaluate the tower equation at J. The ordinary counit is levelwise the ambient one.
   Unit normalization makes the proposed two counits equal after composition with
   the invertible F(a(J)); cancellation proves equality on QJ.
8. Both sides are natural in M. Transport along M ≅ QJ and cancel its evaluation to
   prove the counit equation for every derived tower object. -/
theorem exists_unique_towerDerivedEvaluation_normalized
    {A : Type uA} {B : Type uB} [Category.{vA} A] [Category.{vB} B]
    [Abelian A] [Abelian B]
    [IsGrothendieckAbelian.{vA} A] [IsGrothendieckAbelian.{vB} B]
    [IsGrothendieckAbelian.{vA} (ℕᵒᵖ ⥤ A)]
    [IsGrothendieckAbelian.{vB} (ℕᵒᵖ ⥤ B)]
    [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wB} B]
    [HasDerivedCategory.{wTA} (ℕᵒᵖ ⥤ A)] [HasDerivedCategory.{wTB} (ℕᵒᵖ ⥤ B)]
    (F : B ⥤ A) (G : A ⥤ B) [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] (adj : F ⊣ G)
    (RG : DerivedCategory A ⥤ DerivedCategory B)
    (RT : DerivedCategory (ℕᵒᵖ ⥤ A) ⥤ DerivedCategory (ℕᵒᵖ ⥤ B))
    (η : G.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ RG)
    (ηT : ((Functor.whiskeringRight ℕᵒᵖ A B).obj G).mapHomologicalComplex (.up ℤ) ⋙
      DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ RT)
    [RG.IsRightDerivedFunctor η (HomologicalComplex.quasiIso A (.up ℤ))]
    [RT.IsRightDerivedFunctor ηT (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ A) (.up ℤ))] :
    ∃ (d : F.mapDerivedCategory ⊣ RG)
      (dT : ((Functor.whiskeringRight ℕᵒᵖ B A).obj F).mapDerivedCategory ⊣ RT),
      (∀ (M : CochainComplex B ℤ) (I : CochainComplex A ℤ)
        (f : (F.mapHomologicalComplex (.up ℤ)).obj M ⟶ I),
        d.homEquiv (DerivedCategory.Q.obj M) (DerivedCategory.Q.obj I)
            (F.mapDerivedCategoryFactors.hom.app M ≫ DerivedCategory.Q.map f) =
          DerivedCategory.Q.map ((adj.mapHomologicalComplex (.up ℤ)).homEquiv M I f) ≫
            η.app I) ∧
      (∀ (M : CochainComplex (ℕᵒᵖ ⥤ B) ℤ) (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ)
        (f : (((Functor.whiskeringRight ℕᵒᵖ B A).obj F).mapHomologicalComplex
          (.up ℤ)).obj M ⟶ I),
        dT.homEquiv (DerivedCategory.Q.obj M) (DerivedCategory.Q.obj I)
            (((Functor.whiskeringRight ℕᵒᵖ B A).obj F).mapDerivedCategoryFactors.hom.app M ≫
              DerivedCategory.Q.map f) =
          DerivedCategory.Q.map
              (((adj.whiskerRight ℕᵒᵖ).mapHomologicalComplex (.up ℤ)).homEquiv M I f) ≫
            ηT.app I) ∧
      ∃ β : ∀ n : ℕᵒᵖ, RT ⋙ ((evaluation ℕᵒᵖ B).obj n).mapDerivedCategory ≅
          ((evaluation ℕᵒᵖ A).obj n).mapDerivedCategory ⋙ RG,
        (∀ (n : ℕᵒᵖ) (J : CochainComplex (ℕᵒᵖ ⥤ A) ℤ), J.IsKInjective →
          ((evaluation ℕᵒᵖ B).obj n).mapDerivedCategoryFactors.inv.app
                ((((Functor.whiskeringRight ℕᵒᵖ A B).obj G).mapHomologicalComplex
                  (.up ℤ)).obj J) ≫
              ((evaluation ℕᵒᵖ B).obj n).mapDerivedCategory.map (ηT.app J) ≫
              (β n).hom.app (DerivedCategory.Q.obj J) ≫
              RG.map (((evaluation ℕᵒᵖ A).obj n).mapDerivedCategoryFactors.hom.app J) =
            η.app ((((evaluation ℕᵒᵖ A).obj n).mapHomologicalComplex (.up ℤ)).obj J)) ∧
        (∀ (n : ℕᵒᵖ)
          (γ : RT ⋙ ((evaluation ℕᵒᵖ B).obj n).mapDerivedCategory ≅
            ((evaluation ℕᵒᵖ A).obj n).mapDerivedCategory ⋙ RG),
          (∀ J : CochainComplex (ℕᵒᵖ ⥤ A) ℤ, J.IsKInjective →
            ((evaluation ℕᵒᵖ B).obj n).mapDerivedCategoryFactors.inv.app
                  ((((Functor.whiskeringRight ℕᵒᵖ A B).obj G).mapHomologicalComplex
                    (.up ℤ)).obj J) ≫
                ((evaluation ℕᵒᵖ B).obj n).mapDerivedCategory.map (ηT.app J) ≫
                γ.hom.app (DerivedCategory.Q.obj J) ≫
                RG.map (((evaluation ℕᵒᵖ A).obj n).mapDerivedCategoryFactors.hom.app J) =
              η.app ((((evaluation ℕᵒᵖ A).obj n).mapHomologicalComplex (.up ℤ)).obj J)) →
            γ = β n) ∧
        (∀ (m n : ℕᵒᵖ) (t : m ⟶ n) (M : DerivedCategory (ℕᵒᵖ ⥤ A)),
          (towerDerivedEvaluationTransition B t).app (RT.obj M) ≫ (β n).hom.app M =
            (β m).hom.app M ≫ RG.map ((towerDerivedEvaluationTransition A t).app M)) ∧
        (∀ (n : ℕᵒᵖ) (M : DerivedCategory (ℕᵒᵖ ⥤ A)),
          ((evaluation ℕᵒᵖ A).obj n).mapDerivedCategory.map (dT.counit.app M) =
            (towerDerivedEvaluationInterchange F n).hom.app (RT.obj M) ≫
              F.mapDerivedCategory.map ((β n).hom.app M) ≫
              d.counit.app (((evaluation ℕᵒᵖ A).obj n).mapDerivedCategory.obj M)) := by
  sorry

end CategoryTheory
