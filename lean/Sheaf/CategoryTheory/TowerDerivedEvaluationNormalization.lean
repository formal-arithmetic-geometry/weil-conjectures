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
import Mathlib.CategoryTheory.Functor.Derived.Adjunction
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
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

universe uA vA uB vB wA wB wTA wTB uC vC wC

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

private theorem derivedComposition_fac
    {A : Type uA} {B : Type uB} {C : Type uC}
    [Category.{vA} A] [Category.{vB} B] [Category.{vC} C]
    [Abelian A] [Abelian B] [Abelian C]
    [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wB} B] [HasDerivedCategory.{wC} C]
    (F : A ⥤ B) (G : B ⥤ C) [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (K : CochainComplex A ℤ) :
    (Functor.mapDerivedCategoryCompIso F G).hom.app (DerivedCategory.Q.obj K) ≫
        G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app K) ≫
        G.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj K) =
      (F ⋙ G).mapDerivedCategoryFactors.hom.app K := by
  have h := Functor.mapDerivedCategoryCompIso_fac F G K
  have hid : (Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ G)) (.up ℤ)).hom.app K =
      𝟙 _ := rfl
  erw [hid, DerivedCategory.Q.map_id, Category.comp_id] at h
  exact h

private theorem towerInterchange_fac
    {A : Type uA} {B : Type uB} [Category.{vA} A] [Category.{vB} B]
    [Abelian A] [Abelian B]
    [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wB} B]
    [HasDerivedCategory.{wTA} (ℕᵒᵖ ⥤ A)] [HasDerivedCategory.{wTB} (ℕᵒᵖ ⥤ B)]
    (F : B ⥤ A) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (n : ℕᵒᵖ) (K : CochainComplex (ℕᵒᵖ ⥤ B) ℤ) :
    (towerDerivedEvaluationInterchange F n).hom.app (DerivedCategory.Q.obj K) ≫
        F.mapDerivedCategory.map
          (((evaluation ℕᵒᵖ B).obj n).mapDerivedCategoryFactors.hom.app K) ≫
        F.mapDerivedCategoryFactors.hom.app
          ((((evaluation ℕᵒᵖ B).obj n).mapHomologicalComplex (.up ℤ)).obj K) =
      ((evaluation ℕᵒᵖ A).obj n).mapDerivedCategory.map
          (((Functor.whiskeringRight ℕᵒᵖ B A).obj F).mapDerivedCategoryFactors.hom.app K) ≫
        ((evaluation ℕᵒᵖ A).obj n).mapDerivedCategoryFactors.hom.app
          ((((Functor.whiskeringRight ℕᵒᵖ B A).obj F).mapHomologicalComplex (.up ℤ)).obj K) := by
  let FT := (Functor.whiskeringRight ℕᵒᵖ B A).obj F
  let EA := (evaluation ℕᵒᵖ A).obj n
  let EB := (evaluation ℕᵒᵖ B).obj n
  apply (cancel_epi
    ((Functor.mapDerivedCategoryCompIso FT EA).hom.app (DerivedCategory.Q.obj K))).mp
  dsimp only [FT, EA, EB]
  simp only [towerDerivedEvaluationInterchange, Iso.trans_hom, NatTrans.comp_app,
    Iso.symm_hom, Category.assoc, Iso.hom_inv_id_app_assoc]
  exact (derivedComposition_fac EB F K).trans (derivedComposition_fac FT EA K).symm

private theorem towerTransition_fac
    (A : Type uA) [Category.{vA} A] [Abelian A]
    [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wTA} (ℕᵒᵖ ⥤ A)]
    {m n : ℕᵒᵖ} (t : m ⟶ n) (J : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
    (towerDerivedEvaluationTransition A t).app (DerivedCategory.Q.obj J) ≫
        ((evaluation ℕᵒᵖ A).obj n).mapDerivedCategoryFactors.hom.app J =
      ((evaluation ℕᵒᵖ A).obj m).mapDerivedCategoryFactors.hom.app J ≫
        DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex ((evaluation ℕᵒᵖ A).map t) (.up ℤ)).app J) := by
  have hm : Localization.Lifting.iso DerivedCategory.Q
      (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ A) (.up ℤ))
      (((evaluation ℕᵒᵖ A).obj m).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
      ((evaluation ℕᵒᵖ A).obj m).mapDerivedCategory =
        ((evaluation ℕᵒᵖ A).obj m).mapDerivedCategoryFactors := rfl
  have hn : Localization.Lifting.iso DerivedCategory.Q
      (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ A) (.up ℤ))
      (((evaluation ℕᵒᵖ A).obj n).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
      ((evaluation ℕᵒᵖ A).obj n).mapDerivedCategory =
        ((evaluation ℕᵒᵖ A).obj n).mapDerivedCategoryFactors := rfl
  simp [towerDerivedEvaluationTransition, Localization.liftNatTrans_app, hm, hn]

private theorem towerTransition_inv_fac
    (A : Type uA) [Category.{vA} A] [Abelian A]
    [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wTA} (ℕᵒᵖ ⥤ A)]
    {m n : ℕᵒᵖ} (t : m ⟶ n) (J : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
    ((evaluation ℕᵒᵖ A).obj m).mapDerivedCategoryFactors.inv.app J ≫
        (towerDerivedEvaluationTransition A t).app (DerivedCategory.Q.obj J) =
      DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex ((evaluation ℕᵒᵖ A).map t) (.up ℤ)).app J) ≫
        ((evaluation ℕᵒᵖ A).obj n).mapDerivedCategoryFactors.inv.app J := by
  apply (cancel_mono
    (((evaluation ℕᵒᵖ A).obj n).mapDerivedCategoryFactors.hom.app J)).mp
  simp only [Category.assoc, towerTransition_fac, Iso.inv_hom_id_app_assoc,
    Iso.inv_hom_id_app]
  exact (Category.comp_id _).symm

private theorem exactDerivedAdjunction
    {A : Type uA} {B : Type uB} [Category.{vA} A] [Category.{vB} B]
    [Abelian A] [Abelian B]
    [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wB} B]
    [Abelian.HasKInjectiveResolutions A]
    (F : B ⥤ A) (G : A ⥤ B) [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] (adj : F ⊣ G)
    (RG : DerivedCategory A ⥤ DerivedCategory B)
    (η : G.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ RG)
    [RG.IsRightDerivedFunctor η (HomologicalComplex.quasiIso A (.up ℤ))] :
    ∃ d : F.mapDerivedCategory ⊣ RG,
      ∀ (M : CochainComplex B ℤ) (I : CochainComplex A ℤ)
        (f : (F.mapHomologicalComplex (.up ℤ)).obj M ⟶ I),
        d.homEquiv (DerivedCategory.Q.obj M) (DerivedCategory.Q.obj I)
            (F.mapDerivedCategoryFactors.hom.app M ≫ DerivedCategory.Q.map f) =
          DerivedCategory.Q.map ((adj.mapHomologicalComplex (.up ℤ)).homEquiv M I f) ≫
            η.app I := by
  let W := HomologicalComplex.quasiIso B (.up ℤ)
  let V := HomologicalComplex.quasiIso A (.up ℤ)
  let α := F.mapDerivedCategoryFactors.hom
  have : F.mapDerivedCategory.IsLeftDerivedFunctor α W :=
    Functor.isLeftDerivedFunctor_of_inverts W _ F.mapDerivedCategoryFactors
  have : (F.mapDerivedCategory ⋙ RG).IsLeftDerivedFunctor
      ((Functor.associator _ _ _).inv ≫ Functor.whiskerRight α RG) W :=
    Functor.isLeftDerivedFunctor_of_inverts W _
      ((Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight F.mapDerivedCategoryFactors RG)
  have : (RG ⋙ F.mapDerivedCategory).IsRightDerivedFunctor
      (Functor.whiskerRight η F.mapDerivedCategory ≫
        (Functor.associator _ _ _).hom) V := by
    have hd : (CochainComplex.KInjectives.localizerMorphism A).Derives
        (G.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⋙ F.mapDerivedCategory) := by
      intro I I' f hf
      have : IsIso (DerivedCategory.Q.map
          ((G.mapHomologicalComplex (.up ℤ)).map f.hom)) := (derives G) f hf
      exact F.mapDerivedCategory.map_isIso
        (DerivedCategory.Q.map ((G.mapHomologicalComplex (.up ℤ)).map f.hom))
    apply hd.isRightDerivedFunctor_of_isIso
    intro I
    have : IsIso (η.app I.obj) := (derives G).isIso_of_isRightDerivedFunctor η I
    change IsIso (F.mapDerivedCategory.map (η.app I.obj) ≫ 𝟙 _)
    infer_instance
  let ac := adj.mapHomologicalComplex (.up ℤ)
  let d := ac.derived W V α η
  refine ⟨d, ?_⟩
  intro M I f
  change d.unit.app _ ≫ RG.map (α.app M ≫ DerivedCategory.Q.map f) = _
  rw [RG.map_comp, ← Category.assoc]
  have hunit := ac.derivedη_fac_app W α η M
  change d.unit.app _ ≫ RG.map (α.app M) = _ at hunit
  have hn := η.naturality f
  dsimp only [Functor.comp_map] at hn
  rw [hunit, Category.assoc, ← hn, ← DerivedCategory.Q.map_comp_assoc]
  rfl

private theorem counitOfHomFormula
    {A : Type uA} {B : Type uB} [Category.{vA} A] [Category.{vB} B]
    [Abelian A] [Abelian B]
    [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wB} B]
    (F : B ⥤ A) (G : A ⥤ B) [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] (adj : F ⊣ G)
    (RG : DerivedCategory A ⥤ DerivedCategory B)
    (η : G.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ RG)
    (d : F.mapDerivedCategory ⊣ RG)
    (hd : ∀ (M : CochainComplex B ℤ) (I : CochainComplex A ℤ)
      (f : (F.mapHomologicalComplex (.up ℤ)).obj M ⟶ I),
      d.homEquiv (DerivedCategory.Q.obj M) (DerivedCategory.Q.obj I)
          (F.mapDerivedCategoryFactors.hom.app M ≫ DerivedCategory.Q.map f) =
        DerivedCategory.Q.map ((adj.mapHomologicalComplex (.up ℤ)).homEquiv M I f) ≫
          η.app I)
    (I : CochainComplex A ℤ) :
    F.mapDerivedCategory.map (η.app I) ≫ d.counit.app (DerivedCategory.Q.obj I) =
      F.mapDerivedCategoryFactors.hom.app
          ((G.mapHomologicalComplex (.up ℤ)).obj I) ≫
        DerivedCategory.Q.map ((adj.mapHomologicalComplex (.up ℤ)).counit.app I) := by
  let ac := adj.mapHomologicalComplex (.up ℤ)
  apply (d.homEquiv _ _).injective
  erw [← d.homEquiv_counit, Equiv.apply_symm_apply, hd,
    ← ac.homEquiv_symm_id, Equiv.apply_symm_apply, DerivedCategory.Q.map_id,
    Category.id_comp]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
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
  classical
  let FT := (Functor.whiskeringRight ℕᵒᵖ B A).obj F
  let GT := (Functor.whiskeringRight ℕᵒᵖ A B).obj G
  let Gc := G.mapHomologicalComplex (.up ℤ)
  let GTc := GT.mapHomologicalComplex (.up ℤ)
  let EA (n : ℕᵒᵖ) := (evaluation ℕᵒᵖ A).obj n
  let EB (n : ℕᵒᵖ) := (evaluation ℕᵒᵖ B).obj n
  let κ := CochainComplex.KInjectives.ι (C := ℕᵒᵖ ⥤ A)
  let L := κ ⋙ DerivedCategory.Q
  let V := CochainComplex.KInjectives.quasiIso (ℕᵒᵖ ⥤ A)
  obtain ⟨d, hd⟩ := exactDerivedAdjunction F G adj RG η
  obtain ⟨dT, hdT⟩ := exactDerivedAdjunction FT GT (adj.whiskerRight ℕᵒᵖ) RT ηT
  refine ⟨d, dT, hd, hdT, ?_⟩
  let a (n : ℕᵒᵖ) :
      κ ⋙ GTc ⋙ (EB n).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
        L ⋙ RT ⋙ (EB n).mapDerivedCategory :=
    Functor.whiskerLeft κ
      (Functor.whiskerLeft GTc (EB n).mapDerivedCategoryFactors.inv ≫
        Functor.whiskerRight ηT (EB n).mapDerivedCategory)
  let b (n : ℕᵒᵖ) :
      κ ⋙ GTc ⋙ (EB n).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
        L ⋙ (EA n).mapDerivedCategory ⋙ RG :=
    Functor.whiskerLeft κ
      (Functor.whiskerLeft ((EA n).mapHomologicalComplex (.up ℤ)) η ≫
        Functor.whiskerRight (EA n).mapDerivedCategoryFactors.inv RG)
  have ha (n : ℕᵒᵖ) : IsIso (a n) := by
    have : ∀ J, IsIso ((a n).app J) := by
      intro J
      have : IsIso (ηT.app J.obj) :=
        (derives GT).isIso_of_isRightDerivedFunctor ηT J
      change IsIso ((EB n).mapDerivedCategoryFactors.inv.app (GTc.obj J.obj) ≫
        (EB n).mapDerivedCategory.map (ηT.app J.obj))
      infer_instance
    exact NatIso.isIso_of_isIso_app _
  have hb (n : ℕᵒᵖ) : IsIso (b n) := by
    have : ∀ J, IsIso ((b n).app J) := by
      intro J
      have hJ : J.obj.IsKInjective := J.property
      have hE : CochainComplex.IsKInjective
          (((EA n).mapHomologicalComplex (.up ℤ)).obj J.obj) :=
        tower_evaluation_isKInjective A J.obj n
      have : IsIso (η.app (((EA n).mapHomologicalComplex (.up ℤ)).obj J.obj)) :=
        (derives G).isIso_of_isRightDerivedFunctor η
          ⟨_, hE⟩
      change IsIso (η.app (((EA n).mapHomologicalComplex (.up ℤ)).obj J.obj) ≫
        RG.map ((EA n).mapDerivedCategoryFactors.inv.app J.obj))
      infer_instance
    exact NatIso.isIso_of_isIso_app _
  let β (n : ℕᵒᵖ) : RT ⋙ (EB n).mapDerivedCategory ≅ (EA n).mapDerivedCategory ⋙ RG :=
    Localization.liftNatIso L V _ _ _ _ ((asIso (a n)).symm ≪≫ asIso (b n))
  have hβ (n : ℕᵒᵖ) (J : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (hJ : J.IsKInjective) :
      (a n).app (CochainComplex.KInjectives.mk J) ≫
        (β n).hom.app (DerivedCategory.Q.obj J) =
          (b n).app (CochainComplex.KInjectives.mk J) := by
    change (a n).app (CochainComplex.KInjectives.mk J) ≫
      (Localization.liftNatIso L V _ _ (RT ⋙ (EB n).mapDerivedCategory)
        ((EA n).mapDerivedCategory ⋙ RG)
        ((asIso (a n)).symm ≪≫ asIso (b n))).hom.app
          (L.obj (CochainComplex.KInjectives.mk J)) = _
    simp [Localization.liftNatIso_hom, Localization.liftNatTrans_app,
      Localization.Lifting.iso]
  have hβ' (n : ℕᵒᵖ) (J : CochainComplex.KInjectives (ℕᵒᵖ ⥤ A)) :
      (a n).app J ≫ (β n).hom.app (L.obj J) = (b n).app J :=
    hβ n J.obj J.property
  refine ⟨β, ?_, ?_, ?_, ?_⟩
  · intro n J hJ
    have h := hβ n J hJ
    dsimp [a, b] at h
    have h' := congrArg
      (fun f ↦ f ≫ RG.map ((EA n).mapDerivedCategoryFactors.hom.app J)) h
    dsimp only [κ, CochainComplex.KInjectives.ι, ObjectProperty.ι_obj,
      CochainComplex.KInjectives.mk, GTc, GT, EA, EB] at h'
    simp only [Category.assoc] at h'
    erw [← RG.map_comp, Iso.inv_hom_id_app, RG.map_id,
      Category.comp_id] at h'
    simpa only [Category.assoc] using h'
  · intro n γ hγ
    apply Iso.ext
    apply Localization.natTrans_ext L V
    intro J
    apply (cancel_epi ((a n).app J)).mp
    have h := hγ J.obj J.property
    have h' := congrArg
      (fun f ↦ f ≫ RG.map ((EA n).mapDerivedCategoryFactors.inv.app J.obj)) h
    have hg : (a n).app J ≫ γ.hom.app (L.obj J) = (b n).app J := by
      dsimp only [EA, EB, GTc, GT] at h'
      erw [Category.assoc, Category.assoc, Category.assoc, ← RG.map_comp,
        Iso.hom_inv_id_app, RG.map_id, Category.comp_id] at h'
      simpa only [a, b, Functor.whiskerLeft_app, NatTrans.comp_app,
        Functor.whiskerRight_app, Category.assoc, EA, EB, GTc, GT, L, κ,
        CochainComplex.KInjectives.ι, ObjectProperty.ι_obj, Functor.comp_obj] using h'
    exact hg.trans (hβ n J.obj J.property).symm
  · intro m n t M
    let sA := towerDerivedEvaluationTransition A t
    let sB := towerDerivedEvaluationTransition B t
    have heq : Functor.whiskerLeft RT sB ≫ (β n).hom =
        (β m).hom ≫ Functor.whiskerRight sA RG := by
      apply Localization.natTrans_ext L V
      intro J
      let u := DerivedCategory.Q.map (Gc.map
        ((NatTrans.mapHomologicalComplex ((evaluation ℕᵒᵖ A).map t) (.up ℤ)).app J.obj))
      have hna : (a m).app J ≫ sB.app (RT.obj (L.obj J)) = u ≫ (a n).app J := by
        change ((EB m).mapDerivedCategoryFactors.inv.app (GTc.obj J.obj) ≫
          (EB m).mapDerivedCategory.map (ηT.app J.obj)) ≫ sB.app _ = _
        rw [Category.assoc, sB.naturality, ← Category.assoc]
        rw [towerTransition_inv_fac, Category.assoc]
        rfl
      have hnb : (b m).app J ≫ RG.map (sA.app (L.obj J)) = u ≫ (b n).app J := by
        change (η.app (((EA m).mapHomologicalComplex (.up ℤ)).obj J.obj) ≫
          RG.map ((EA m).mapDerivedCategoryFactors.inv.app J.obj)) ≫ RG.map _ = _
        erw [Category.assoc, ← RG.map_comp, towerTransition_inv_fac, RG.map_comp]
        erw [← Category.assoc, ← η.naturality, Category.assoc]
        rfl
      change sB.app _ ≫ (β n).hom.app _ = (β m).hom.app _ ≫ RG.map (sA.app _)
      apply (cancel_epi ((a m).app J)).mp
      rw [← Category.assoc, hna, Category.assoc, hβ' n J]
      rw [← Category.assoc, hβ' m J]
      exact hnb.symm
    exact NatTrans.congr_app heq M
  · intro n M
    let c := towerDerivedEvaluationInterchange F n
    have heq : Functor.whiskerRight dT.counit (EA n).mapDerivedCategory =
        Functor.whiskerLeft RT c.hom ≫ Functor.whiskerRight (β n).hom F.mapDerivedCategory ≫
          Functor.whiskerLeft (EA n).mapDerivedCategory d.counit := by
      apply Localization.natTrans_ext L V
      intro J
      let I := ((EA n).mapHomologicalComplex (.up ℤ)).obj J.obj
      let εT := ((adj.whiskerRight ℕᵒᵖ).mapHomologicalComplex (.up ℤ)).counit.app J.obj
      let ε := (adj.mapHomologicalComplex (.up ℤ)).counit.app I
      have hε : ((EA n).mapHomologicalComplex (.up ℤ)).map εT = ε := by
        ext p
        simp [εT, ε, I, EA, Adjunction.mapHomologicalComplex_counit_app_f]
      have hcT := counitOfHomFormula FT GT (adj.whiskerRight ℕᵒᵖ) RT ηT dT hdT J.obj
      have hc := counitOfHomFormula F G adj RG η d hd I
      have hn : (EB n).mapDerivedCategory.map (ηT.app J.obj) ≫
          (β n).hom.app (L.obj J) =
          (EB n).mapDerivedCategoryFactors.hom.app (GTc.obj J.obj) ≫
            η.app I ≫ RG.map ((EA n).mapDerivedCategoryFactors.inv.app J.obj) := by
        have h := congrArg
          (fun f ↦ (EB n).mapDerivedCategoryFactors.hom.app (GTc.obj J.obj) ≫ f)
          (hβ' n J)
        dsimp only [a, b, Functor.whiskerLeft_app, NatTrans.comp_app,
          Functor.whiskerRight_app] at h
        simp only [Category.assoc] at h
        erw [Iso.hom_inv_id_app_assoc] at h
        exact h
      have : IsIso (ηT.app J.obj) :=
        (derives GT).isIso_of_isRightDerivedFunctor ηT J
      change (EA n).mapDerivedCategory.map (dT.counit.app (L.obj J)) =
        c.hom.app (RT.obj (L.obj J)) ≫ F.mapDerivedCategory.map ((β n).hom.app _) ≫
          d.counit.app ((EA n).mapDerivedCategory.obj (L.obj J))
      apply (cancel_epi
        ((EA n).mapDerivedCategory.map (FT.mapDerivedCategory.map (ηT.app J.obj)))).mp
      erw [← (EA n).mapDerivedCategory.map_comp, hcT]
      erw [← Category.assoc, ← Category.assoc, c.hom.naturality]
      dsimp only [Functor.comp_map]
      erw [Category.assoc, Category.assoc, ← F.mapDerivedCategory.map_comp_assoc, hn]
      simp only [F.mapDerivedCategory.map_comp, Category.assoc]
      erw [d.counit.naturality]
      dsimp only [Functor.id_map, Functor.comp_map]
      erw [reassoc_of% hc]
      erw [reassoc_of% (towerInterchange_fac F n (GTc.obj J.obj))]
      have hfac := (EA n).mapDerivedCategoryFactors.hom.naturality εT
      dsimp only [Functor.comp_map, Functor.id_obj] at hfac
      have hf := congrArg
        (fun f ↦ f ≫ (EA n).mapDerivedCategoryFactors.inv.app J.obj) hfac
      simp only [Category.assoc, Iso.hom_inv_id_app, Category.comp_id] at hf
      have hq := congrArg
        (fun f ↦ (EA n).mapDerivedCategoryFactors.hom.app
            ((FT.mapHomologicalComplex (.up ℤ)).obj (GTc.obj J.obj)) ≫
          DerivedCategory.Q.map f ≫ (EA n).mapDerivedCategoryFactors.inv.app J.obj) hε
      exact ((EA n).mapDerivedCategory.map_comp _ _).trans
        (congrArg
          (fun f ↦ (EA n).mapDerivedCategory.map
            (FT.mapDerivedCategoryFactors.hom.app (GTc.obj J.obj)) ≫ f) (hf.trans hq))
    exact NatTrans.congr_app heq M

end CategoryTheory
