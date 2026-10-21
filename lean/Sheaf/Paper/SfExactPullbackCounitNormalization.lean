/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q17
-/
module

public import Sheaf.Paper.PbcQbarCompletedPullback
public import Sheaf.Paper.CompletedRlimFunctor
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import Sheaf.CategoryTheory.ExactFunctorDerivedFunctor
import Mathlib.CategoryTheory.Functor.KanExtension.Basic
public import Sheaf.Paper.DerivedTowerEvaluationNormalization
import Sheaf.CategoryTheory.DerivedCategory.ConstantTowerNormalization
import Sheaf.Algebra.Homology.DiagramKFlatReplacements
import Sheaf.Paper.StrictQuotientPullbackComputation
import Sheaf.CategoryTheory.DerivedTowerCounitProjections
import Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients

/-! # Counit normalization of exact completed-coefficient pullback

Source: blueprint localization, returned Step 6 and immersion-comparison Steps 1 and 5;
Stacks Tags 015F, 06XN, 0941 and 099N (2),(5)
(blueprint: lem-sf-exact-pullback-counit-normalization).

The ordinary and strict pullbacks, their counits, the quotient augmentation and the
ambient completed pullback are the published constructions. Level `n` means exponent `n+1`.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
namespace ExactPullbackNormalization

variable {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
  {X Y : Scheme.{u}} (g : Y ⟶ X) [IsIso (completedCoefficientMap g d)]

/-- Inverse image with its scalar action transported along the inverse coefficient map.
Source: localization Step 6, exact pullback identification; Stacks 099N
(blueprint: lem-sf-exact-pullback-counit-normalization). -/
abbrev moduleFunctor :=
  proEtaleModuleInverseImage g (pbcAdicCompletion X d) ⋙
    reductionRestrict Y (inv (completedCoefficientMap g d))

/-- The same functor applied levelwise to actual strict towers.
Source: localization Step 6, strict exact pullback; Stacks 02MZ
(blueprint: lem-sf-exact-pullback-counit-normalization). -/
abbrev towerFunctor :=
  (Functor.whiskeringRight ℕᵒᵖ _ _).obj (moduleFunctor d g)

variable [(moduleFunctor d g).Additive]
  [PreservesFiniteLimits (moduleFunctor d g)] [PreservesFiniteColimits (moduleFunctor d g)]

/-- Finite limits of the levelwise functor are supplied by Mathlib's shape-wise instance.
Source: Stacks 02MZ, levelwise kernels
(blueprint: lem-sf-exact-pullback-counit-normalization). -/
instance towerFiniteLimits : PreservesFiniteLimits (towerFunctor d g) where
  preservesFiniteLimits _ _ _ := inferInstance

/-- Finite colimits of the levelwise functor use Mathlib's shape-wise instance.
Source: Stacks 02MZ, levelwise cokernels
(blueprint: lem-sf-exact-pullback-counit-normalization). -/
instance towerFiniteColimits : PreservesFiniteColimits (towerFunctor d g) where
  preservesFiniteColimits _ _ _ := inferInstance

/-- Exact localization of the ordinary identity commuting pullback and constant towers.
Source: localization Step 6, constant-tower compatibility; Stacks 015F
(blueprint: lem-sf-exact-pullback-counit-normalization). -/
def constantIso :
    (moduleFunctor d g).mapDerivedCategory ⋙ completedDerivedConstant d Y ≅
      completedDerivedConstant d X ⋙ (towerFunctor d g).mapDerivedCategory :=
  (Functor.mapDerivedCategoryCompIso (moduleFunctor d g) (completedTowerConstant d Y)).symm ≪≫
    Functor.mapDerivedCategoryNatIso (Functor.compConstIso ℕᵒᵖ (moduleFunctor d g)) ≪≫
    Functor.mapDerivedCategoryCompIso (completedTowerConstant d X) (towerFunctor d g)

/-- Exact localization of the identity commuting levelwise pullback and evaluation.
Source: localization Step 6, evaluation compatibility; Stacks 015F
(blueprint: lem-sf-exact-pullback-counit-normalization). -/
def evaluationIso (n : ℕ) :
    (towerFunctor d g).mapDerivedCategory ⋙ pbcTowerEvaluation Y (pbcAdicCompletion Y d) n ≅
      pbcTowerEvaluation X (pbcAdicCompletion X d) n ⋙ (moduleFunctor d g).mapDerivedCategory :=
  (Functor.mapDerivedCategoryCompIso (towerFunctor d g)
    ((CategoryTheory.evaluation ℕᵒᵖ (pbcModules Y (pbcAdicCompletion Y d))).obj (op n))).symm ≪≫
    Functor.mapDerivedCategoryNatIso (Iso.refl _) ≪≫
    Functor.mapDerivedCategoryCompIso
      ((CategoryTheory.evaluation ℕᵒᵖ (pbcModules X (pbcAdicCompletion X d))).obj (op n))
      (moduleFunctor d g)

/-- The exact augmented construction, using the published quotient augmentation and unit.
Source: localization Step 6, augmented comparison; Stacks 099N (2),(5)
(blueprint: lem-sf-exact-pullback-counit-normalization). -/
def exactAugmentation (K : DerivedCategory (pbcModules X (pbcAdicCompletion X d))) :
    (moduleFunctor d g).mapDerivedCategory.obj K ⟶
      (completedTowerRlim d Y).obj ((towerFunctor d g).mapDerivedCategory.obj
        ((completedReductionTower X d).obj K)) :=
  (completedConstantRlimUnit d Y).app ((moduleFunctor d g).mapDerivedCategory.obj K) ≫
    (completedTowerRlim d Y).map ((constantIso d g).hom.app K ≫
      (towerFunctor d g).mapDerivedCategory.map ((completedReductionTowerUnit d X).app K))

/-- The prescribed tensor-generator normalization of the ordinary module isomorphism.
Source: localization Step 6, x tensor b maps to b x; Stacks 03EK
(blueprint: lem-sf-exact-pullback-counit-normalization). -/
def ModuleComparisonSpec (m : completedModulePullback g d ≅ moduleFunctor d g) : Prop :=
  ∀ (M : pbcModules X (pbcAdicCompletion X d)) (U : Y.ProEtᵒᵖ)
    (b : (pbcAdicCompletion Y d).obj.obj U)
    (x : ((proEtaleModuleInverseImage g (pbcAdicCompletion X d)).obj M).val.obj U),
    (m.hom.app M).val.app U
        (reductionTensorSection Y (completedCoefficientMap g d)
          ((proEtaleModuleInverseImage g (pbcAdicCompletion X d)).obj M) U b x) =
      ((inv (completedCoefficientMap g d)).hom.app U b) • x

/-- The equation fixing the ordinary derived comparison by the published universal counit.
Source: localization Step 6, first displayed normalization; Stacks 015F
(blueprint: lem-sf-exact-pullback-counit-normalization). -/
def OrdinaryNormalized (m : completedModulePullback g d ≅ moduleFunctor d g)
    (e : completedOrdinaryPullback g d ≅ (moduleFunctor d g).mapDerivedCategory) : Prop :=
  ∀ P : CochainComplex (pbcModules X (pbcAdicCompletion X d)) ℤ,
    e.hom.app (DerivedCategory.Q.obj P) ≫
        (moduleFunctor d g).mapDerivedCategoryFactors.hom.app P =
      completedOrdinaryPullbackComplexCounit g d P ≫
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex m (.up ℤ)).hom.app P)

/-- The same universal-counit equation inside the derived category of strict towers.
Source: localization Step 6, tower normalization; Stacks 015F and 02MZ
(blueprint: lem-sf-exact-pullback-counit-normalization). -/
def TowerNormalized (m : completedModulePullback g d ≅ moduleFunctor d g)
    (E : completedTowerPullback g d ≅ (towerFunctor d g).mapDerivedCategory) : Prop :=
  ∀ P : CochainComplex (pbcTowers X (pbcAdicCompletion X d)) ℤ,
    E.hom.app (DerivedCategory.Q.obj P) ≫
        (towerFunctor d g).mapDerivedCategoryFactors.hom.app P =
      completedTowerPullbackComplexCounit g d P ≫
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex
          ((Functor.whiskeringRight ℕᵒᵖ _ _).mapIso m) (.up ℤ)).hom.app P)

/-- Evaluation is normalized by both actual counits on objectwise K-flat representatives.
Source: localization Step 6, evaluation equation; Stacks 06XN
(blueprint: lem-sf-exact-pullback-counit-normalization). -/
def EvaluationNormalized (n : ℕ)
    (v : completedTowerPullback g d ⋙ pbcTowerEvaluation Y (pbcAdicCompletion Y d) n ≅
      pbcTowerEvaluation X (pbcAdicCompletion X d) n ⋙ completedOrdinaryPullback g d) : Prop :=
  letI : EssentiallySmall.{u + 1} X.ProEt := essentiallySmallSelf.{0, u, u + 1} _
  ∀ P : CochainComplex (pbcTowers X (pbcAdicCompletion X d)) ℤ,
    (∀ k : ℕ, @CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
      X.ProEt inferInstance (essentiallySmallSelf.{0, u, u + 1} X.ProEt)
      (ProEt.topology X) (pbcAdicCompletion X d) (P.asFunctor.obj (op k))) →
    (∀ (k : ℕ) (q : ℤ), SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1}
      (C := X.ProEt) (J := ProEt.topology X)
      (R := pbcAdicCompletion X d) ((P.X q).obj (op k))) →
    v.hom.app (DerivedCategory.Q.obj P) ≫
        (completedOrdinaryPullback g d).map
          (((CategoryTheory.evaluation ℕᵒᵖ (pbcModules X (pbcAdicCompletion X d))).obj
            (op n)).mapDerivedCategoryFactors.hom.app P) ≫
        completedOrdinaryPullbackComplexCounit g d (P.asFunctor.obj (op n)) =
      (pbcTowerEvaluation Y (pbcAdicCompletion Y d) n).map
          (completedTowerPullbackComplexCounit g d P) ≫
        ((CategoryTheory.evaluation ℕᵒᵖ (pbcModules Y (pbcAdicCompletion Y d))).obj
          (op n)).mapDerivedCategoryFactors.hom.app
            (((completedTowerModulePullback g d).mapHomologicalComplex (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map
          ((DerivedTowerPullback.evaluationComplexIso (completedModulePullback g d) n).hom.app P)

/-- Apply the actual total derived limit to the strict tower comparison at the quotient tower.
Source: localization Step 6, definition of d_K; Stacks 0941
(blueprint: lem-sf-exact-pullback-counit-normalization). -/
def completedIso
    (E : completedTowerPullback g d ≅ (towerFunctor d g).mapDerivedCategory)
    (K : DerivedCategory (pbcModules X (pbcAdicCompletion X d))) :
    completedPullbackObject g d K ≅
      (completedTowerRlim d Y).obj ((towerFunctor d g).mapDerivedCategory.obj
        ((completedReductionTower X d).obj K)) :=
  (completedTowerRlim d Y).mapIso (E.app ((completedReductionTower X d).obj K))

/-- The unique counit-normalized exact pullback comparison, with its strict-tower,
constant-tower, quotient-augmentation and derived-limit evaluation compatibilities.

Source: blueprint localization returned Step 6, immersion-comparison Steps 1 and 5;
native SfImmersionCompletedPullbackComparison derivedIso_exists and strictIso_exists;
Stacks Tags 015F, 06XN, 0941, 099N (2),(5)
(blueprint: lem-sf-exact-pullback-counit-normalization).

Proof:
1. By lem-weil-pbc-exact-functor-derived-functor, exact termwise descent with its
localization comparison is a universal left-derived pair. Compose the specified
pullback counit with Q(m). Right Kan extension uniqueness
(lem-sfb-right-kan-extension-unique-iso) gives e and its unique normalization.
2. Kernels and cokernels of strict towers are levelwise
(lem-weil-tower-category-levelwise-abelian). Thus levelwise F is exact and levelwise m
is an isomorphism. Apply the same two universal-property results to obtain E uniquely.
3. On an objectwise K-flat flat-term representative, evaluate the normalization of E.
The normalized evaluation equation of lem-cbc-derived-tower-evaluation-normalization
identifies it with the normalization of e after v_n. All unbounded towers have these
representatives by lem-weil-pbc-diagram-kflat-replacements. Naturality extends the
identity to every tower, respecting all transitions.
4. The counit normalization of lem-cbc-derived-constant-tower-normalization gives
b followed by E = Delta(e) followed by the exact constant comparison c. Check on a
K-flat flat-term representative, compose with the invertible target localization
comparison and cancel it; then descend by replacement and naturality. This is equality
in the strict derived tower category, rather than equality tested only by evaluation.
5. Write a_K : Delta K -> K_bullet for the published strict quotient augmentation.
By lem-cbc-strict-quotient-pullback-computation, the actual augmented map is b_K
followed by L_tower(a_K). The exact one is c_K followed by F_tower(a_K).
Naturality of E at a_K and Step 4 give their commutative square with Delta(e_K).
No quotient level is assumed K-flat.
6. Apply Rlim to E at K_bullet to obtain d_K. The constant/limit unit in
lem-coef-derived-tower-counit-projections is the compatible-family unit used in the
published ambient construction. Its naturality and Step 5 give alpha_K followed by
d_K = e_K followed by alpha^F_K. Total derived limit exists for unbounded towers by
lem-weil-pbc-ringed-strict-tower-homotopy-limit and prop-weil-pbc-rlim-functoriality.
7. Naturality of each actual derived-limit projection gives the last displayed square.
Step 3 identifies its evaluation of E. All constructions precede the restriction to
intrinsically complete objects, so every unbounded K is covered. -/
theorem counit_normalization
    (m : completedModulePullback g d ≅ moduleFunctor d g)
    (_hm : ModuleComparisonSpec d g m) :
    ∃ e : completedOrdinaryPullback g d ≅ (moduleFunctor d g).mapDerivedCategory,
      OrdinaryNormalized d g m e ∧
      (∀ e' : completedOrdinaryPullback g d ≅ (moduleFunctor d g).mapDerivedCategory,
        OrdinaryNormalized d g m e' → e' = e) ∧
      ∃ E : completedTowerPullback g d ≅ (towerFunctor d g).mapDerivedCategory,
        TowerNormalized d g m E ∧
        (∀ E' : completedTowerPullback g d ≅ (towerFunctor d g).mapDerivedCategory,
          TowerNormalized d g m E' → E' = E) ∧
        (∀ K : DerivedCategory (pbcModules X (pbcAdicCompletion X d)),
          (completedPullbackConstantIso g d).hom.app K ≫
              E.hom.app ((completedDerivedConstant d X).obj K) =
            (completedDerivedConstant d Y).map (e.hom.app K) ≫
              (constantIso d g).hom.app K) ∧
        (∀ K : DerivedCategory (pbcModules X (pbcAdicCompletion X d)),
          completedPullbackComparison g d K ≫ (completedIso d g E K).hom =
            e.hom.app K ≫ exactAugmentation d g K) ∧
        (∀ (K : DerivedCategory (pbcModules X (pbcAdicCompletion X d))) (n : ℕ),
          (completedIso d g E K).hom ≫
              (completedRlimProjection Y (pbcAdicCompletion Y d) n).app
                ((towerFunctor d g).mapDerivedCategory.obj ((completedReductionTower X d).obj K)) =
            (completedRlimProjection Y (pbcAdicCompletion Y d) n).app
                ((completedTowerPullback g d).obj ((completedReductionTower X d).obj K)) ≫
              (pbcTowerEvaluation Y (pbcAdicCompletion Y d) n).map
                (E.hom.app ((completedReductionTower X d).obj K))) ∧
        ∃ v : ∀ n : ℕ,
            completedTowerPullback g d ⋙ pbcTowerEvaluation Y (pbcAdicCompletion Y d) n ≅
              pbcTowerEvaluation X (pbcAdicCompletion X d) n ⋙ completedOrdinaryPullback g d,
          (∀ n : ℕ, EvaluationNormalized d g n (v n)) ∧
          (∀ (n : ℕ) (M : DerivedCategory (pbcTowers X (pbcAdicCompletion X d))),
            (pbcTowerEvaluation Y (pbcAdicCompletion Y d) n).map (E.hom.app M) ≫
                (evaluationIso d g n).hom.app M =
              (v n).hom.app M ≫
                e.hom.app ((pbcTowerEvaluation X (pbcAdicCompletion X d) n).obj M)) ∧
          (∀ (a b : ℕ) (h : a ≤ b)
              (M : DerivedCategory (pbcTowers X (pbcAdicCompletion X d))),
            (v b).hom.app M ≫ (completedOrdinaryPullback g d).map
                ((DerivedTowerPullback.derivedTransition
                  (A := pbcModules X (pbcAdicCompletion X d)) a b h).app M) =
              (DerivedTowerPullback.derivedTransition
                  (A := pbcModules Y (pbcAdicCompletion Y d)) a b h).app
                    ((completedTowerPullback g d).obj M) ≫ (v a).hom.app M) := by
  sorry

end ExactPullbackNormalization
end AlgebraicGeometry.Scheme
