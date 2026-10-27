/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q16
-/
module

public import Sheaf.Paper.TraceFormulaCoefficientConventions
public import Sheaf.Paper.InverseImagePullbackComparisonDerived
public import Sheaf.Paper.CompletedIntegralConstantMapOfUniverses
public import Sheaf.Paper.IntegralCoefficientPresentationComparison
public import Sheaf.Paper.AdicCoefficientDatum
public import Sheaf.Paper.PointProEtaleSectionsExact
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.Functor
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
public import Mathlib.CategoryTheory.Quotient
public import WeilConjectures.FromJoel.Algebra.Homology.HomologicalComplexFunctorEquiv
public import Sheaf.Paper.PointQuotientTowerData
public import Sheaf.Paper.PointQuotientTowerCoherentSource
import all Sheaf.Paper.IntegralOperationsWellDefined
import all Sheaf.Paper.IntegralReductionTowerUnrestricted

/-! # Quotient-section towers preserve homotopies

Source: blueprint main-20261015, sec-trace-formula/sk-d-weil,
prop-trf-rational-frobenius-integral-model.proof.md, clause (3)
(blueprint: lem-trf-point-quotient-tower-homotopy).

The index n denotes the positive exponent n+1. Both functors are constructed from
published strict quotient diagrams before localization. The coherent-source comparison
uses the normalized coefficient-presentation isomorphisms on the entire diagram.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale
namespace WeilConjectures.PointQuotientTower

attribute [local irreducible] completedIntegralCoefficientSheafUnrestricted
  completedIntegralCommRingSheafUnrestricted scalarReductionDerivedExistence
  HasDerivedCategory.standard pointIntegralSectionMap unrestrictedModuleStep
  unrestrictedTowerResolutionIso unrestrictedTowerUnit unrestrictedIntegralTransition
  unrestrictedIntegralReductionExistence scalarReductionExistence


variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

private instance sourceLevel_additive (n : ℕ) : (sourceLevel D l E n).Additive := by
  dsimp only [sourceLevel]
  infer_instance

private instance targetLevel_additive (g : Spec (.of D.k) ⟶ Spec (.of D.k)) (n : ℕ) :
    (targetLevel D l E g n).Additive := by
  let := integralOperationsLevelPullback_additive l E g n
  dsimp only [targetLevel]
  infer_instance

/-- The two strict quotient-section functors are additive and homotopical, and their
source is exact sections of the coefficient-transported coherent reduction tower.

Source: blueprint main-20261015, prop-trf-rational-frobenius-integral-model.proof.md,
clause (3) (blueprint: lem-trf-point-quotient-tower-homotopy).

Proof:
1. Use def-weil-inverse-system and the canonical tensor transitions to form both
   strict sheaf towers. Naturality on tensor generators gives their maps on chain
   maps. Termwise tensor, inverse image, restriction and sections are additive.
2. By lem-weil-tower-category-levelwise-abelian, module towers are abelian and
   evaluation preserves kernels and cokernels. It therefore preserves homology;
   joint reflection of isomorphisms detects quasi-isomorphisms levelwise.
3. Lem-pur-derived-change-of-rings preserves quasi-isomorphisms between K-flat
   complexes for every quotient, without quotient flatness. Exact restriction and
   lem-weil-point-proetale-sections-exact preserve them; step 2 assembles the levels.
4. Lem-weil-proetale-isomorphism-inverse-image identifies the finite pullback with
   inverse image and tensor along its coefficient isomorphism c_n. It is exact;
   its coefficient naturality makes its transitions balanced and compatible.
5. Tensor h with 1, apply the additive finite pullback when appropriate, and take
   sections. Applying these additive functors to f-f'=dh+hd proves the homotopy
   identity. Naturality in every component h makes these degree -1 maps commute
   with all quotient transitions, giving homotopies in the strict tower category.
6. The homotopies have equal localized images by def-weil-abstract-derived-category.
   The quotient universal property gives both factorizations through K(P).
7. Use def-weil-pbc-adic-coefficient-datum with pbcIntegralDatum: O_E is Noetherian,
   its residue field is finite torsion, and its finite quotients are perfect by the
   two-term uniformizer resolutions. Lem-weil-pbc-integral-coefficient-presentation-
   comparison gives the normalized e and level maps. Restriction along e preserves
   K-flatness and flat terms. The balanced maps b tensor x to e_n(b) tensor x,
   with inverse using e_n inverse, identify the entire strict reduction diagrams,
   including transitions and differentials. Its universal derived counit computes
   the coherent reduction tower on this representative. Exact sections on towers
   and lem-sf-exact-functor-derived-triangulated give the displayed comparison.
   Each evaluation computes N tensor^L S_n by lem-pur-derived-change-of-rings.
   The units x to 1 tensor x commute with quotient transitions and give the stated
   strict augmentation. Step 4 computes the finite pullback tower on the same P;
   all comparisons occur before evaluation, retaining the entire coherent diagram.
-/
theorem homotopical (_hl : l ≠ D.p) (g : Spec (.of D.k) ⟶ Spec (.of D.k)) [IsIso g] :
    Nonempty (Abelian (ℕᵒᵖ ⥤ ModuleCat.{u + 1}
      (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)))) ∧
    (∀ n : ℕ,
      PreservesFiniteLimits ((evaluation ℕᵒᵖ
        (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)))).obj
          (op n)) ∧
      PreservesFiniteColimits ((evaluation ℕᵒᵖ
        (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)))).obj
          (op n)) ∧
      ∀ i : ℤ, Nonempty
        (HomologicalComplex.homologyFunctor _ (.up ℤ) i ⋙
            (evaluation ℕᵒᵖ
              (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)))).obj
                (op n) ≅
          (((evaluation ℕᵒᵖ
            (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)))).obj
              (op n)).mapHomologicalComplex (.up ℤ)) ⋙
                HomologicalComplex.homologyFunctor _ (.up ℤ) i)) ∧
    (∀ (X Y : CochainComplex (ℕᵒᵖ ⥤ ModuleCat.{u + 1}
        (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E))) ℤ) (f : X ⟶ Y),
      QuasiIso f ↔ ∀ n : ℕ,
        QuasiIso (((HomologicalComplex.complexOfFunctorsToFunctorToComplex).map f).app
          (op n))) ∧
    ((integralOperationsGoodComplex l E (Spec (.of D.k))).ι ⋙ source D l E).Additive ∧
    ((integralOperationsGoodComplex l E (Spec (.of D.k))).ι ⋙ target D l E g).Additive ∧
    (∀ (P P' : (integralOperationsGoodComplex l E (Spec (.of D.k))).FullSubcategory)
      (f : P.obj ⟶ P'.obj), QuasiIso f →
        QuasiIso ((source D l E).map f) ∧ QuasiIso ((target D l E g).map f)) := by
  refine ⟨⟨inferInstance⟩, ?_, ?_, ?_, ?_, ?_⟩
  · intro n
    refine ⟨inferInstance, inferInstance, fun i ↦ ⟨?_⟩⟩
    exact Functor.isoWhiskerLeft (HomologicalComplex.shortComplexFunctor _ (.up ℤ) i)
      (ShortComplex.homologyFunctorIso ((CategoryTheory.evaluation ℕᵒᵖ _).obj (op n))).symm
  · intro X Y f
    exact (HomologicalComplex.quasiIso_iff_evaluation f).trans
      ⟨fun h n ↦ h (op n), fun h n ↦ h n.unop⟩
  · constructor
    intro P P' f f'
    apply HomologicalComplex.hom_ext
    intro i
    apply NatTrans.ext
    funext n
    change (sourceLevel D l E n.unop).map (f.hom.f i + f'.hom.f i) = _
    exact (sourceLevel D l E n.unop).map_add
  · constructor
    intro P P' f f'
    apply HomologicalComplex.hom_ext
    intro i
    apply NatTrans.ext
    funext n
    change (targetLevel D l E g n.unop).map (f.hom.f i + f'.hom.f i) = _
    exact (targetLevel D l E g n.unop).map_add
  · intro P P' f hf
    have hred (n : ℕ) :
        QuasiIso ((unrestrictedIntegralFiniteComplex l E (Spec (.of D.k)) n).map f) :=
      finiteReduction_quasiIso l E (Spec (.of D.k)) n f P.property P'.property hf
    constructor
    · apply (HomologicalComplex.quasiIso_iff_evaluation _).2
      intro n
      let R := scalarReductionRestriction l E (Spec (.of D.k)) n.unop
      have hR := HomologicalComplex.quasiIso_map_of_preservesHomology _ R
        (hφ := hred n.unop)
      exact HomologicalComplex.quasiIso_map_of_preservesHomology _
        (pointIntegralSections l E D.k) (hφ := hR)
    · apply (HomologicalComplex.quasiIso_iff_evaluation _).2
      intro n
      let F := integralOperationsLevelPullback l E g n.unop
      have he := Scheme.coefficientProEtaleModulePullback_exact.{u, u} g
        (CommRingCat.of (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n.unop + 1))))
      let : PreservesFiniteLimits F := he.1
      let : PreservesFiniteColimits F := he.2
      have hF := HomologicalComplex.quasiIso_map_of_preservesHomology _ F
        (hφ := hred n.unop)
      let R := scalarReductionRestriction l E (Spec (.of D.k)) n.unop
      have hR := HomologicalComplex.quasiIso_map_of_preservesHomology _ R (hφ := hF)
      exact HomologicalComplex.quasiIso_map_of_preservesHomology _
        (pointIntegralSections l E D.k) (hφ := hR)


private abbrev sourceSheafLevel (n : ℕ) :=
  unrestrictedIntegralReductionFunctor l E (Spec (.of D.k)) n ⋙
    scalarReductionRestriction l E (Spec (.of D.k)) n

private abbrev targetSheafLevel (g : Spec (.of D.k) ⟶ Spec (.of D.k)) (n : ℕ) :=
  unrestrictedIntegralReductionFunctor l E (Spec (.of D.k)) n ⋙
    integralOperationsLevelPullback l E g n ⋙
      scalarReductionRestriction l E (Spec (.of D.k)) n

private def sourceStep (n : ℕ) :
    unrestrictedIntegralComplexFunctor l E (Spec (.of D.k)) (n + 1) ⟶
      unrestrictedIntegralComplexFunctor l E (Spec (.of D.k)) n where
  app P :=
    { f i := unrestrictedModuleStep l E (Spec (.of D.k)) n (P.X i)
      comm' i j _ := by
        exact (unrestrictedModuleStep_naturality l E (Spec (.of D.k)) n (P.d i j)).symm }
  naturality P Q a := by
    ext i : 1
    exact unrestrictedModuleStep_naturality l E (Spec (.of D.k)) n (a.f i)

private theorem sourceTransition_eq (n : ℕ) :
    unrestrictedIntegralTransition l E (Spec (.of D.k)) n =
      sourceStep D l E n := by
  unfold unrestrictedIntegralTransition
  apply (unrestrictedIntegralTransition_existsUnique l E (Spec (.of D.k)) n).unique
    (unrestrictedIntegralTransition_existsUnique l E (Spec (.of D.k)) n).exists.choose_spec
  intro P i U b x
  exact unrestrictedModuleStep_tmul l E (Spec (.of D.k)) n (P.X i) U b x

private theorem sourceTransition_naturality (n : ℕ)
    (P Q : CochainComplex (integralTowerModules l E (Spec (.of D.k))) ℤ)
    (i j : ℤ) (a : P.X i ⟶ Q.X j) :
    (((unrestrictedIntegralTransition l E (Spec (.of D.k)) n).app P).f i) ≫
        (sourceSheafLevel D l E n).map a =
      (sourceSheafLevel D l E (n + 1)).map a ≫
        (((unrestrictedIntegralTransition l E (Spec (.of D.k)) n).app Q).f j) := by
  simpa only [sourceTransition_eq, sourceStep, Functor.comp_map] using
    (unrestrictedModuleStep_naturality l E (Spec (.of D.k)) n a).symm

private theorem targetTransition_eq (g : Spec (.of D.k) ⟶ Spec (.of D.k)) (n : ℕ) :
    integralOperationsPullbackTransition l E g n = integralPullbackTransitionCandidate l E g n := by
  apply (integralOperationsPullbackTransition_existsUnique l E g n).unique
    (integralOperationsPullbackTransition_existsUnique l E g n).exists.choose_spec
  intro P i V x
  exact SheafOfModules.IntegralPullbackProof.mateData_unit_formula
    (integralOperationsBaseChange g)
    (integralCoefficientSheafTransition l E (Spec (.of D.k)) n)
    (integralCoefficientSheafTransition l E (Spec (.of D.k)) n)
    (integralDirectRingMap l E g (n + 1)) (integralDirectRingMap l E g n)
    (integralDirectRingMap_square l E g n)
    (integralPullbackAdj l E g (n + 1)) (integralPullbackAdj l E g n)
    (((integralFiniteTransition l E (Spec (.of D.k)) n).app P).f i) (op V) x

private theorem targetTransition_naturality
    (g : Spec (.of D.k) ⟶ Spec (.of D.k)) (n : ℕ)
    (P Q : CochainComplex (integralTowerModules l E (Spec (.of D.k))) ℤ)
    (i j : ℤ) (a : P.X i ⟶ Q.X j) :
    (((integralOperationsPullbackTransition l E g n).app P).f i) ≫
        (targetSheafLevel D l E g n).map a =
      (targetSheafLevel D l E g (n + 1)).map a ≫
        (((integralOperationsPullbackTransition l E g n).app Q).f j) := by
  have hfinite :
      (unrestrictedIntegralReductionFunctor l E (Spec (.of D.k)) (n + 1)).map a ≫
          integralFiniteMap l E (Spec (.of D.k)) n Q j =
        integralFiniteMap l E (Spec (.of D.k)) n P i ≫
          (integralFiniteRestrict l E (Spec (.of D.k)) n).map
            ((unrestrictedIntegralReductionFunctor l E (Spec (.of D.k)) n).map a) := by
    ext U x
    exact congrArg (fun k ↦ k.val.app U x)
      (sourceTransition_naturality D l E n P Q i j a).symm
  have h := integralPullbackFiniteMap_naturality l E g n
    (integralFiniteMap l E (Spec (.of D.k)) n P i)
    (integralFiniteMap l E (Spec (.of D.k)) n Q j)
    ((unrestrictedIntegralReductionFunctor l E (Spec (.of D.k)) (n + 1)).map a)
    ((unrestrictedIntegralReductionFunctor l E (Spec (.of D.k)) n).map a) hfinite
  simp only [targetTransition_eq]
  ext U x
  exact congrArg (fun k ↦ k.val.app U x) h.symm

/-- The specified degree -1 maps are homotopies of whole strict diagrams.
Proof: apply additive tensor, finite pullback and sections to f-f'=dh+hd.
Naturality of the quotient transitions in each component of h makes every
component a tower map. This proves both homotopy identities degreewise.
Source: blueprint clause (3) (blueprint: lem-trf-point-quotient-tower-homotopy). -/
theorem homotopies (_hl : l ≠ D.p) (g : Spec (.of D.k) ⟶ Spec (.of D.k)) [IsIso g] :
    ∀ (P P' : (integralOperationsGoodComplex l E (Spec (.of D.k))).FullSubcategory)
      (f f' : P.obj ⟶ P'.obj) (h : Homotopy f f'),
      (∃ H : Homotopy ((source D l E).map f) ((source D l E).map f'),
        ∀ (i j : ℤ) (n : ℕ), (H.hom i j).app (op n) =
          (sourceLevel D l E n).map (h.hom i j)) ∧
      (∃ H : Homotopy ((target D l E g).map f) ((target D l E g).map f'),
        ∀ (i j : ℤ) (n : ℕ), (H.hom i j).app (op n) =
          (targetLevel D l E g n).map (h.hom i j)) := by
  intro P P' f f' h
  constructor
  · let H : Homotopy ((source D l E).map f) ((source D l E).map f') :=
      { hom := fun i j ↦ NatTrans.ofOpSequence
          (fun n ↦ (sourceLevel D l E n).map (h.hom i j)) (by
            intro n
            change (pointIntegralSections l E D.k).map
                (((Functor.ofOpSequence (unrestrictedIntegralTransition l E (Spec (.of D.k)))).map
                  (homOfLE (Nat.le_succ n)).op).app P.obj |>.f i) ≫
                    (pointIntegralSections l E D.k).map
                      ((sourceSheafLevel D l E n).map (h.hom i j)) =
              (pointIntegralSections l E D.k).map
                  ((sourceSheafLevel D l E (n + 1)).map (h.hom i j)) ≫
                (pointIntegralSections l E D.k).map
                  (((Functor.ofOpSequence (unrestrictedIntegralTransition l E (Spec (.of D.k)))).map
                    (homOfLE (Nat.le_succ n)).op).app P'.obj |>.f j)
            simp only [Functor.ofOpSequence_map_homOfLE_succ, ← Functor.map_comp]
            exact congrArg (pointIntegralSections l E D.k).map
              (sourceTransition_naturality D l E n P.obj P'.obj i j (h.hom i j)))
        zero := fun i j hij ↦ by
          apply NatTrans.ext
          funext n
          exact ((sourceLevel D l E n.unop).mapHomotopy h).zero i j hij
        comm := fun i ↦ by
          apply NatTrans.ext
          funext n
          exact ((sourceLevel D l E n.unop).mapHomotopy h).comm i }
    exact ⟨H, fun _ _ _ ↦ rfl⟩
  · let H : Homotopy ((target D l E g).map f) ((target D l E g).map f') :=
      { hom := fun i j ↦ NatTrans.ofOpSequence
          (fun n ↦ (targetLevel D l E g n).map (h.hom i j)) (by
            intro n
            change (pointIntegralSections l E D.k).map
                (((Functor.ofOpSequence (integralOperationsPullbackTransition l E g)).map
                  (homOfLE (Nat.le_succ n)).op).app P.obj |>.f i) ≫
                    (pointIntegralSections l E D.k).map
                      ((targetSheafLevel D l E g n).map (h.hom i j)) =
              (pointIntegralSections l E D.k).map
                  ((targetSheafLevel D l E g (n + 1)).map (h.hom i j)) ≫
                (pointIntegralSections l E D.k).map
                  (((Functor.ofOpSequence (integralOperationsPullbackTransition l E g)).map
                    (homOfLE (Nat.le_succ n)).op).app P'.obj |>.f j)
            simp only [Functor.ofOpSequence_map_homOfLE_succ, ← Functor.map_comp]
            exact congrArg (pointIntegralSections l E D.k).map
              (targetTransition_naturality D l E g n P.obj P'.obj i j (h.hom i j)))
        zero := fun i j hij ↦ by
          apply NatTrans.ext
          funext n
          exact ((targetLevel D l E g n.unop).mapHomotopy h).zero i j hij
        comm := fun i ↦ by
          apply NatTrans.ext
          funext n
          exact ((targetLevel D l E g n.unop).mapHomotopy h).comm i }
    exact ⟨H, fun _ _ _ ↦ rfl⟩


/-- Both localized functors factor through the homotopy category of the good complexes.
Proof: the specified homotopies in homotopies give equal maps after localization
by def-weil-abstract-derived-category. Apply the quotient category universal
property to this relation for each of the two functors.
Source: blueprint clause (3) (blueprint: lem-trf-point-quotient-tower-homotopy). -/
theorem homotopyDescent (_hl : l ≠ D.p) (g : Spec (.of D.k) ⟶ Spec (.of D.k)) [IsIso g] :
    ∃ F G : CategoryTheory.Quotient (goodHomotopyRelation D l E) ⥤
        DerivedCategory (ℕᵒᵖ ⥤ ModuleCat.{u + 1}
          (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E))),
      Nonempty (CategoryTheory.Quotient.functor (goodHomotopyRelation D l E) ⋙ F ≅
        (integralOperationsGoodComplex l E (Spec (.of D.k))).ι ⋙ source D l E ⋙
          DerivedCategory.Q) ∧
      Nonempty (CategoryTheory.Quotient.functor (goodHomotopyRelation D l E) ⋙ G ≅
        (integralOperationsGoodComplex l E (Spec (.of D.k))).ι ⋙ target D l E g ⋙
          DerivedCategory.Q) := by
  let S := (integralOperationsGoodComplex l E (Spec (.of D.k))).ι ⋙
    source D l E ⋙ DerivedCategory.Q
  let T := (integralOperationsGoodComplex l E (Spec (.of D.k))).ι ⋙
    target D l E g ⋙ DerivedCategory.Q
  have hS : ∀ P P' (f f' : P ⟶ P'), goodHomotopyRelation D l E f f' →
      S.map f = S.map f' := by
    intro P P' f f' ⟨h⟩
    obtain ⟨H, _⟩ := (homotopies D l E _hl g P P' f.hom f'.hom h).1
    exact DerivedCategory.Q_map_eq_of_homotopy _ H
  have hT : ∀ P P' (f f' : P ⟶ P'), goodHomotopyRelation D l E f f' →
      T.map f = T.map f' := by
    intro P P' f f' ⟨h⟩
    obtain ⟨H, _⟩ := (homotopies D l E _hl g P P' f.hom f'.hom h).2
    exact DerivedCategory.Q_map_eq_of_homotopy _ H
  exact ⟨CategoryTheory.Quotient.lift _ S hS, CategoryTheory.Quotient.lift _ T hT,
    ⟨CategoryTheory.Quotient.lift.isLift _ S hS⟩,
    ⟨CategoryTheory.Quotient.lift.isLift _ T hT⟩⟩


private theorem source_asFunctor
    (P : CochainComplex (integralTowerModules l E (Spec (.of D.k))) ℤ) :
    ((source D l E).obj P).asFunctor =
      (Functor.ofOpSequence
        (unrestrictedIntegralTransition l E (Spec (.of D.k)))).flip.obj P ⋙
          (pointIntegralSections l E D.k).mapHomologicalComplex (.up ℤ) := by
  rfl

private theorem sourceComplex_eq (n : ℕ)
    (P : CochainComplex (integralTowerModules l E (Spec (.of D.k))) ℤ) :
    (unrestrictedIntegralComplexFunctor l E (Spec (.of D.k)) n).obj P =
      unrestrictedTowerComplex l E (Spec (.of D.k)) n P := by
  unfold unrestrictedIntegralComplexFunctor unrestrictedIntegralFiniteComplex
    unrestrictedTowerComplex unrestrictedTowerFiniteComplex
    unrestrictedIntegralReductionFunctor
  rfl

private theorem coefficientStep_one (n : ℕ) (U : (Spec (.of D.k)).ProEtᵒᵖ) :
    ((integralCoefficientSheafTransition l E (Spec (.of D.k)) n).hom.app U)
        (1 : (integralCoefficientCommRingSheaf l E (Spec (.of D.k)) (n + 1)).obj.obj U) =
      (1 : (integralCoefficientCommRingSheaf l E (Spec (.of D.k)) n).obj.obj U) := by
  exact ((integralCoefficientSheafTransition l E (Spec (.of D.k)) n).hom.app U).hom.map_one

attribute [local irreducible] constantSheaf presheafToSheaf integralCoefficientCommRingSheaf

attribute [-instance] CategoryTheory.catToReflQuiver in
set_option backward.isDefEq.respectTransparency true in
/-- The quotient unit is a strict augmentation, including every transition.
Proof: the published unit sends x to 1 tensor x. Each coefficient transition sends
1 to 1, so the strict quotient transition composed with the higher unit is the
lower unit, on pure tensors. Sheafification and degreewise equality give the
chain-map equality. Taking sections and NatTrans.ofOpSequence give a.
Source: blueprint clause (3) (blueprint: lem-trf-point-quotient-tower-homotopy). -/
theorem quotientAugmentation (_hl : l ≠ D.p) :
    ∀ P : (integralOperationsGoodComplex l E (Spec (.of D.k))).FullSubcategory,
      ∃ a : (Functor.const ℕᵒᵖ).obj
          (((pointIntegralSections l E D.k).mapHomologicalComplex (.up ℤ)).obj P.obj) ⟶
        ((source D l E).obj P.obj).asFunctor,
        ∀ n : ℕ, HEq (a.app (op n))
          (((pointIntegralSections l E D.k).mapHomologicalComplex (.up ℤ)).map
            (unrestrictedTowerUnit l E (Spec (.of D.k)) P.obj n)) := by
  intro P
  rw [source_asFunctor]
  generalize (pointIntegralSections l E D.k).mapHomologicalComplex (.up ℤ) = Γ
  let a : (Functor.const ℕᵒᵖ).obj P.obj ⟶
      (Functor.ofOpSequence
        (unrestrictedIntegralTransition l E (Spec (.of D.k)))).flip.obj P.obj :=
    NatTrans.ofOpSequence (fun n ↦ by
      change P.obj ⟶
        (unrestrictedIntegralComplexFunctor l E (Spec (.of D.k)) n).obj P.obj
      have v := unrestrictedTowerUnit l E (Spec (.of D.k)) P.obj n
      dsimp only [unrestrictedIntegralComplexFunctor, unrestrictedIntegralFiniteComplex,
        unrestrictedTowerComplex, unrestrictedTowerFiniteComplex,
        unrestrictedIntegralReductionFunctor, scalarReductionExtension,
        unrestrictedIntegralReductionExistence, scalarReductionExistence,
        Functor.comp_obj] at v ⊢
      exact v) (by
        intro n
        simp only [Functor.const_obj_map, Functor.flip_obj_map,
          Functor.ofOpSequence_map_homOfLE_succ]
        have hunit := unrestrictedTowerUnit_condition l E (Spec (.of D.k)) P.obj
        symm
        ext i U x
        change
          (((unrestrictedIntegralTransition l E (Spec (.of D.k)) n).app P.obj).f i).val.app U
              ((((unrestrictedTowerUnit l E (Spec (.of D.k)) P.obj (n + 1)).f i).val.app U) x) =
            (((unrestrictedTowerUnit l E (Spec (.of D.k)) P.obj n).f i).val.app U) x
        erw [hunit (n + 1) i U x, hunit n i U x]
        simpa only [unrestrictedTowerTensorSection, unrestrictedIntegralTransition,
          coefficientStep_one] using
          (unrestrictedIntegralTransition_existsUnique l E (Spec (.of D.k)) n).exists.choose_spec
            P.obj i U 1 x)
  refine ⟨(Functor.constComp (J := ℕᵒᵖ) P.obj Γ).inv ≫ Functor.whiskerRight a Γ, ?_⟩
  intro n
  dsimp only [NatTrans.comp_app, Functor.constComp_inv_app,
    Functor.whiskerRight_app, a, NatTrans.ofOpSequence_app]
  erw [Category.id_comp]
  rfl


attribute [local irreducible] Functor.mapDerivedCategory Functor.mapDerivedCategoryFactors
  Functor.mapDerivedCategoryFactorsh

/-- Evaluation of D(P) computes sections of the derived finite reduction of [P].
This is a corollary of the whole-diagram comparison, not a replacement for it.
Source: blueprint clause (3) (blueprint: lem-trf-point-quotient-tower-homotopy).
Proof: the universal scalar-extension counit identifies the ordinary reduction of
K-flat P with [P] tensor^L S_n by lem-pur-derived-change-of-rings. Restriction is
exact, and point sections are exact by lem-weil-point-proetale-sections-exact.
Apply their exact derived functors and their localization factorizations to this
counit isomorphism; its target is exactly the nth evaluation of source. -/
theorem evaluation (_hl : l ≠ D.p)
    (P : (integralOperationsGoodComplex l E (Spec (.of D.k))).FullSubcategory) (n : ℕ) :
    Nonempty
      (DerivedCategory.Q.obj (((source D l E).obj P.obj).asFunctor.obj (op n)) ≅
        (pointIntegralSections l E D.k).mapDerivedCategory.obj
          ((scalarReductionDerivedRestriction l E (Spec (.of D.k)) n).obj
            ((scalarReductionDerivedExtension l E (Spec (.of D.k)) n).obj
              (DerivedCategory.Q.obj P.obj)))) := by
  rw [source_asFunctor]
  change Nonempty
    (DerivedCategory.Q.obj
      (((pointIntegralSections l E D.k).mapHomologicalComplex (.up ℤ)).obj
        ((unrestrictedIntegralComplexFunctor l E (Spec (.of D.k)) n).obj P.obj)) ≅ _)
  rw [sourceComplex_eq]
  dsimp only [scalarReductionDerivedRestriction]
  have e := unrestrictedTowerResolutionIso l E (Spec (.of D.k)) n (𝟙 P.obj)
    ⟨inferInstance, P.property.1⟩
  exact ⟨((pointIntegralSections l E D.k).mapDerivedCategoryFactors.app
      (unrestrictedTowerComplex l E (Spec (.of D.k)) n P.obj)).symm ≪≫
    (pointIntegralSections l E D.k).mapDerivedCategory.mapIso
      (((scalarReductionRestriction l E (Spec (.of D.k)) n).mapDerivedCategoryFactors.app
        (unrestrictedTowerFiniteComplex l E (Spec (.of D.k)) n P.obj)).symm ≪≫
        (scalarReductionRestriction l E (Spec (.of D.k)) n).mapDerivedCategory.mapIso e.symm)⟩


end WeilConjectures.PointQuotientTower
