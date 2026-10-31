/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CompletedIntegralCoefficientGerm
public import WeilConjectures.AlgebraicGeometry.IntegralScalarExtensionUniverses
public import WeilConjectures.AlgebraicGeometry.IntegralOperationsWellDefinedSupplement
public import WeilConjectures.AlgebraicGeometry.FiniteFreeCompletedScalarComparison
public import WeilConjectures.CategoryTheory.StrictRoosModel
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.Algebra.Homology.Functor
public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCocone
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import WeilConjectures.CategoryTheory.Limits.TowerTransitionEndomorphism
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
import all WeilConjectures.AlgebraicGeometry.ExactProductFunctorRoosChainMaps
import all WeilConjectures.CategoryTheory.StrictRoosComparison
import all WeilConjectures.CategoryTheory.RingedStrictTowerHomotopyLimitOfUniverses
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
import all Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import all Mathlib.CategoryTheory.Preadditive.Injective.Basic
import all Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import all Mathlib.Algebra.Homology.HomologicalComplexLimits
import all WeilConjectures.CategoryTheory.Limits.TowerTransitionEndomorphism
import all WeilConjectures.CategoryTheory.StrictRoosDerivation
import all WeilConjectures.CategoryTheory.StrictRoosModel
import all Mathlib.CategoryTheory.Functor.Derived.RightDerived
import all Mathlib.CategoryTheory.Whiskering
import all Mathlib.Algebra.Homology.Functor
import all Mathlib.CategoryTheory.Limits.Shapes.Countable
import all Mathlib.Algebra.Homology.HomotopyCategory.MappingCocone
import all Mathlib.CategoryTheory.Abelian.FunctorCategory
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import all WeilConjectures.Algebra.Homology.RoosComplex
import all WeilConjectures.Algebra.Homology.DerivedCategory.TowerLimit
import all WeilConjectures.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
import all WeilConjectures.CategoryTheory.Sites.RGammaDerivedLimitSupplement
import all Mathlib.Algebra.Category.Grp.AB
import all Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all Mathlib.LinearAlgebra.Finsupp.LinearCombination
import all Mathlib.CategoryTheory.Adjunction.Evaluation
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
import all Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import all WeilConjectures.CategoryTheory.StrictRoosNormalization
import all Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import all Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import all WeilConjectures.AlgebraicGeometry.IntegralOperationsWellDefinedSupplement
import all WeilConjectures.AlgebraicGeometry.FiniteFreeCompletedScalarComparison

/-! # Whole-cone sections of the quotient augmentation

Source: blueprint main-20261015, sec-trace-formula/sk-d-weil,
prop-trf-rational-frobenius-integral-model.proof.md, clause (3); Stacks Tag 0941,
lemma-derived-limit-is-ok (blueprint: lem-trf-point-quotient-augmentation-diagram).

The existing strict quotient tower, diagonal Roos functor, tensor augmentation and
specified scalar-extension localization are retained. Level n means exponent n+1.
No finite-field datum, completeness, constructibility or boundedness is assumed.
The two-coordinate equations specify the section comparison before localization.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology
attribute [-instance] WeilConjectures.PrincipalKoszulStrictReplacement.abSheafify
attribute [-instance] WeilConjectures.PrincipalKoszulStrictReplacement.abLocallyBijective
attribute [-instance] WeilConjectures.PrincipalKoszulStrictReplacement.siteSmall
attribute [-instance] WeilConjectures.integralOperationsAbSheafify
attribute [-instance] WeilConjectures.integralOperationsAbLocallyBijective
attribute [-instance] WeilConjectures.integralOperationsSiteSmall

attribute [local irreducible] CategoryTheory.constantSheaf HasDerivedCategory.standard
  CategoryTheory.Limits.limit

universe u a b v w
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures.PointQuotientAugmentation

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (k : Type u) [Field k] [IsAlgClosed k]

/-- Exact final-object sections with the existing canonical integral scalar action.
Source: blueprint clause (3); Stacks 0946
(blueprint: lem-trf-point-quotient-augmentation-diagram). -/
abbrev sections := (pointIntegralSections l E k).mapHomologicalComplex (.up ℤ)

/-- The actual quotient tower, including restriction of scalars and its transitions.
Source: blueprint clause (3); Bhatt--Scholze 3.4.10
(blueprint: lem-trf-point-quotient-augmentation-diagram). -/
abbrev reductions := integralScalarTowerFunctor l E E (AlgHom.id ℚ_[l] E) (Spec (.of k))

/-- The chain functor P ↦ H(Γ T(P)); maps are the published diagonal Roos maps.
Source: blueprint clause (3); Stacks 0941
(blueprint: lem-trf-point-quotient-augmentation-diagram). -/
def sectionRoos := reductions l E k ⋙
  (Functor.whiskeringRight ℕᵒᵖ _ _).obj (sections l E k) ⋙ integralOperationsRoosFunctor

/-- The source of the canonical comparison on arbitrary strict towers.
Source: Stacks 0941 (blueprint: lem-trf-point-quotient-augmentation-diagram). -/
def roosSections := integralOperationsRoosFunctor ⋙ sections l E k

/-- The target of the canonical comparison on arbitrary strict towers.
Source: Stacks 0941 (blueprint: lem-trf-point-quotient-augmentation-diagram). -/
def sectionsRoos :=
  (Functor.whiskeringRight ℕᵒᵖ _ _).obj (sections l E k) ⋙ integralOperationsRoosFunctor

/-- The fixed small-Hom localization of ordinary integral module complexes.
Source: Stacks 05RU (blueprint: lem-trf-point-quotient-augmentation-diagram). -/
abbrev moduleQ := @DerivedCategory.Q
  (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E))) _ _
  (HasDerivedCategory.ofIsGrothendieckAbelian _)

/-- Finite-limit exactness is the recorded point theorem followed by scalar restriction.
Source: Stacks 0946 (blueprint: lem-trf-point-quotient-augmentation-diagram). -/
instance sectionsLimits : PreservesFiniteLimits (pointIntegralSections l E k) :=
  @comp_preservesFiniteLimits _ _ _ _ _ _
    (ProEtale.pointModuleSections k (completedIntegralCommRingSheafUnrestricted l E
      (Spec (.of k))))
    (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} (pointIntegralSectionMap l E k))
    ((ProEtale.point_proEtale_sections_exact.{u, u + 2, u + 2} k).2 _).1 inferInstance

/-- Finite-colimit exactness is the same point theorem followed by scalar restriction.
Source: Stacks 0946 (blueprint: lem-trf-point-quotient-augmentation-diagram). -/
instance sectionsColimits : PreservesFiniteColimits (pointIntegralSections l E k) :=
  @comp_preservesFiniteColimits _ _ _ _ _ _
    (ProEtale.pointModuleSections k (completedIntegralCommRingSheafUnrestricted l E
      (Spec (.of k))))
    (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} (pointIntegralSectionMap l E k))
    ((ProEtale.point_proEtale_sections_exact.{u, u + 2, u + 2} k).2 _).2.1 inferInstance

/-- Unbounded derived sections, with the same module localization as moduleQ.
Source: Stacks 015F (blueprint: lem-trf-point-quotient-augmentation-diagram). -/
def derivedSections := @Functor.mapDerivedCategory _ _ _ (HasDerivedCategory.standard _)
  _ _ _ (HasDerivedCategory.ofIsGrothendieckAbelian _) (pointIntegralSections l E k)
  (pointIntegralSectionsAdditive l E k) (sectionsLimits l E k) (sectionsColimits l E k)

/-- The specified comparison with termwise sections on complexes.
Source: Stacks 015F (blueprint: lem-trf-point-quotient-augmentation-diagram). -/
def factors : DerivedCategory.Q ⋙ derivedSections l E k ≅
    sections l E k ⋙ moduleQ l E :=
  @Functor.mapDerivedCategoryFactors _ _ _ (HasDerivedCategory.standard _)
    _ _ _ (HasDerivedCategory.ofIsGrothendieckAbelian _) (pointIntegralSections l E k)
    (pointIntegralSectionsAdditive l E k) (sectionsLimits l E k) (sectionsColimits l E k)

/-- The prescribed identity-extension quotient completion on the full derived category.
Source: Bhatt--Scholze 3.4.10
(blueprint: lem-trf-point-quotient-augmentation-diagram). -/
abbrev completion :=
  integralScalarExtensionOfUniverses l E E (AlgHom.id ℚ_[l] E) (Spec (.of k))

/-- Completion followed by exact integral sections.
Source: blueprint clause (3) (blueprint: lem-trf-point-quotient-augmentation-diagram). -/
def completedSections := completion l E k ⋙ derivedSections l E k

/-- The section augmentation, using the existing tensor unit and whole-cone comparison.
The theorem below fixes the comparison on both coordinates.
Source: blueprint clause (3) (blueprint: lem-trf-point-quotient-augmentation-diagram). -/
def augmentation (c : roosSections l E k ≅ sectionsRoos l E k)
    (P : CochainComplex (integralTowerModules l E (Spec (.of k))) ℤ) :
    (sections l E k).obj P ⟶ (sectionRoos l E k).obj P :=
  (sections l E k).map ((completedScalarIdentityUnit l E (Spec (.of k))).app P) ≫
    c.hom.app ((reductions l E k).obj P)

/-- The specified localization comparison including q, exact sections' factorization,
and the canonical two-coordinate comparison, in that order.
Source: blueprint clause (3) (blueprint: lem-trf-point-quotient-augmentation-diagram). -/
def model (c : roosSections l E k ≅ sectionsRoos l E k)
    (K : DerivedCategory (integralTowerModules l E (Spec (.of k))))
    (P : (integralOperationsGoodComplex l E (Spec (.of k))).FullSubcategory)
    (q : DerivedCategory.Q.obj P.obj ≅ K) :
    (completedSections l E k).obj K ≅ (moduleQ l E).obj ((sectionRoos l E k).obj P.obj) :=
  (completedSections l E k).mapIso q.symm ≪≫
    (derivedSections l E k).mapIso
      ((integralScalarExtensionComparisonOfUniverses l E E (AlgHom.id ℚ_[l] E)
        (Spec (.of k))).app P) ≪≫
    (factors l E k).app
      ((integralScalarComplexFunctor l E E (AlgHom.id ℚ_[l] E) (Spec (.of k))).obj P.obj) ≪≫
    (moduleQ l E).mapIso (c.app ((reductions l E k).obj P.obj))

/-- A comparison preserves both actual cone coordinates, with every product projection fixed.
This condition specifies the canonical product comparison, before localization.
Source: Stacks 0941 (blueprint: lem-trf-point-quotient-augmentation-diagram). -/
def RoosCoordinates
    {A : Type a} [Category.{v} A] [Abelian A] [HasCountableProducts A]
    {B : Type b} [Category.{w} B] [Abelian B] [HasCountableProducts B]
    (F : A ⥤ B) [F.Additive]
    (c : integralOperationsRoosFunctor ⋙ F.mapHomologicalComplex (.up ℤ) ≅
      (Functor.whiskeringRight ℕᵒᵖ _ _).obj (F.mapHomologicalComplex (.up ℤ)) ⋙
        integralOperationsRoosFunctor) : Prop :=
  (∀ (T : ℕᵒᵖ ⥤ CochainComplex A ℤ)
        (n : ℕ) (i : ℤ),
        (c.hom.app T).f i ≫
          (CochainComplex.mappingCocone.fst
            (towerTransitionEndomorphism
              (K := fun m : ℕ ↦ (T ⋙ F.mapHomologicalComplex (.up ℤ)).obj (op m))
              (fun m ↦ (T ⋙ F.mapHomologicalComplex (.up ℤ)).map
                (homOfLE (Nat.le_succ m)).op))).f i ≫
          (Pi.π (fun m ↦ (T ⋙ F.mapHomologicalComplex (.up ℤ)).obj (op m)) n).f i =
        F.map
          ((CochainComplex.mappingCocone.fst
            (towerTransitionEndomorphism (K := fun m : ℕ ↦ T.obj (op m))
              (fun m ↦ T.map (homOfLE (Nat.le_succ m)).op))).f i ≫
            (Pi.π (fun m ↦ T.obj (op m)) n).f i)) ∧
  (∀ (T : ℕᵒᵖ ⥤ CochainComplex A ℤ)
        (n : ℕ) (i : ℤ),
        (c.hom.app T).f i ≫
          (CochainComplex.mappingCocone.snd
            (towerTransitionEndomorphism
              (K := fun m : ℕ ↦ (T ⋙ F.mapHomologicalComplex (.up ℤ)).obj (op m))
              (fun m ↦ (T ⋙ F.mapHomologicalComplex (.up ℤ)).map
                (homOfLE (Nat.le_succ m)).op))).v i (i + -1) rfl ≫
          (Pi.π (fun m ↦ (T ⋙ F.mapHomologicalComplex (.up ℤ)).obj (op m)) n).f (i + -1) =
        F.map
          ((CochainComplex.mappingCocone.snd
            (towerTransitionEndomorphism (K := fun m : ℕ ↦ T.obj (op m))
              (fun m ↦ T.map (homOfLE (Nat.le_succ m)).op))).v i (i + -1) rfl ≫
            (Pi.π (fun m ↦ T.obj (op m)) n).f (i + -1)))

section Proof
attribute [-instance] WeilConjectures.integralOperationsCommHasDerivedCategory
attribute [local instance 5000] WeilConjectures.integralTowerHasDerivedCategory

attribute [local irreducible] completedIntegralCommRingSheafUnrestricted
  completedIntegralCoefficientSheafUnrestricted pointIntegralSectionMap
  integralScalarTowerFunctor completedScalarIdentityUnit
attribute [local irreducible] integralScalarExtensionOfUniverses
  integralScalarExtensionComparisonOfUniverses
attribute [local irreducible] HasDerivedCategory.ofIsGrothendieckAbelian
  HasDerivedCategory.ofHasKInjectiveResolutions
attribute [local irreducible] DerivedCategory.Q Functor.mapDerivedCategory
  Functor.mapDerivedCategoryFactors

omit [IsAlgClosed k] in
private theorem sectionsProducts :
    PreservesLimitsOfShape (Discrete ℕ) (pointIntegralSections l E k) := by
  let U := ModuleCat.restrictScalars.{u + 1, u + 1, u + 1}
    (pointIntegralSectionMap l E k)
  have : PreservesLimitsOfShape (Discrete ℕ) U := ⟨fun {D} ↦
    ModuleCat.preservesLimit_restrictScalars (pointIntegralSectionMap l E k) D⟩
  exact @comp_preservesLimitsOfShape _ _ _ _ _ _ _ _
    (ProEtale.pointModuleSections k (completedIntegralCommRingSheafUnrestricted l E
      (Spec (.of k))))
    (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} (pointIntegralSectionMap l E k))
    inferInstance inferInstance

section Comparison
variable {A : Type a} [Category.{v} A] [Abelian A] [HasCountableProducts A]
  {B : Type b} [Category.{w} B] [Abelian B] [HasCountableProducts B]
  (F : A ⥤ B) [F.Additive] [PreservesLimitsOfShape (Discrete ℕ) F]

private abbrev boundary (T : ℕᵒᵖ ⥤ CochainComplex A ℤ) :=
  towerTransitionEndomorphism (K := fun n ↦ T.obj (op n)) (integralOperationsTowerStep T)

private theorem roosMap_fst {T T' : ℕᵒᵖ ⥤ CochainComplex A ℤ} (f : T ⟶ T')
    (p : ℤ) :
    (integralOperationsRoosMap f).f (p + 1) ≫
        (CochainComplex.mappingCocone.fst (boundary T')).f (p + 1) =
      (CochainComplex.mappingCocone.fst (boundary T)).f (p + 1) ≫
        (Limits.Pi.map (fun n ↦ f.app (op n))).f (p + 1) := by
  let m := HomologicalComplex.homotopyCofiber.mapArrowHom (boundary T) (boundary T')
    (fun j ↦ ⟨j - 1, Int.sub_add_cancel j 1⟩)
    (Arrow.homMk (Limits.Pi.map (fun n ↦ f.app (op n)))
      (Limits.Pi.map (fun n ↦ f.app (op n))) (integralOperationsRoos_square f).symm)
  have h : m.f p ≫ HomologicalComplex.homotopyCofiber.fstX (boundary T') p (p + 1) rfl =
      HomologicalComplex.homotopyCofiber.fstX (boundary T) p (p + 1) rfl ≫
        (Limits.Pi.map (fun n ↦ f.app (op n))).f (p + 1) := by
    dsimp only [m]
    rw [HomologicalComplex.homotopyCofiber.mapArrowHom,
      HomologicalComplex.homotopyCofiber.desc_f _ _ _ p (p + 1) rfl]
    simp [Category.assoc, HomologicalComplex.homotopyCofiber.inrCompHomotopy_hom]
  have hs : ((shiftFunctor _ (-1 : ℤ)).map m).f (p + 1) ≫
      ((CochainComplex.mappingCone (boundary T')).shiftFunctorObjXIso (-1) (p + 1) p
        (by omega)).hom ≫ HomologicalComplex.homotopyCofiber.fstX
          (boundary T') p (p + 1) rfl =
      ((CochainComplex.mappingCone (boundary T)).shiftFunctorObjXIso (-1) (p + 1) p
        (by omega)).hom ≫ HomologicalComplex.homotopyCofiber.fstX
          (boundary T) p (p + 1) rfl ≫
        (Limits.Pi.map (fun n ↦ f.app (op n))).f (p + 1) := by
    dsimp only [CochainComplex.mappingCone]
    change m.f (p + 1 + -1) ≫ _ ≫ _ = _
    erw [CochainComplex.shiftFunctorObjXIso,
      HomologicalComplex.XIsoOfEq_hom_naturality_assoc, h]
    rfl
  simpa [integralOperationsRoosMap, m, boundary,
    CochainComplex.mappingCocone.fst, CochainComplex.HomComplex.Cocycle.homOf,
    CochainComplex.HomComplex.Cochain.leftShift_v, CochainComplex.mappingCone.fst,
    HomologicalComplex.homotopyCofiber.fstX, Category.assoc] using! hs

private theorem roosMap_snd {T T' : ℕᵒᵖ ⥤ CochainComplex A ℤ} (f : T ⟶ T')
    (p : ℤ) :
    (integralOperationsRoosMap f).f (p + 1) ≫
        (CochainComplex.mappingCocone.snd (boundary T')).v (p + 1) p (by omega) =
      (CochainComplex.mappingCocone.snd (boundary T)).v (p + 1) p (by omega) ≫
        (Limits.Pi.map (fun n ↦ f.app (op n))).f p := by
  let m := HomologicalComplex.homotopyCofiber.mapArrowHom (boundary T) (boundary T')
    (fun j ↦ ⟨j - 1, Int.sub_add_cancel j 1⟩)
    (Arrow.homMk (Limits.Pi.map (fun n ↦ f.app (op n)))
      (Limits.Pi.map (fun n ↦ f.app (op n))) (integralOperationsRoos_square f).symm)
  have h : m.f p ≫ HomologicalComplex.homotopyCofiber.sndX (boundary T') p =
      HomologicalComplex.homotopyCofiber.sndX (boundary T) p ≫
        (Limits.Pi.map (fun n ↦ f.app (op n))).f p := by
    dsimp only [m]
    rw [HomologicalComplex.homotopyCofiber.mapArrowHom,
      HomologicalComplex.homotopyCofiber.desc_f _ _ _ p (p + 1) rfl]
    simp [Category.assoc, HomologicalComplex.homotopyCofiber.inrCompHomotopy_hom]
  have hs : ((shiftFunctor _ (-1 : ℤ)).map m).f (p + 1) ≫
      ((CochainComplex.mappingCone (boundary T')).shiftFunctorObjXIso (-1) (p + 1) p
        (by omega)).hom ≫ HomologicalComplex.homotopyCofiber.sndX (boundary T') p =
      ((CochainComplex.mappingCone (boundary T)).shiftFunctorObjXIso (-1) (p + 1) p
        (by omega)).hom ≫ HomologicalComplex.homotopyCofiber.sndX (boundary T) p ≫
        (Limits.Pi.map (fun n ↦ f.app (op n))).f p := by
    dsimp only [CochainComplex.mappingCone]
    change m.f (p + 1 + -1) ≫ _ ≫ _ = _
    erw [CochainComplex.shiftFunctorObjXIso,
      HomologicalComplex.XIsoOfEq_hom_naturality_assoc, h]
    rfl
  simpa [integralOperationsRoosMap, m, boundary,
    CochainComplex.mappingCocone.snd, CochainComplex.HomComplex.Cochain.leftShift_v,
    CochainComplex.mappingCone.snd, Category.assoc,
    show Int.negOnePow 2 = 1 by rfl] using! hs

private def coneComparison (T : ℕᵒᵖ ⥤ CochainComplex A ℤ) :
    (F.mapHomologicalComplex (.up ℤ)).obj (integralOperationsRoos T) ≅
      integralOperationsRoos (T ⋙ F.mapHomologicalComplex (.up ℤ)) :=
  CategoryTheory.cs F (boundary T) (boundary (T ⋙ F.mapHomologicalComplex (.up ℤ)))
    (asIso (piComparison (F.mapHomologicalComplex (.up ℤ)) (fun n ↦ T.obj (op n))))
    (CategoryTheory.productComparison_transition F _ _)

private theorem coneComparison_fst (T : ℕᵒᵖ ⥤ CochainComplex A ℤ) (p : ℤ) :
    (coneComparison F T).hom.f (p + 1) ≫
        (CochainComplex.mappingCocone.fst (boundary
          (T ⋙ F.mapHomologicalComplex (.up ℤ)))).f (p + 1) =
      F.map ((CochainComplex.mappingCocone.fst (boundary T)).f (p + 1)) ≫
        (piComparison (F.mapHomologicalComplex (.up ℤ))
          (fun n ↦ T.obj (op n))).f (p + 1) := by
  simpa [coneComparison, boundary, integralOperationsTowerStep, integralOperationsRoos,
    CochainComplex.mappingCocone,
    CochainComplex.mappingCocone.fst,
    CochainComplex.HomComplex.Cocycle.homOf,
    CochainComplex.HomComplex.Cochain.leftShift_v, CochainComplex.mappingCone.fst,
    HomologicalComplex.homotopyCofiber.fstX, Category.assoc] using!
    CategoryTheory.cs_fst F (boundary T) _
      (asIso (piComparison (F.mapHomologicalComplex (.up ℤ)) (fun n ↦ T.obj (op n))))
      (CategoryTheory.productComparison_transition F _ _) p

private theorem coneComparison_snd (T : ℕᵒᵖ ⥤ CochainComplex A ℤ) (p : ℤ) :
    (coneComparison F T).hom.f (p + 1) ≫
        (CochainComplex.mappingCocone.snd (boundary
          (T ⋙ F.mapHomologicalComplex (.up ℤ)))).v (p + 1) p (by omega) =
      F.map ((CochainComplex.mappingCocone.snd (boundary T)).v
        (p + 1) p (by omega)) ≫
        (piComparison (F.mapHomologicalComplex (.up ℤ))
          (fun n ↦ T.obj (op n))).f p := by
  simpa [coneComparison, boundary, integralOperationsTowerStep, integralOperationsRoos,
    CochainComplex.mappingCocone,
    CochainComplex.mappingCocone.snd,
    CochainComplex.HomComplex.Cochain.leftShift_v, CochainComplex.mappingCone.snd,
    Category.assoc, show Int.negOnePow 2 = 1 by rfl] using!
    CategoryTheory.cs_snd F (boundary T) _
      (asIso (piComparison (F.mapHomologicalComplex (.up ℤ)) (fun n ↦ T.obj (op n))))
      (CategoryTheory.productComparison_transition F _ _) p

private theorem coneComparison_snd' (T : ℕᵒᵖ ⥤ CochainComplex A ℤ)
    (i j : ℤ) (h : i + -1 = j) :
    (coneComparison F T).hom.f i ≫
        (CochainComplex.mappingCocone.snd (boundary
          (T ⋙ F.mapHomologicalComplex (.up ℤ)))).v i j h =
      F.map ((CochainComplex.mappingCocone.snd (boundary T)).v i j h) ≫
        (piComparison (F.mapHomologicalComplex (.up ℤ))
          (fun n ↦ T.obj (op n))).f j := by
  obtain ⟨p, rfl⟩ : ∃ p : ℤ, i = p + 1 := ⟨i - 1, by omega⟩
  have hj : j = p := by omega
  cases hj
  exact coneComparison_snd F T _

private theorem roosMap_snd' {T T' : ℕᵒᵖ ⥤ CochainComplex A ℤ} (f : T ⟶ T')
    (i j : ℤ) (h : i + -1 = j) :
    (integralOperationsRoosMap f).f i ≫
        (CochainComplex.mappingCocone.snd (boundary T')).v i j h =
      (CochainComplex.mappingCocone.snd (boundary T)).v i j h ≫
        (Limits.Pi.map (fun n ↦ f.app (op n))).f j := by
  obtain ⟨p, rfl⟩ : ∃ p : ℤ, i = p + 1 := ⟨i - 1, by omega⟩
  have hj : j = p := by omega
  cases hj
  exact roosMap_snd f _

private theorem coneComparison_naturality
    {T T' : ℕᵒᵖ ⥤ CochainComplex A ℤ} (f : T ⟶ T') :
    (F.mapHomologicalComplex (.up ℤ)).map (integralOperationsRoosMap f) ≫
        (coneComparison F T').hom =
      (coneComparison F T).hom ≫
        integralOperationsRoosMap ((Functor.whiskeringRight ℕᵒᵖ _ _).obj
          (F.mapHomologicalComplex (.up ℤ)) |>.map f) := by
  let g : T ⋙ F.mapHomologicalComplex (.up ℤ) ⟶
      T' ⋙ F.mapHomologicalComplex (.up ℤ) := ((Functor.whiskeringRight ℕᵒᵖ _ _).obj
    (F.mapHomologicalComplex (.up ℤ))).map f
  let : HasCountableProducts (CochainComplex A ℤ) := ⟨fun _ ↦ inferInstance⟩
  let : HasCountableProducts (CochainComplex B ℤ) := ⟨fun _ ↦ inferInstance⟩
  ext i : 1
  obtain ⟨p, rfl⟩ : ∃ p : ℤ, i = p + 1 := ⟨i - 1, by omega⟩
  apply WeilConjectures.cocone_degree_ext
    (boundary (T' ⋙ F.mapHomologicalComplex (.up ℤ))) _ _ (p + 1)
  · simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f]
    erw [Category.assoc, coneComparison_fst F T' p,
      ← Category.assoc, ← F.map_comp, roosMap_fst f p, F.map_comp, Category.assoc]
    erw [Category.assoc, roosMap_fst g p]
    simp only [← Category.assoc]
    erw [coneComparison_fst F T p]
    simp only [Category.assoc]
    congr 1
    exact congrArg (fun z ↦ z.f (p + 1))
      (CategoryTheory.productComparison_natural
        (F.mapHomologicalComplex (.up ℤ)) (fun n ↦ f.app (op n)))
  · simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f]
    erw [Category.assoc, coneComparison_snd' F T' (p + 1) (p + 1 - 1) (by omega),
      ← Category.assoc, ← F.map_comp,
      roosMap_snd' f (p + 1) (p + 1 - 1) (by omega), F.map_comp, Category.assoc]
    erw [Category.assoc, roosMap_snd' g (p + 1) (p + 1 - 1) (by omega)]
    simp only [← Category.assoc]
    erw [coneComparison_snd' F T (p + 1) (p + 1 - 1) (by omega)]
    simp only [Category.assoc]
    congr 1
    exact congrArg (fun z ↦ z.f (p + 1 - 1))
      (CategoryTheory.productComparison_natural
        (F.mapHomologicalComplex (.up ℤ)) (fun n ↦ f.app (op n)))

private def roosComparison :
    integralOperationsRoosFunctor ⋙ F.mapHomologicalComplex (.up ℤ) ≅
      (Functor.whiskeringRight ℕᵒᵖ _ _).obj (F.mapHomologicalComplex (.up ℤ)) ⋙
        integralOperationsRoosFunctor :=
  NatIso.ofComponents (coneComparison F) (fun f ↦ coneComparison_naturality F f)

private theorem roosComparison_coordinates : RoosCoordinates F (roosComparison F) := by
  constructor
  · intro T n i
    obtain ⟨p, rfl⟩ : ∃ p : ℤ, i = p + 1 := ⟨i - 1, by omega⟩
    have h := congrArg (fun z ↦ z ≫
      (Pi.π (fun n ↦ (F.mapHomologicalComplex (.up ℤ)).obj (T.obj (op n))) n).f (p + 1))
      (coneComparison_fst F T p)
    have hπ := congrArg (fun z ↦ z.f (p + 1))
      (piComparison_comp_π (F.mapHomologicalComplex (.up ℤ))
        (fun n ↦ T.obj (op n)) n)
    dsimp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f] at hπ
    simpa only [Category.assoc, hπ, Functor.mapHomologicalComplex_map_f,
      ← F.map_comp] using! h
  · intro T n i
    have h := congrArg (fun z ↦ z ≫
      (Pi.π (fun n ↦ (F.mapHomologicalComplex (.up ℤ)).obj (T.obj (op n))) n).f (i + -1))
      (coneComparison_snd' F T i (i + -1) rfl)
    have hπ := congrArg (fun z ↦ z.f (i + -1))
      (piComparison_comp_π (F.mapHomologicalComplex (.up ℤ))
        (fun n ↦ T.obj (op n)) n)
    dsimp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f] at hπ
    simpa only [Category.assoc, hπ, Functor.mapHomologicalComplex_map_f,
      ← F.map_comp] using! h

end Comparison

attribute [local irreducible] coneComparison roosComparison pointIntegralSections

private def representativeComparison (c : roosSections.{u} l E k ≅ sectionsRoos.{u} l E k) :
    (integralOperationsGoodLocalization.{u, u} l E (Spec.{u} (.of k))) ⋙
        completedSections.{u} l E k ≅
      (integralOperationsGoodComplex.{u, u} l E (Spec.{u} (.of k))).ι ⋙
        sectionRoos.{u} l E k ⋙ moduleQ.{u} l E :=
  Functor.isoWhiskerRight
      (integralScalarExtensionComparisonOfUniverses.{u, u} l E E (AlgHom.id ℚ_[l] E)
        (Spec.{u} (.of k))) (derivedSections.{u} l E k) ≪≫
    Functor.isoWhiskerLeft
      ((integralOperationsGoodComplex.{u, u} l E (Spec.{u} (.of k))).ι ⋙
        integralScalarComplexFunctor.{u, u} l E E (AlgHom.id ℚ_[l] E) (Spec.{u} (.of k)))
      (factors.{u} l E k) ≪≫
    Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft ((integralOperationsGoodComplex.{u, u} l E (Spec.{u} (.of k))).ι ⋙
        reductions l E k) c) (moduleQ.{u} l E)

section Transport

private theorem transport_map
    {C : Type a} [Category.{v} C] {D : Type b} [Category.{w} D]
    (F : C ⥤ D) {X X' K K' : C} {Y Y' : D}
    (q : X ≅ K) (q' : X' ≅ K') (e : F.obj X ≅ Y) (e' : F.obj X' ≅ Y')
    (f : K ⟶ K') (g : X ⟶ X') (v : Y ⟶ Y')
    (hf : q.hom ≫ f = g ≫ q'.hom) (hg : F.map g ≫ e'.hom = e.hom ≫ v) :
    (F.mapIso q.symm ≪≫ e).inv ≫ F.map f ≫ (F.mapIso q'.symm ≪≫ e').hom = v := by
  simp only [Iso.trans_inv, Iso.trans_hom, Functor.mapIso_inv, Functor.mapIso_hom,
    Iso.symm_inv, Iso.symm_hom, Category.assoc]
  have hh : q.hom ≫ f ≫ q'.inv = g := by
    rw [← Category.assoc, hf, Category.assoc, q'.hom_inv_id, Category.comp_id]
  calc
    _ = e.inv ≫ F.map (q.hom ≫ f ≫ q'.inv) ≫ e'.hom := by
      simp only [Functor.map_comp, Category.assoc]
    _ = e.inv ≫ F.map g ≫ e'.hom := by rw [hh]
    _ = e.inv ≫ e.hom ≫ v := by rw [hg]
    _ = v := by simp

attribute [local irreducible] derivedSections factors

private theorem transport_unit
    {C : Type a} [Category.{v} C] {D : Type b} [Category.{w} D]
    (F : C ⥤ D) (G : C ⥤ C) (χ : 𝟭 C ⟶ G)
    {X K : C} {Y : D} (q : X ≅ K) (e : F.obj (G.obj X) ≅ Y) :
    F.map q.hom ≫ F.map (χ.app K) ≫ ((G ⋙ F).mapIso q.symm ≪≫ e).hom =
      F.map (χ.app X) ≫ e.hom := by
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Functor.comp_map]
  have hn : q.hom ≫ χ.app K = χ.app X ≫ G.map q.hom := χ.naturality q.hom
  calc
    _ = F.map (q.hom ≫ χ.app K ≫ G.map q.inv) ≫ e.hom := by
      simp only [Functor.map_comp, Category.assoc]
    _ = F.map (χ.app X ≫ G.map q.hom ≫ G.map q.inv) ≫ e.hom := by
      rw [← Category.assoc, hn, Category.assoc]
    _ = _ := by rw [← G.map_comp, q.hom_inv_id, G.map_id, Category.comp_id]

private theorem combine_unit
    {C : Type a} [Category.{v} C] {D : Type b} [Category.{w} D]
    (F : C ⥤ D) {X Y Z : C} {A B L : D}
    (α : X ⟶ Y) (β : Y ⟶ Z) (γ : X ⟶ Z)
    (δ : F.obj Z ⟶ B) (ε : F.obj X ⟶ A) (ζ : A ⟶ B) (η : B ⟶ L)
    (h : α ≫ β = γ) (h' : F.map γ ≫ δ = ε ≫ ζ) :
    F.map α ≫ (F.map β ≫ δ ≫ η) = ε ≫ ζ ≫ η := by
  rw [← Category.assoc, ← Category.assoc, ← F.map_comp, h, h', Category.assoc]

private theorem transport_unit_spec
    {C : Type a} [Category.{v} C] {D : Type b} [Category.{w} D]
    (F : C ⥤ D) (G : C ⥤ C) (χ : 𝟭 C ⟶ G)
    {X K : C} {Y : D} (q : X ≅ K) (e : F.obj (G.obj X) ≅ Y)
    (m : F.obj (G.obj K) ≅ Y) (hm : m = (G ⋙ F).mapIso q.symm ≪≫ e)
    (t : F.obj X ⟶ Y) (ht : F.map (χ.app X) ≫ e.hom = t) :
    F.map q.hom ≫ F.map (χ.app K) ≫ m.hom = t := by
  rw [hm]
  exact (transport_unit F G χ q e).trans ht

private theorem transport_map_spec
    {C : Type a} [Category.{v} C] {D : Type b} [Category.{w} D]
    (F : C ⥤ D) {X X' K K' : C} {Y Y' : D}
    (q : X ≅ K) (q' : X' ≅ K') (e : F.obj X ≅ Y) (e' : F.obj X' ≅ Y')
    (m : F.obj K ≅ Y) (m' : F.obj K' ≅ Y')
    (hm : m = F.mapIso q.symm ≪≫ e) (hm' : m' = F.mapIso q'.symm ≪≫ e')
    (f : K ⟶ K') (g : X ⟶ X') (v : Y ⟶ Y')
    (hf : q.hom ≫ f = g ≫ q'.hom) (hg : F.map g ≫ e'.hom = e.hom ≫ v) :
    m.inv ≫ F.map f ≫ m'.hom = v := by
  rw [hm, hm']
  exact transport_map F q q' e e' f g v hf hg

private theorem transport_roof
    {C : Type a} [Category.{v} C] {D : Type b} [Category.{w} D]
    (F : C ⥤ D) {X X' R K K' : C} {Y Y' Z : D}
    (q : X ≅ K) (q' : X' ≅ K') (e : F.obj X ≅ Y) (e' : F.obj X' ≅ Y')
    (eR : F.obj R ≅ Z) (f : K ⟶ K') (s : R ⟶ X) (v : R ⟶ X')
    (a : Z ⟶ Y) (b : Z ⟶ Y')
    (hf : s ≫ q.hom ≫ f = v ≫ q'.hom)
    (hs : F.map s ≫ e.hom = eR.hom ≫ a)
    (hv : F.map v ≫ e'.hom = eR.hom ≫ b) :
    a ≫ (F.mapIso q.symm ≪≫ e).inv ≫ F.map f ≫
      (F.mapIso q'.symm ≪≫ e').hom = b := by
  apply (cancel_epi eR.hom).1
  simp only [Iso.trans_inv, Iso.trans_hom, Functor.mapIso_inv, Functor.mapIso_hom,
    Iso.symm_inv, Iso.symm_hom, ← Category.assoc]
  rw [← hs]
  simp only [Category.assoc, Iso.hom_inv_id, Category.id_comp]
  have hh : s ≫ q.hom ≫ f ≫ q'.inv = v := by
    apply (cancel_mono q'.hom).1
    simpa only [Category.assoc, q'.inv_hom_id, Category.comp_id] using hf
  calc
    _ = F.map (s ≫ q.hom ≫ f ≫ q'.inv) ≫ e'.hom := by
      simp only [Functor.map_comp, Category.assoc]
    _ = _ := by rw [hh, hv]

private theorem transport_roof_spec
    {C : Type a} [Category.{v} C] {D : Type b} [Category.{w} D]
    (F : C ⥤ D) {X X' R K K' : C} {Y Y' Z : D}
    (q : X ≅ K) (q' : X' ≅ K') (e : F.obj X ≅ Y) (e' : F.obj X' ≅ Y')
    (eR : F.obj R ≅ Z) (m : F.obj K ≅ Y) (m' : F.obj K' ≅ Y')
    (hm : m = F.mapIso q.symm ≪≫ e) (hm' : m' = F.mapIso q'.symm ≪≫ e')
    (f : K ⟶ K') (s : R ⟶ X) (v : R ⟶ X') (a : Z ⟶ Y) (b : Z ⟶ Y')
    (hf : s ≫ q.hom ≫ f = v ≫ q'.hom)
    (hs : F.map s ≫ e.hom = eR.hom ≫ a)
    (hv : F.map v ≫ e'.hom = eR.hom ≫ b) :
    a ≫ m.inv ≫ F.map f ≫ m'.hom = b := by
  rw [hm, hm']
  exact transport_roof F q q' e e' eR f s v a b hf hs hv

private theorem model_eq (c : roosSections l E k ≅ sectionsRoos l E k)
    (K₀ : DerivedCategory (integralTowerModules.{u, u} l E (Spec.{u} (.of k))))
    (P₀ : (integralOperationsGoodComplex.{u, u} l E (Spec.{u} (.of k))).FullSubcategory)
    (q₀ : DerivedCategory.Q.obj P₀.obj ≅ K₀) :
    model l E k c K₀ P₀ q₀ =
      (completedSections l E k).mapIso q₀.symm ≪≫
        (representativeComparison l E k c).app P₀ := by
  rfl

attribute [local irreducible] representativeComparison model

private theorem model_naturality (c : roosSections.{u} l E k ≅ sectionsRoos.{u} l E k)
    {K K' : DerivedCategory.{u + 2} (integralTowerModules.{u, u} l E (Spec.{u} (.of k)))}
    (f : K ⟶ K')
    (P P' : (integralOperationsGoodComplex.{u, u} l E (Spec.{u} (.of k))).FullSubcategory)
    (q : DerivedCategory.Q.{u + 2, u + 1, u + 2}.obj P.obj ≅ K)
    (q' : DerivedCategory.Q.{u + 2, u + 1, u + 2}.obj P'.obj ≅ K')
    (v : P.obj ⟶ P'.obj) (hv : q.hom ≫ f = DerivedCategory.Q.{u + 2, u + 1, u + 2}.map v ≫ q'.hom) :
    (model.{u} l E k c K P q).inv ≫ (completedSections.{u} l E k).map f ≫
        (model.{u} l E k c K' P' q').hom =
      (moduleQ.{u} l E).map ((sectionRoos.{u} l E k).map v) := by
  let e := representativeComparison l E k c
  have hn := e.hom.naturality (ObjectProperty.homMk v)
  exact transport_map_spec (completedSections l E k) q q' (e.app P) (e.app P')
    (model l E k c K P q) (model l E k c K' P' q')
    (model_eq l E k c K P q) (model_eq l E k c K' P' q') f
    (DerivedCategory.Q.map v) ((moduleQ l E).map ((sectionRoos l E k).map v)) hv hn

private theorem model_roof (c : roosSections l E k ≅ sectionsRoos l E k)
    {K K' : DerivedCategory (integralTowerModules.{u, u} l E (Spec.{u} (.of k)))}
    (f : K ⟶ K')
    (P P' R : (integralOperationsGoodComplex.{u, u} l E (Spec.{u} (.of k))).FullSubcategory)
    (q : DerivedCategory.Q.obj P.obj ≅ K) (q' : DerivedCategory.Q.obj P'.obj ≅ K')
    (s : R.obj ⟶ P.obj) (v : R.obj ⟶ P'.obj)
    (hf : DerivedCategory.Q.map s ≫ q.hom ≫ f = DerivedCategory.Q.map v ≫ q'.hom) :
    (moduleQ l E).map ((sectionRoos l E k).map s) ≫
      (model l E k c K P q).inv ≫ (completedSections l E k).map f ≫
        (model l E k c K' P' q').hom =
      (moduleQ l E).map ((sectionRoos l E k).map v) := by
  let e := representativeComparison l E k c
  exact transport_roof_spec (completedSections l E k) q q' (e.app P) (e.app P')
    (e.app R) (model l E k c K P q) (model l E k c K' P' q')
    (model_eq l E k c K P q) (model_eq l E k c K' P' q') f
    (DerivedCategory.Q.map s) (DerivedCategory.Q.map v)
    ((moduleQ l E).map ((sectionRoos l E k).map s))
    ((moduleQ l E).map ((sectionRoos l E k).map v)) hf
    (e.hom.naturality (ObjectProperty.homMk s))
    (e.hom.naturality (ObjectProperty.homMk v))

end Transport

omit [IsAlgClosed k] in
private theorem completion_unit :
    ∃ χ : 𝟭 _ ⟶ completion.{u} l E k,
      ∀ P : (integralOperationsGoodComplex.{u, u} l E (Spec.{u} (.of k))).FullSubcategory,
        χ.app (DerivedCategory.Q.{u + 2, u + 1, u + 2}.obj P.obj) ≫
          (integralScalarExtensionComparisonOfUniverses.{u, u} l E E (AlgHom.id ℚ_[l] E)
            (Spec.{u} (.of k))).hom.app P =
          DerivedCategory.Q.{u + 2, u + 1, u + 2}.map
            ((completedScalarIdentityUnit.{u, u} l E (Spec.{u} (.of k))).app P.obj) := by
  let Λ := integralOperationsGoodLocalization.{u, u} l E (Spec.{u} (.of k))
  let W := (HomologicalComplex.quasiIso (integralTowerModules.{u, u} l E (Spec.{u} (.of k)))
    (.up ℤ)).inverseImage (integralOperationsGoodComplex.{u, u} l E (Spec.{u} (.of k))).ι
  let : Λ.IsLocalization W := integralOperationsGoodLocalization_isLocalization.{u, u} l E _
  exact (localization_descent_with_comparison Λ W (𝟭 _) (completion.{u} l E k) _
    (integralScalarExtensionComparisonOfUniverses.{u, u} l E E (AlgHom.id ℚ_[l] E)
      (Spec.{u} (.of k)))
    (Functor.whiskerLeft (integralOperationsGoodComplex.{u, u} l E (Spec.{u} (.of k))).ι
      (Functor.whiskerRight (completedScalarIdentityUnit.{u, u} l E (Spec.{u} (.of k)))
        DerivedCategory.Q.{u + 2, u + 1, u + 2}))).exists

omit [IsAlgClosed k] in
private theorem augmentation_naturality
    (c : roosSections.{u} l E k ≅ sectionsRoos.{u} l E k)
    {P P' : CochainComplex (integralTowerModules.{u, u} l E (Spec.{u} (.of k))) ℤ}
    (v : P ⟶ P') :
    (sections.{u} l E k).map v ≫ augmentation.{u} l E k c P' =
      augmentation.{u} l E k c P ≫ (sectionRoos.{u} l E k).map v := by
  dsimp only [augmentation, sectionRoos, Functor.comp_map]
  erw [← Category.assoc, ← Functor.map_comp,
    show v ≫ (completedScalarIdentityUnit l E (Spec.{u} (.of k))).app P' =
      (completedScalarIdentityUnit l E (Spec.{u} (.of k))).app P ≫
        (integralScalarComplexFunctor.{u, u} l E E (AlgHom.id ℚ_[l] E)
          (Spec.{u} (.of k))).map v from
      (completedScalarIdentityUnit l E (Spec.{u} (.of k))).naturality v,
    Functor.map_comp, Category.assoc]
  exact congrArg ((sections.{u} l E k).map
    ((completedScalarIdentityUnit l E (Spec.{u} (.of k))).app P) ≫ ·)
    (c.hom.naturality ((reductions l E k).map v))

private theorem sectionRoos_quasiIso
    (c : roosSections.{u} l E k ≅ sectionsRoos.{u} l E k)
    (P P' : (integralOperationsGoodComplex.{u, u} l E (Spec.{u} (.of k))).FullSubcategory)
    (v : P.obj ⟶ P'.obj) (hv : QuasiIso v) :
    QuasiIso ((sectionRoos.{u} l E k).map v) := by
  have : QuasiIso ((integralScalarComplexFunctor.{u, u} l E E (AlgHom.id ℚ_[l] E)
      (Spec.{u} (.of k))).map v) :=
    ((integralScalarExtensionWellDefined.{u, u} l E E (AlgHom.id ℚ_[l] E)
      (Spec.{u} (.of k))).1 P P' v hv).2
  have : QuasiIso ((sections.{u} l E k).map
      ((integralScalarComplexFunctor.{u, u} l E E (AlgHom.id ℚ_[l] E)
        (Spec.{u} (.of k))).map v)) := inferInstance
  have hq : QuasiIso ((roosSections l E k).map ((reductions l E k).map v)) :=
    ‹QuasiIso ((sections l E k).map
      ((integralScalarComplexFunctor.{u, u} l E E (AlgHom.id ℚ_[l] E)
        (Spec.{u} (.of k))).map v))›
  have hn := c.hom.naturality ((reductions l E k).map v)
  have : QuasiIso (c.hom.app ((reductions l E k).obj P.obj) ≫
      (sectionRoos.{u} l E k).map v) := by
    erw [← hn]
    infer_instance
  exact quasiIso_of_comp_left
    (c.hom.app ((reductions l E k).obj P.obj)) _

private theorem module_roos_limit
    (R : Type a) [Ring R] (C : ℕᵒᵖ ⥤ CochainComplex (ModuleCat.{a} R) ℤ) :
    ∃ hprod : HasProduct (fun n ↦
      (@DerivedCategory.Q (ModuleCat.{a} R) _ _
        (HasDerivedCategory.ofIsGrothendieckAbelian _)).obj (C.obj (op n))),
      @IsDerivedLimit _ _ _ _ _ _ _ _ hprod
        (fun n ↦ (@DerivedCategory.Q (ModuleCat.{a} R) _ _
          (HasDerivedCategory.ofIsGrothendieckAbelian _)).map (integralOperationsTowerStep C n))
        ((@DerivedCategory.Q (ModuleCat.{a} R) _ _
          (HasDerivedCategory.ofIsGrothendieckAbelian _)).obj (integralOperationsRoos C)) := by
  let A := ModuleCat.{a} R
  let hD : HasDerivedCategory.{a} A := HasDerivedCategory.ofIsGrothendieckAbelian A
  obtain ⟨hP, _⟩ := @derivedCategory_countableProducts_core.{0, a, a, a + 1}
    A _ _ hD _ _
  let := hP
  exact ⟨inferInstance, @roos_derivedLimit.{a + 1, a, a} A _ _ _ hD _ hP C⟩

omit [IsAlgClosed k] in
private theorem sectionRoos_limit
    (P : (integralOperationsGoodComplex.{u, u} l E (Spec.{u} (.of k))).FullSubcategory) :
    ∃ hprod : HasProduct
      (fun n : ℕ ↦ (moduleQ.{u} l E).obj
        (((reductions l E k).obj P.obj ⋙ sections.{u} l E k).obj (op n))),
      @IsDerivedLimit _ _ _ _ _ _ _ _ hprod
        (fun n ↦ (moduleQ.{u} l E).map
          (((reductions l E k).obj P.obj ⋙ sections.{u} l E k).map
            (homOfLE (Nat.le_succ n)).op))
        ((moduleQ.{u} l E).obj ((sectionRoos.{u} l E k).obj P.obj)) := by
  exact module_roos_limit (ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E))
    ((reductions l E k).obj P.obj ⋙ sections l E k)

section UnitModel
attribute [local irreducible] derivedSections factors

private theorem unit_model
    (c : roosSections l E k ≅ sectionsRoos l E k)
    (χ : 𝟭 _ ⟶ completion l E k)
    (hχ : ∀ P : (integralOperationsGoodComplex.{u, u} l E (Spec.{u} (.of k))).FullSubcategory,
      χ.app (DerivedCategory.Q.obj P.obj) ≫
        (integralScalarExtensionComparisonOfUniverses.{u, u} l E E (AlgHom.id ℚ_[l] E)
          (Spec.{u} (.of k))).hom.app P =
        DerivedCategory.Q.map
          ((completedScalarIdentityUnit.{u, u} l E (Spec.{u} (.of k))).app P.obj))
    (K : DerivedCategory (integralTowerModules.{u, u} l E (Spec.{u} (.of k))))
    (P : (integralOperationsGoodComplex.{u, u} l E (Spec.{u} (.of k))).FullSubcategory)
    (q : DerivedCategory.Q.obj P.obj ≅ K) :
    (derivedSections l E k).map q.hom ≫ (derivedSections l E k).map (χ.app K) ≫
      (model l E k c K P q).hom =
      (factors l E k).hom.app P.obj ≫ (moduleQ l E).map (augmentation l E k c P.obj) := by
  refine transport_unit_spec (derivedSections l E k) (completion l E k) χ q
    ((representativeComparison l E k c).app P) (model l E k c K P q)
    (model_eq l E k c K P q) _ ?_
  have hn := (factors l E k).hom.naturality
    ((completedScalarIdentityUnit l E (Spec.{u} (.of k))).app P.obj)
  have hc := combine_unit (derivedSections l E k) (χ.app (DerivedCategory.Q.obj P.obj))
    ((integralScalarExtensionComparisonOfUniverses.{u, u} l E E (AlgHom.id ℚ_[l] E)
      (Spec.{u} (.of k))).hom.app P)
    (DerivedCategory.Q.map
      ((completedScalarIdentityUnit l E (Spec.{u} (.of k))).app P.obj))
    ((factors l E k).hom.app
      ((integralScalarComplexFunctor.{u, u} l E E (AlgHom.id ℚ_[l] E)
        (Spec.{u} (.of k))).obj P.obj))
    ((factors l E k).hom.app P.obj)
    ((moduleQ l E).map ((sections l E k).map
      ((completedScalarIdentityUnit l E (Spec.{u} (.of k))).app P.obj)))
    ((moduleQ l E).map (c.hom.app ((reductions l E k).obj P.obj))) (hχ P) hn
  exact hc.trans (congrArg ((factors l E k).hom.app P.obj ≫ ·)
    ((moduleQ l E).map_comp
      ((sections l E k).map
        ((completedScalarIdentityUnit l E (Spec.{u} (.of k))).app P.obj))
      (c.hom.app ((reductions l E k).obj P.obj))).symm)

end UnitModel

end Proof

attribute [local irreducible] derivedSections factors representativeComparison model

/-- Whole-cone normalization, localization, and naturality for the complete quotient tower.
Source: blueprint main-20261015, prop-trf-rational-frobenius-integral-model, clause (3);
Stacks 0941, lemma-derived-limit-is-ok
(blueprint: lem-trf-point-quotient-augmentation-diagram).

Proof (the six node steps):
1. Sections and restriction of scalars preserve countable products. The generic cone
   and shift comparisons of lem-cbc-exact-product-functor-roos-chain-maps give a
   natural comparison c of Roos cocones whose two shifted coordinates are the product
   comparisons; naturality follows from their joint monicity.
2. The augmentation is the existing completedScalarIdentityUnit followed by sections
   and c; it is natural as a composite of natural maps. Integral scalar extension
   preserves quasi-isomorphisms of good complexes
   (lem-weil-integral-scalar-extension-well-defined), exact sections preserve them
   (lem-weil-point-proetale-sections-exact), and conjugation by c keeps this.
3. Whiskering the specified scalar-extension comparison by derived sections, then the
   factors isomorphism and the localized c, gives the representative comparison;
   model is its transport along q.
4. The good-complex inclusion followed by Q is a localization; descending the
   localized chain unit along it (lem-weil-pbc-localization-universal-property)
   gives χ with the representative normalization, and naturality of χ and of
   factors gives the whole augmentation equation.
5. Naturality of the representative comparison, transported along q and q', gives
   the chain-map formula; applied to both legs it gives the roof formula.
6. The generic roos_derivedLimit theorem (lem-pur-integral-operations-well-defined)
   with derived countable products of module complexes
   (lem-weil-derived-limit-products-core) makes the section Roos cone a derived limit
   of the entire tower. No completeness or boundedness is assumed. -/
theorem pointQuotientAugmentationDiagram (_hl : IsUnit (l : k)) :
    ∃ c : roosSections l E k ≅ sectionsRoos l E k,
      RoosCoordinates (pointIntegralSections l E k) c ∧
      (∀ (P P' : (integralOperationsGoodComplex l E (Spec (.of k))).FullSubcategory)
        (v : P.obj ⟶ P'.obj),
        (sections l E k).map v ≫ augmentation l E k c P'.obj =
          augmentation l E k c P.obj ≫ (sectionRoos l E k).map v) ∧
      (∀ (P P' : (integralOperationsGoodComplex l E (Spec (.of k))).FullSubcategory)
        (v : P.obj ⟶ P'.obj), QuasiIso v → QuasiIso ((sectionRoos l E k).map v)) ∧
      (∃ e : ((integralOperationsGoodComplex l E (Spec (.of k))).ι ⋙ DerivedCategory.Q) ⋙
          completedSections l E k ≅
          (integralOperationsGoodComplex l E (Spec (.of k))).ι ⋙
            sectionRoos l E k ⋙ moduleQ l E,
        ∀ P : (integralOperationsGoodComplex l E (Spec (.of k))).FullSubcategory,
          e.app P = model l E k c (DerivedCategory.Q.obj P.obj) P (Iso.refl _)) ∧
      ∃ χ : 𝟭 _ ⟶ completion l E k,
        (∀ P : (integralOperationsGoodComplex l E (Spec (.of k))).FullSubcategory,
          χ.app (DerivedCategory.Q.obj P.obj) ≫
            (integralScalarExtensionComparisonOfUniverses l E E (AlgHom.id ℚ_[l] E)
              (Spec (.of k))).hom.app P =
            DerivedCategory.Q.map ((completedScalarIdentityUnit l E (Spec (.of k))).app P.obj)) ∧
        (∀ (K : DerivedCategory (integralTowerModules l E (Spec (.of k))))
          (P : (integralOperationsGoodComplex l E (Spec (.of k))).FullSubcategory)
          (q : DerivedCategory.Q.obj P.obj ≅ K),
          (derivedSections l E k).map q.hom ≫
            (derivedSections l E k).map (χ.app K) ≫ (model l E k c K P q).hom =
            (factors l E k).hom.app P.obj ≫
              (moduleQ l E).map (augmentation l E k c P.obj)) ∧
        (∀ (K K' : DerivedCategory (integralTowerModules l E (Spec (.of k)))) (f : K ⟶ K')
          (P P' : (integralOperationsGoodComplex l E (Spec (.of k))).FullSubcategory)
          (q : DerivedCategory.Q.obj P.obj ≅ K) (q' : DerivedCategory.Q.obj P'.obj ≅ K')
          (v : P.obj ⟶ P'.obj),
          q.hom ≫ f = DerivedCategory.Q.map v ≫ q'.hom →
          (model l E k c K P q).inv ≫ (completedSections l E k).map f ≫
            (model l E k c K' P' q').hom =
            (moduleQ l E).map ((sectionRoos l E k).map v)) ∧
        (∀ (K K' : DerivedCategory (integralTowerModules l E (Spec (.of k)))) (f : K ⟶ K')
          (P P' R : (integralOperationsGoodComplex l E (Spec (.of k))).FullSubcategory)
          (q : DerivedCategory.Q.obj P.obj ≅ K) (q' : DerivedCategory.Q.obj P'.obj ≅ K')
          (s : R.obj ⟶ P.obj) (v : R.obj ⟶ P'.obj), QuasiIso s →
          DerivedCategory.Q.map s ≫ q.hom ≫ f = DerivedCategory.Q.map v ≫ q'.hom →
          (moduleQ l E).map ((sectionRoos l E k).map s) ≫
            (model l E k c K P q).inv ≫ (completedSections l E k).map f ≫
              (model l E k c K' P' q').hom =
            (moduleQ l E).map ((sectionRoos l E k).map v)) ∧
        (∀ P : (integralOperationsGoodComplex l E (Spec (.of k))).FullSubcategory,
          ∃ hprod : HasProduct
            (fun n : ℕ ↦ (moduleQ l E).obj
              (((reductions l E k).obj P.obj ⋙ sections l E k).obj (op n))),
          @IsDerivedLimit _ _ _ _ _ _ _ _ hprod
            (fun n ↦ (moduleQ l E).map
              (((reductions l E k).obj P.obj ⋙ sections l E k).map
                (homOfLE (Nat.le_succ n)).op))
            ((moduleQ l E).obj ((sectionRoos l E k).obj P.obj))) := by
  let : PreservesLimitsOfShape (Discrete ℕ) (pointIntegralSections l E k) :=
    sectionsProducts l E k
  let c : roosSections l E k ≅ sectionsRoos l E k :=
    roosComparison (pointIntegralSections l E k)
  refine ⟨c, roosComparison_coordinates _, ?_, ?_, ?_, ?_⟩
  · exact fun P P' v ↦ augmentation_naturality l E k c v
  · exact sectionRoos_quasiIso l E k c
  · refine ⟨representativeComparison l E k c, ?_⟩
    intro P
    exact (model_eq l E k c _ P (Iso.refl _)).trans (by
      rw [Iso.refl_symm, Functor.mapIso_refl, Iso.refl_trans]) |>.symm
  · obtain ⟨χ, hχ⟩ := completion_unit l E k
    refine ⟨χ, hχ, unit_model l E k c χ hχ, ?_, ?_, sectionRoos_limit l E k⟩
    · exact fun K K' f P P' q q' v hv ↦ model_naturality l E k c f P P' q q' v hv
    · exact fun K K' f P P' R q q' s v _hs hv ↦ model_roof l E k c f P P' R q q' s v hv


end WeilConjectures.PointQuotientAugmentation
