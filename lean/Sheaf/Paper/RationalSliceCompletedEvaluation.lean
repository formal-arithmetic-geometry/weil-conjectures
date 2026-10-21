/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q138
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Sheaf.Paper.CompletedIntegralConstantMapOfUniverses
public import Sheaf.Paper.IntegralDerivedOperationsOnSlices
public import Sheaf.Paper.SfIntegralConstructible
public import Sheaf.AlgebraicGeometry.ProEtaleCohomologicalSupport
public import Sheaf.Paper.IntrinsicFiniteTorsionConstructibility
public import Sheaf.Paper.SfDerivedComplete
public import Sheaf.Paper.DerivedCompleteOnSlices
public import Sheaf.CategoryTheory.ScalarLocalization
public import Sheaf.NumberTheory.Padics.IntegersLocalizationUniformizer
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
public import Sheaf.Paper.RationalThickEvaluation
public import Sheaf.Algebra.Homology.RingedSliceEvaluationTranspose

import Sheaf.CategoryTheory.LocalizedModuleExactIndependent
import Sheaf.CategoryTheory.DerivedCategory.AdjointFunctors
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
import Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimitExistence
import Sheaf.Paper.IntegralOperationsWellDefined
import Sheaf.Algebra.Homology.RingedInternalHomExactRestriction
import Sheaf.NumberTheory.Padics.ExtensionIntegersDvr
import Sheaf.Paper.CompletedConstantSheafReduction
import Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitOfUniverses
import Sheaf.CategoryTheory.RingedCechKoszulDualLimit
import Sheaf.Paper.ExtendedCechCompletionModel
import Sheaf.Algebra.Homology.WeilSiteDerivedTensorDescent
import Sheaf.Algebra.Homology.RingedInternalHomShiftOfUniverses
import Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
import Sheaf.CategoryTheory.LocalizedModuleExactForSystems
import Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients

/-!
# Restriction of completed integral operations and rational evaluation

Source: main-20261015 blueprint, sec-six-functors/sk-prop-sf-dualizable-biduality,
termwise comparison and coefficient unit; Stacks Tags 03DJ, 08JB, 08TC, 099F
(blueprint: lem-sf-rational-slice-completed-evaluation).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u
open CategoryTheory CategoryTheory.Limits Opposite
namespace WeilConjectures.IntegralOnSlice

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (X : AlgebraicGeometry.Scheme.{t})

/-- An index for direct restriction or relocalization; none denotes the ambient site.
Source: Stacks 03EH (blueprint: lem-sf-rational-slice-completed-evaluation). -/
def RestrictionArrow (U V : Option X.ProEt) : Type t :=
  match U, V with
  | none, _ => PUnit
  | some _, none => PEmpty
  | some A, some B => B ⟶ A

/-- The actual functor forgetting a structural arrow (or composing it).
Source: Stacks 03EH (blueprint: lem-sf-rational-slice-completed-evaluation). -/
def restrictionSite {U V : Option X.ProEt} (a : RestrictionArrow X U V) :
    Site X V ⥤ Site X U :=
  match U, V, a with
  | none, none, _ => 𝟭 _
  | none, some B, _ => Over.forget B
  | some _, none, a => PEmpty.elim a
  | some _, some _, a => Over.map a

/-- The module functor is Mathlib's sectionwise restriction with its original ring action.
Source: Stacks 03DH (blueprint: lem-sf-rational-slice-completed-evaluation). -/
def restrictionModules {U V : Option X.ProEt} (a : RestrictionArrow X U V) :
    Mod l E X U ⥤ Mod l E X V :=
  match U, V, a with
  | none, none, _ => 𝟭 _
  | none, some B, _ => SheafOfModules.overFunctor (rings l E X none) B
  | some _, none, a => PEmpty.elim a
  | some _, some _, a => SheafOfModules.overMap (rings l E X none) a

/-- Sectionwise restriction is additive and exact, including relocalization.
Source: Stacks 03DJ (blueprint: lem-sf-rational-slice-completed-evaluation).
Proof: restriction preserves kernels and products sectionwise. Coverings of an object
of an over-site are exactly coverings of its domain with the same structural arrow;
hence local lifts of cokernel sections restrict, proving preservation of cokernels.
Addition is sectionwise. The same argument applies to Over.map and the identity. -/
theorem restrictionModules_exact {U V : Option X.ProEt} (a : RestrictionArrow X U V) :
    (restrictionModules l E X a).Additive ∧
      PreservesFiniteLimits (restrictionModules l E X a) ∧
      PreservesFiniteColimits (restrictionModules l E X a) := by
  sorry

/-- The additive structure supplied by exact sectionwise restriction.
Source: Stacks 03DJ (blueprint: lem-sf-rational-slice-completed-evaluation). -/
instance restrictionModulesAdditive {U V : Option X.ProEt} (a : RestrictionArrow X U V) :
    (restrictionModules l E X a).Additive := (restrictionModules_exact l E X a).1

/-- The finite-limit structure supplied by exact sectionwise restriction.
Source: Stacks 03DJ (blueprint: lem-sf-rational-slice-completed-evaluation). -/
instance restrictionModulesLimits {U V : Option X.ProEt} (a : RestrictionArrow X U V) :
    PreservesFiniteLimits (restrictionModules l E X a) :=
  (restrictionModules_exact l E X a).2.1

/-- The finite-colimit structure supplied by exact sectionwise restriction.
Source: Stacks 03DJ (blueprint: lem-sf-rational-slice-completed-evaluation). -/
instance restrictionModulesColimits {U V : Option X.ProEt} (a : RestrictionArrow X U V) :
    PreservesFiniteColimits (restrictionModules l E X a) :=
  (restrictionModules_exact l E X a).2.2

/-- Restrict the actual complexes term by term.
Source: Stacks 03DJ (blueprint: lem-sf-rational-slice-completed-evaluation). -/
def restrictionComplex {U V : Option X.ProEt} (a : RestrictionArrow X U V) :
    Cx l E X U ⥤ Cx l E X V :=
  (restrictionModules l E X a).mapHomologicalComplex (.up ℤ)

/-- The functor induced by this exact restriction on the existing derived categories.
Source: Stacks 03DJ (blueprint: lem-sf-rational-slice-completed-evaluation). -/
def restrictionDerived {U V : Option X.ProEt} (a : RestrictionArrow X U V) :
    D l E X U ⥤ D l E X V := (restrictionModules l E X a).mapDerivedCategory

/-- The termwise additive functor remains additive after quasi-isomorphism localization.
Source: Stacks 03DJ (blueprint: lem-sf-rational-slice-completed-evaluation).
Proof: termwise restriction preserves sums of chain maps. The additive localization
universal property descends this identity, equivalently use the derived adjunction
with exact extension by zero. Thus the induced derived functor preserves addition. -/
theorem restrictionDerived_additive {U V : Option X.ProEt} (a : RestrictionArrow X U V) :
    (restrictionDerived l E X a).Additive := by
  sorry

/-- The additive structure from termwise restriction and additive localization.
Source: Stacks 03DJ (blueprint: lem-sf-rational-slice-completed-evaluation). -/
instance restrictionDerivedAdditive {U V : Option X.ProEt} (a : RestrictionArrow X U V) :
    (restrictionDerived l E X a).Additive := restrictionDerived_additive l E X a

/-- Its fixed localization comparison, used in all representative normalizations.
Source: Stacks 03DJ (blueprint: lem-sf-rational-slice-completed-evaluation). -/
def restrictionLocalization {U V : Option X.ProEt} (a : RestrictionArrow X U V) :
    DerivedCategory.Q ⋙ restrictionDerived l E X a ≅
      restrictionComplex l E X a ⋙ DerivedCategory.Q :=
  (restrictionModules l E X a).mapDerivedCategoryFactors


/-- The identity on underlying sections, retaining their original module action.
Source: Stacks 03DH (blueprint: lem-sf-rational-slice-completed-evaluation). -/
def restrictionSection {U V : Option X.ProEt} (a : RestrictionArrow X U V)
    (M : Mod l E X U) (W : (Site X V)ᵒᵖ) :
    M.val.obj ((restrictionSite X a).op.obj W) ≃+
      ((restrictionModules l E X a).obj M).val.obj W :=
  match U, V, a, M, W with
  | none, none, _, _, _ => AddEquiv.refl _
  | none, some _, _, _, _ => AddEquiv.refl _
  | some _, none, a, _, _ => PEmpty.elim a
  | some _, some _, _, _, _ => AddEquiv.refl _

/-- The identity on the restricted finite-coefficient sections.
Source: Stacks 03DH (blueprint: lem-sf-rational-slice-completed-evaluation). -/
def restrictionFiniteSection {U V : Option X.ProEt} (a : RestrictionArrow X U V)
    (n : ℕ) (W : (Site X V)ᵒᵖ) :
    (finite l E X U n).obj.obj ((restrictionSite X a).op.obj W) ≃+*
      (finite l E X V n).obj.obj W :=
  match U, V, a, W with
  | none, none, _, _ => RingEquiv.refl _
  | none, some _, _, _ => RingEquiv.refl _
  | some _, none, a, _ => PEmpty.elim a
  | some _, some _, _, _ => RingEquiv.refl _

/-- The fixed 1-s endomorphism defining the actual quotient Roos complex.
Source: Stacks 08TC (blueprint: lem-sf-rational-slice-completed-evaluation). -/
def restrictionRoosStep (U : Option X.ProEt) (P : Cx l E X U) :=
  towerTransitionEndomorphism
    (K := fun n : ℕ ↦ ((tower l E X U).obj P).obj (op n))
    (integralOperationsTowerStep ((tower l E X U).obj P))

/-- Comparison data for the actual restriction functor. The generator and two
cone-coordinate equations fix the reduction and Roos comparisons, not just their
isomorphism classes. Completed tensor is tied to these comparisons and ordinary tensor.
Source: Stacks 03DJ, 08JB, 08TC; Bhatt--Scholze 3.4.10
(blueprint: lem-sf-rational-slice-completed-evaluation). -/
structure CompletedRestrictionComparisons {U V : Option X.ProEt}
    (a : RestrictionArrow X U V) where
  /-- Restriction of a flat-term K-flat representative is again such a representative. -/
  good : ∀ P : Cx l E X U, Good l E X U P →
    Good l E X V ((restrictionComplex l E X a).obj P)
  /-- Derived reduction computed on these representatives; scalars are restored by pi_n. -/
  reductionIso : ∀ n : ℕ, level l E X U n ⋙ restrictionComplex l E X a ≅
    restrictionComplex l E X a ⋙ level l E X V n
  /-- Products are compared using their restricted projections. -/
  productIso : ∀ P : Cx l E X U,
    (restrictionComplex l E X a).obj
      (∏ᶜ fun n : ℕ ↦ ((tower l E X U).obj P).obj (op n)) ≅
        ∏ᶜ fun n : ℕ ↦ ((tower l E X V).obj
          ((restrictionComplex l E X a).obj P)).obj (op n)
  /-- The comparison of the specified shifted cones, natural in the input complex. -/
  roosIso : roos l E X U ⋙ restrictionComplex l E X a ≅
    restrictionComplex l E X a ⋙ roos l E X V
  /-- Completion comparison, natural on the actual derived category. -/
  completionIso : completion l E X U ⋙ restrictionDerived l E X a ≅
    restrictionDerived l E X a ⋙ completion l E X V
  /-- Ordinary tensor comparison, used to identify the completed tensor. -/
  ordinaryTensorIso : (duality l E X U).closed.tensor ⋙ restrictionDerived l E X a ≅
    ((restrictionDerived l E X a).prod (restrictionDerived l E X a)) ⋙
      (duality l E X V).closed.tensor
  /-- Completed tensor comparison. -/
  tensorIso : completedTensor l E X U ⋙ restrictionDerived l E X a ≅
    ((restrictionDerived l E X a).prod (restrictionDerived l E X a)) ⋙
      completedTensor l E X V
  /-- Internal Hom is the ordinary ambient ringed-site derived internal Hom. -/
  homIso : hom l E X U ⋙ restrictionDerived l E X a ≅
    ((restrictionDerived l E X a).op.prod (restrictionDerived l E X a)) ⋙ hom l E X V
  /-- The coefficient object carries its unchanged restricted coefficient action. -/
  coefficientIso : (restrictionDerived l E X a).obj (coefficient l E X U) ≅
    coefficient l E X V

/-- Its actual formula is s tensor x mapped to the same restricted s tensor x. Source: Stacks
03DJ, 08JB, 08TC
(blueprint: lem-sf-rational-slice-completed-evaluation). -/
def CompletedRestrictionComparisons.reduction_generator
    {U V : Option X.ProEt} {a : RestrictionArrow X U V}
    (d : CompletedRestrictionComparisons l E X a) : Prop :=
  ∀ (P : Cx l E X U) (n : ℕ) (i : ℤ)
  (W : (Site X V)ᵒᵖ)
  (s : (finite l E X U n).obj.obj ((restrictionSite X a).op.obj W))
  (x : (P.X i).val.obj ((restrictionSite X a).op.obj W)),
  (((d.reductionIso n).hom.app P).f i).val.app W
    (restrictionSection l E X a (((level l E X U n).obj P).X i) W
      (generator l E X U n (P.X i) ((restrictionSite X a).op.obj W) s x)) =
    generator l E X V n (((restrictionComplex l E X a).obj P).X i) W
      (restrictionFiniteSection l E X a n W s) (restrictionSection l E X a (P.X i) W x)

/-- Compatibility with the actual quotient transitions. Source: Stacks 03DJ, 08JB, 08TC
(blueprint: lem-sf-rational-slice-completed-evaluation). -/
def CompletedRestrictionComparisons.reduction_transition
    {U V : Option X.ProEt} {a : RestrictionArrow X U V}
    (d : CompletedRestrictionComparisons l E X a) : Prop :=
  ∀ (P : Cx l E X U) (n : ℕ),
  (restrictionComplex l E X a).map ((transition l E X U n).app P) ≫
      (d.reductionIso n).hom.app P =
    (d.reductionIso (n + 1)).hom.app P ≫
      (transition l E X V n).app ((restrictionComplex l E X a).obj P)

/-- Compatibility with the canonical reduction units. Source: Stacks 03DJ, 08JB, 08TC
(blueprint: lem-sf-rational-slice-completed-evaluation). -/
def CompletedRestrictionComparisons.reduction_unit
    {U V : Option X.ProEt} {a : RestrictionArrow X U V}
    (d : CompletedRestrictionComparisons l E X a) : Prop :=
  ∀ (P : Cx l E X U) (n : ℕ),
  (restrictionComplex l E X a).map (((augmentation l E X U).app P).app (op n)) ≫
      (d.reductionIso n).hom.app P =
    ((augmentation l E X V).app ((restrictionComplex l E X a).obj P)).app (op n)

/-- Every product component is the prescribed restricted reduction projection. Source: Stacks
03DJ, 08JB, 08TC
(blueprint: lem-sf-rational-slice-completed-evaluation). -/
def CompletedRestrictionComparisons.product_projection
    {U V : Option X.ProEt} {a : RestrictionArrow X U V}
    (d : CompletedRestrictionComparisons l E X a) : Prop :=
  ∀ (P : Cx l E X U) (n : ℕ),
  (d.productIso P).hom ≫ Pi.π _ n =
    (restrictionComplex l E X a).map (Pi.π
      (fun k : ℕ ↦ ((tower l E X U).obj P).obj (op k)) n) ≫
        (d.reductionIso n).hom.app P

/-- First cone coordinate is precisely the product comparison. Source: Stacks 03DJ, 08JB, 08TC
(blueprint: lem-sf-rational-slice-completed-evaluation). -/
def CompletedRestrictionComparisons.roos_fst
    {U V : Option X.ProEt} {a : RestrictionArrow X U V}
    (d : CompletedRestrictionComparisons l E X a) : Prop :=
  ∀ P : Cx l E X U,
  d.roosIso.hom.app P ≫ CochainComplex.mappingCocone.fst
      (restrictionRoosStep l E X V ((restrictionComplex l E X a).obj P)) =
    (restrictionComplex l E X a).map
      (CochainComplex.mappingCocone.fst (restrictionRoosStep l E X U P)) ≫
        (d.productIso P).hom

/-- The degree-minus-one coordinate is the same product comparison as well. Source: Stacks 03DJ,
08JB, 08TC
(blueprint: lem-sf-rational-slice-completed-evaluation). -/
def CompletedRestrictionComparisons.roos_snd
    {U V : Option X.ProEt} {a : RestrictionArrow X U V}
    (d : CompletedRestrictionComparisons l E X a) : Prop :=
  ∀ (P : Cx l E X U) (i j : ℤ) (h : i + -1 = j),
  (d.roosIso.hom.app P).f i ≫
      (CochainComplex.mappingCocone.snd
        (restrictionRoosStep l E X V ((restrictionComplex l E X a).obj P))).v i j h =
    (restrictionModules l E X a).map
      ((CochainComplex.mappingCocone.snd (restrictionRoosStep l E X U P)).v i j h) ≫
        (d.productIso P).hom.f j

/-- Its descent agrees with the prescribed shifted-cone comparison. Source: Stacks 03DJ, 08JB, 08TC
(blueprint: lem-sf-rational-slice-completed-evaluation). -/
def CompletedRestrictionComparisons.completion_model
    {U V : Option X.ProEt} {a : RestrictionArrow X U V}
    (d : CompletedRestrictionComparisons l E X a) : Prop :=
  ∀ P : (Good l E X U).FullSubcategory,
  (restrictionDerived l E X a).map ((completionComparison l E X U).hom.app P) ≫
      (restrictionLocalization l E X a).hom.app ((roos l E X U).obj P.obj) ≫
      DerivedCategory.Q.map (d.roosIso.hom.app P.obj) =
    d.completionIso.hom.app (DerivedCategory.Q.obj P.obj) ≫
      (completion l E X V).map ((restrictionLocalization l E X a).hom.app P.obj) ≫
      (completionComparison l E X V).hom.app
        ⟨(restrictionComplex l E X a).obj P.obj, d.good P.obj P.property⟩

/-- The normalized completion unit is preserved. Source: Stacks 03DJ, 08JB, 08TC
(blueprint: lem-sf-rational-slice-completed-evaluation). -/
def CompletedRestrictionComparisons.completion_unit
    {U V : Option X.ProEt} {a : RestrictionArrow X U V}
    (d : CompletedRestrictionComparisons l E X a) : Prop :=
  ∀ L : D l E X U,
  (restrictionDerived l E X a).map ((completionUnit l E X U).app L) ≫
      d.completionIso.hom.app L =
    (completionUnit l E X V).app ((restrictionDerived l E X a).obj L)

/-- It is completion of the ordinary tensor comparison, with the actual Roos descent. Source:
Stacks 03DJ, 08JB, 08TC
(blueprint: lem-sf-rational-slice-completed-evaluation). -/
def CompletedRestrictionComparisons.tensor_completion
    {U V : Option X.ProEt} {a : RestrictionArrow X U V}
    (d : CompletedRestrictionComparisons l E X a) : Prop :=
  ∀ L M : D l E X U,
  d.tensorIso.hom.app (L, M) =
    d.completionIso.hom.app ((duality l E X U).closed.tensor.obj (L, M)) ≫
      (completion l E X V).map (d.ordinaryTensorIso.hom.app (L, M))

/-- Completeness gives the reflection bijection for the specified quotient completion.
Source: Stacks 099F, Bhatt--Scholze 3.4.11
(blueprint: lem-sf-rational-slice-completed-evaluation).
Proof: the DVR is Noetherian. The two-term free resolutions of its positive
uniformizer quotients identify the strict reduction tower with the dual Koszul
tower, respecting its actual unit. The Cech completion model is the reflection
into locally complete objects. A Roos triangle identifies a complete target with
this limit, so it is locally complete. The reflector's universal property gives
exactly the stated precomposition bijection, also on every over-site. -/
theorem restrictionCompletion_bijective
    (_hInv : ∀ x : X, IsUnit (l : X.presheaf.stalk x)) (U : Option X.ProEt)
    (Z N : D l E X U) (_hN : IsComplete l E X U N) :
    Function.Bijective (fun f : (completion l E X U).obj Z ⟶ N ↦
      (completionUnit l E X U).app Z ≫ f) := by
  sorry

/-- The inverse of precomposition with the actual completion unit.
Source: Stacks 099F (blueprint: lem-sf-rational-slice-completed-evaluation). -/
def restrictionCompletionEquiv
    (hInv : ∀ x : X, IsUnit (l : X.presheaf.stalk x)) (U : Option X.ProEt)
    (Z N : D l E X U) (hN : IsComplete l E X U N) :
    ((completion l E X U).obj Z ⟶ N) ≃ (Z ⟶ N) :=
  Equiv.ofBijective _ (restrictionCompletion_bijective l E X hInv U Z N hN)

/-- Derived internal Hom into a complete target is complete on the same site.
Source: Stacks 099A, Bhatt--Scholze 3.4.11
(blueprint: lem-sf-rational-slice-completed-evaluation).
Proof: the Roos condition implies local completeness by the Cech/Koszul comparison.
On any further slice, curry and interchange the two tensor factors to identify
Hom(B[1/f],Hom(L,M)) with Hom(L,Hom(B[1/f],M)). The latter vanishes for every
f in the uniformizer ideal. Thus Hom(L,M) is locally complete. The same
Cech/Koszul comparison identifies this condition with the stated quotient Roos
condition. No constructibility or boundedness of L on the slice is required. -/
theorem restrictionHom_complete
    (_hInv : ∀ x : X, IsUnit (l : X.presheaf.stalk x)) (U : Option X.ProEt)
    (L M : D l E X U) (_hM : IsComplete l E X U M) :
    IsComplete l E X U ((hom l E X U).obj (op L, M)) := by
  sorry

/-- The completed evaluation is the unique extension of the actual ordinary evaluation
along the normalized completion unit; no arbitrary map or lift is chosen.
Source: Bhatt--Scholze 3.4.11, Stacks 099F
(blueprint: lem-sf-rational-slice-completed-evaluation). -/
def restrictionCompletedEvaluation
    (hInv : ∀ x : X, IsUnit (l : X.presheaf.stalk x)) (U : Option X.ProEt)
    (L M : D l E X U) (hM : IsComplete l E X U M) :
    (phi l E X U M).obj (op L) ⟶ (psi l E X U M).obj (op L) :=
  (restrictionCompletionEquiv l E X hInv U
    ((ordinaryPhi l E X U M).obj (op L)) ((hom l E X U).obj (op L, M))
    (restrictionHom_complete l E X hInv U L M hM)).symm
      (ordinaryEvaluation l E X U L M)

/-- The completed right coefficient-unit constraint, extended from scalar multiplication.
Source: Bhatt--Scholze 3.4.11, Stacks 099F
(blueprint: lem-sf-rational-slice-completed-evaluation). -/
def restrictionCompletedRightUnit
    (hInv : ∀ x : X, IsUnit (l : X.presheaf.stalk x)) (U : Option X.ProEt)
    (L : D l E X U) (hL : IsComplete l E X U L) :
    (completedTensor l E X U).obj (L, coefficient l E X U) ⟶ L :=
  (restrictionCompletionEquiv l E X hInv U
    ((duality l E X U).closed.tensor.obj (L, coefficient l E X U)) L hL).symm
      ((duality l E X U).closed.tensor.map
        (X := (L, coefficient l E X U))
        (Y := (L, (duality l E X U).closed.monoidal.tensorUnit))
        (𝟙 L, (duality l E X U).unitIso.inv) ≫
        ((duality l E X U).closed.monoidal.rightUnitor L).hom)

/-- The comparison on the evaluation source includes restriction of the coefficient dual.
Source: blueprint, dualizable biduality proof
(blueprint: lem-sf-rational-slice-completed-evaluation). -/
def restrictionEvaluationSource {U V : Option X.ProEt} {a : RestrictionArrow X U V}
    (d : CompletedRestrictionComparisons l E X a) (L M : D l E X U) :
    (restrictionDerived l E X a).obj ((phi l E X U M).obj (op L)) ≅
      (phi l E X V ((restrictionDerived l E X a).obj M)).obj
        (op ((restrictionDerived l E X a).obj L)) :=
  d.tensorIso.app ((hom l E X U).obj (op L, coefficient l E X U), M) ≪≫
    (completedTensor l E X V).mapIso
      (Iso.prod
        (d.homIso.app (op L, coefficient l E X U) ≪≫
          (hom l E X V).mapIso (Iso.prod (Iso.refl _) d.coefficientIso)) (Iso.refl _))

/-- The index for composing actual restriction and relocalization arrows.
Source: Stacks 03EH (blueprint: lem-sf-rational-slice-completed-evaluation). -/
def restrictionComp {U V W : Option X.ProEt}
    (a : RestrictionArrow X U V) (b : RestrictionArrow X V W) : RestrictionArrow X U W :=
  match U, V, W, a, b with
  | none, _, _, _, _ => PUnit.unit
  | some _, none, _, a, _ => PEmpty.elim a
  | some _, some _, none, _, b => PEmpty.elim b
  | some _, some _, some _, a, b => b ≫ a

/-- The canonical derived composite comparison attached to a sectionwise module comparison.
Source: Stacks 03EH (blueprint: lem-sf-rational-slice-completed-evaluation). -/
def restrictionCompDerived {U V W : Option X.ProEt}
    (a : RestrictionArrow X U V) (b : RestrictionArrow X V W)
    (μ : restrictionModules l E X a ⋙ restrictionModules l E X b ≅
      restrictionModules l E X (restrictionComp X a b)) :
    restrictionDerived l E X a ⋙ restrictionDerived l E X b ≅
      restrictionDerived l E X (restrictionComp X a b) :=
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫ Functor.mapDerivedCategoryNatIso μ


/-- The sectionwise rank-one coefficient restriction, with no scalar change.
Source: Stacks 03DH (blueprint: lem-sf-rational-slice-completed-evaluation). -/
def restrictionCoefficientModuleIso {U V : Option X.ProEt} (a : RestrictionArrow X U V) :
    (restrictionModules l E X a).obj (SheafOfModules.unit (rings l E X U)) ≅
      SheafOfModules.unit (rings l E X V) :=
  match U, V, a with
  | none, none, _ => Iso.refl _
  | none, some _, _ => Iso.refl _
  | some _, none, a => PEmpty.elim a
  | some _, some _, a => SheafOfModules.overMapUnitIso (R := rings l E X none) a

/-- The prescribed coefficient comparison in degree zero.
Source: Stacks 03DH (blueprint: lem-sf-rational-slice-completed-evaluation). -/
def restrictionCoefficientIso {U V : Option X.ProEt} (a : RestrictionArrow X U V) :
    (restrictionDerived l E X a).obj (coefficient l E X U) ≅ coefficient l E X V :=
  ((restrictionModules l E X a).mapDerivedCategorySingleFunctor 0).app
      (SheafOfModules.unit (rings l E X U)) ≪≫
    (DerivedCategory.singleFunctor (Mod l E X V) 0).mapIso
      (restrictionCoefficientModuleIso l E X a)

/-- All chain-level and descent normalizations required of a comparison datum.
Source: Stacks 03DJ, 08TC (blueprint: lem-sf-rational-slice-completed-evaluation). -/
def CompletedRestrictionComparisons.Normalized
    {U V : Option X.ProEt} {a : RestrictionArrow X U V}
    (d : CompletedRestrictionComparisons l E X a) : Prop :=
  d.reduction_generator ∧ d.reduction_transition ∧ d.reduction_unit ∧
    d.product_projection ∧ d.roos_fst ∧ d.roos_snd ∧ d.completion_model ∧
    d.completion_unit ∧ d.tensor_completion ∧
    d.coefficientIso = restrictionCoefficientIso l E X a

/-- On direct restriction the ordinary tensor and Hom comparisons are precisely the
published pure-tensor and local-Hom-family comparisons, including their model squares.
Source: Stacks 07A4, 08JB (blueprint: lem-sf-rational-slice-completed-evaluation). -/
def CompletedRestrictionComparisons.GlobalModel (B : X.ProEt)
    (d : CompletedRestrictionComparisons l E X
      (U := none) (V := some B) PUnit.unit) : Prop :=
  letI : HasDerivedCategory (SheafOfModules.{max u (t + 1)}
      ((sheafCompose ((topology X none).over B)
        (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj
          ((ring l E X none).over B))) := hasDerived l E X (some B)
  ∃ e : RingedSliceEvaluationComparisons
      (hom l E X none) (hom l E X (some B))
      (restrictionDerived l E X (U := none) (V := some B) PUnit.unit)
      (duality l E X none).closed (duality l E X (some B)).closed
      (RingedSliceFlatRestriction (topology X none) (ring l E X none) B),
    RingedSliceEvaluationNormalized (topology X none) (ring l E X none) B
      (duality l E X none).closed (duality l E X none).models
      (duality l E X (some B)).closed (duality l E X (some B)).models e ∧
    (∀ L M : D l E X none, d.ordinaryTensorIso.hom.app (L, M) = (e.rho L M).hom) ∧
    (∀ L M : D l E X none, d.homIso.hom.app (op L, M) = (e.eta L M).hom)

/-- Restriction retains the constant-section coefficient scalar action.
Source: Stacks 03DJ (blueprint: lem-sf-rational-slice-completed-evaluation).
Proof: multiplication by each integral constant restricts to multiplication by the
same constant. This equality holds on complexes in each degree. Fully faithful
whiskering by quasi-isomorphism localization descends it to derived morphisms,
including those represented by roofs. This is the asserted linearity. -/
theorem restrictionDerived_linear {U V : Option X.ProEt} (a : RestrictionArrow X U V) :
    (restrictionDerived l E X a).Linear (Padic.coefficientExtensionIntegers l E) := by
  sorry

/-- Use the canonical scalar-action preservation just stated.
Source: Stacks 03DJ (blueprint: lem-sf-rational-slice-completed-evaluation). -/
instance restrictionDerivedLinear {U V : Option X.ProEt} (a : RestrictionArrow X U V) :
    (restrictionDerived l E X a).Linear (Padic.coefficientExtensionIntegers l E) :=
  restrictionDerived_linear l E X a

/-- Scalar extension of the actual restriction map on Hom modules.
Source: blueprint, scalar localization
(blueprint: lem-sf-rational-slice-completed-evaluation). -/
def restrictionRationalHom {U V : Option X.ProEt} (a : RestrictionArrow X U V)
    (L M : D l E X U) :=
  ((restrictionDerived l E X a).mapLinearMap (Padic.coefficientExtensionIntegers l E)
    (X := L) (Y := M)).baseChange
      (Localization.Away (Padic.coefficientExtensionUniformizer l E))

/-- The scalar-extended Hom maps preserve identities and composition.
Source: blueprint, scalar localization
(blueprint: lem-sf-rational-slice-completed-evaluation).
Proof: on pure tensors the map is c tensor f mapped to c tensor r(f). Identities
are 1 tensor identity and composition is the product of the two scalars tensor
the composed morphism. Functoriality of r gives both equations on pure tensors;
bilinearity extends the composition equation to all tensor elements. -/
theorem restrictionRationalHom_laws {U V : Option X.ProEt} (a : RestrictionArrow X U V) :
    (∀ L : D l E X U,
      restrictionRationalHom l E X a L L ((q l E X U).map (𝟙 L)) =
        (q l E X V).map (𝟙 ((restrictionDerived l E X a).obj L))) ∧
    (∀ (L M N : Rational l E X U) (f : L ⟶ M) (g : M ⟶ N),
      restrictionRationalHom l E X a L.obj N.obj (f ≫ g) =
        ScalarLocalization.composition (Padic.coefficientExtensionIntegers l E)
          (D l E X V) (Padic.coefficientExtensionUniformizer l E)
          ((restrictionDerived l E X a).obj L.obj)
          ((restrictionDerived l E X a).obj M.obj)
          ((restrictionDerived l E X a).obj N.obj)
          (restrictionRationalHom l E X a M.obj N.obj g)
          (restrictionRationalHom l E X a L.obj M.obj f)) := by
  sorry

/-- The induced functor between the two actual scalar localizations.
Source: blueprint, scalar localization
(blueprint: lem-sf-rational-slice-completed-evaluation). -/
def restrictionRational {U V : Option X.ProEt} (a : RestrictionArrow X U V) :
    Rational l E X U ⥤ Rational l E X V where
  obj L := ⟨(restrictionDerived l E X a).obj L.obj⟩
  map {L M} f := restrictionRationalHom l E X a L.obj M.obj f
  map_id L := (restrictionRationalHom_laws l E X a).1 L.obj
  map_comp f g := (restrictionRationalHom_laws l E X a).2 _ _ _ f g

/-- The required completed evaluation square for a specified complete pair.
Source: blueprint, dualizable biduality proof; Bhatt--Scholze 3.4.11
(blueprint: lem-sf-rational-slice-completed-evaluation). -/
def CompletedRestrictionComparisons.Evaluation
    (hInv : ∀ x : X, IsUnit (l : X.presheaf.stalk x))
    {U V : Option X.ProEt} {a : RestrictionArrow X U V}
    (d : CompletedRestrictionComparisons l E X a) (L M : D l E X U)
    (hM : IsComplete l E X U M)
    (hRM : IsComplete l E X V ((restrictionDerived l E X a).obj M)) : Prop :=
  (restrictionDerived l E X a).map (restrictionCompletedEvaluation l E X hInv U L M hM) ≫
      d.homIso.hom.app (op L, M) =
    (restrictionEvaluationSource l E X d L M).hom ≫
      restrictionCompletedEvaluation l E X hInv V
        ((restrictionDerived l E X a).obj L) ((restrictionDerived l E X a).obj M) hRM

/-- The same square after taking the specified images in the scalar localizations.
Source: blueprint, dualizable biduality proof
(blueprint: lem-sf-rational-slice-completed-evaluation). -/
def CompletedRestrictionComparisons.RationalEvaluation
    (hInv : ∀ x : X, IsUnit (l : X.presheaf.stalk x))
    {U V : Option X.ProEt} {a : RestrictionArrow X U V}
    (d : CompletedRestrictionComparisons l E X a) (L M : D l E X U)
    (hM : IsComplete l E X U M)
    (hRM : IsComplete l E X V ((restrictionDerived l E X a).obj M)) : Prop :=
  (restrictionRational l E X a).map
      ((q l E X U).map (restrictionCompletedEvaluation l E X hInv U L M hM)) ≫
      (q l E X V).map (d.homIso.hom.app (op L, M)) =
    (q l E X V).map (restrictionEvaluationSource l E X d L M).hom ≫
      (q l E X V).map (restrictionCompletedEvaluation l E X hInv V
        ((restrictionDerived l E X a).obj L) ((restrictionDerived l E X a).obj M) hRM)

/-- Preservation of the completed coefficient-unit constraint on a complete input.
Source: Bhatt--Scholze 3.4.11
(blueprint: lem-sf-rational-slice-completed-evaluation). -/
def CompletedRestrictionComparisons.CoefficientUnit
    (hInv : ∀ x : X, IsUnit (l : X.presheaf.stalk x))
    {U V : Option X.ProEt} {a : RestrictionArrow X U V}
    (d : CompletedRestrictionComparisons l E X a) (L : D l E X U)
    (hL : IsComplete l E X U L)
    (hRL : IsComplete l E X V ((restrictionDerived l E X a).obj L)) : Prop :=
  (restrictionDerived l E X a).map (restrictionCompletedRightUnit l E X hInv U L hL) =
    d.tensorIso.hom.app (L, coefficient l E X U) ≫
      (completedTensor l E X V).map
        (X := ((restrictionDerived l E X a).obj L,
          (restrictionDerived l E X a).obj (coefficient l E X U)))
        (Y := ((restrictionDerived l E X a).obj L, coefficient l E X V))
        (𝟙 _, d.coefficientIso.hom) ≫
      restrictionCompletedRightUnit l E X hInv V ((restrictionDerived l E X a).obj L) hRL


/-- Restriction transports the Roos triangle of a complete object to its actual slice tower.
Source: Stacks 03DJ and 08TC (blueprint: lem-sf-rational-slice-completed-evaluation).
Proof: exact extension by zero is left adjoint to restriction. Their derived
adjunction makes restriction preserve derived products, with the restricted
projections. K-flat restriction identifies every reduction, transition and unit.
Applying exact restriction to the original Roos triangle therefore gives precisely
the target Roos triangle, with its canonical first map and 1-s middle map. -/
theorem restrictionComplete {U V : Option X.ProEt} (a : RestrictionArrow X U V)
    (L : D l E X U) (_hL : IsComplete l E X U L) :
    IsComplete l E X V ((restrictionDerived l E X a).obj L) := by
  sorry

/-- Direct restriction, including the ambient identity case U=none.
Source: Stacks 03DH (blueprint: lem-sf-rational-slice-completed-evaluation). -/
def restrictionGlobal (U : Option X.ProEt) : D l E X none ⥤ D l E X U :=
  restrictionDerived l E X (U := none) (V := U) PUnit.unit

/-- Identity restriction index, including the ambient site.
Source: Stacks 03EH (blueprint: lem-sf-rational-slice-completed-evaluation). -/
def restrictionId (U : Option X.ProEt) : RestrictionArrow X U U :=
  match U with
  | none => PUnit.unit
  | some B => 𝟙 B

/-- The derived identity comparison induced by its sectionwise module identity.
Source: Stacks 03EH (blueprint: lem-sf-rational-slice-completed-evaluation). -/
def restrictionIdDerived (U : Option X.ProEt)
    (ε : restrictionModules l E X (restrictionId X U) ≅ 𝟭 (Mod l E X U)) :
    restrictionDerived l E X (restrictionId X U) ≅ 𝟭 (D l E X U) :=
  Functor.mapDerivedCategoryNatIso ε ≪≫ Functor.mapDerivedCategoryIdIso (Mod l E X U)

/-- Composition coherence for completed tensor, ambient Hom, completion and coefficient unit.
The derived transport is induced by the actual sectionwise module comparison.
Source: Stacks 03EH, 08JB, 08TC
(blueprint: lem-sf-rational-slice-completed-evaluation). -/
def CompletedRestrictionComparisons.Composition
    {U V W : Option X.ProEt} (a : RestrictionArrow X U V) (b : RestrictionArrow X V W)
    (da : CompletedRestrictionComparisons l E X a)
    (db : CompletedRestrictionComparisons l E X b)
    (dc : CompletedRestrictionComparisons l E X (restrictionComp X a b))
    (μ : restrictionModules l E X a ⋙ restrictionModules l E X b ≅
      restrictionModules l E X (restrictionComp X a b)) : Prop :=
  (∀ L M : D l E X U,
    (restrictionDerived l E X b).map (da.tensorIso.hom.app (L, M)) ≫
        db.tensorIso.hom.app
          ((restrictionDerived l E X a).obj L, (restrictionDerived l E X a).obj M) ≫
        (completedTensor l E X W).map
          (X := ((restrictionDerived l E X b).obj ((restrictionDerived l E X a).obj L),
            (restrictionDerived l E X b).obj ((restrictionDerived l E X a).obj M)))
          (Y := ((restrictionDerived l E X (restrictionComp X a b)).obj L,
            (restrictionDerived l E X (restrictionComp X a b)).obj M))
          ((restrictionCompDerived l E X a b μ).hom.app L,
            (restrictionCompDerived l E X a b μ).hom.app M) =
      (restrictionCompDerived l E X a b μ).hom.app ((completedTensor l E X U).obj (L, M)) ≫
        dc.tensorIso.hom.app (L, M)) ∧
  (∀ L M : D l E X U,
    (restrictionDerived l E X b).map (da.homIso.hom.app (op L, M)) ≫
        db.homIso.hom.app
          (op ((restrictionDerived l E X a).obj L), (restrictionDerived l E X a).obj M) ≫
        (hom l E X W).map
          (X := (op ((restrictionDerived l E X b).obj ((restrictionDerived l E X a).obj L)),
            (restrictionDerived l E X b).obj ((restrictionDerived l E X a).obj M)))
          (Y := (op ((restrictionDerived l E X (restrictionComp X a b)).obj L),
            (restrictionDerived l E X (restrictionComp X a b)).obj M))
          (((restrictionCompDerived l E X a b μ).inv.app L).op,
            (restrictionCompDerived l E X a b μ).hom.app M) =
      (restrictionCompDerived l E X a b μ).hom.app ((hom l E X U).obj (op L, M)) ≫
        dc.homIso.hom.app (op L, M)) ∧
  (∀ L : D l E X U,
    (restrictionDerived l E X b).map (da.completionIso.hom.app L) ≫
        db.completionIso.hom.app ((restrictionDerived l E X a).obj L) ≫
        (completion l E X W).map ((restrictionCompDerived l E X a b μ).hom.app L) =
      (restrictionCompDerived l E X a b μ).hom.app ((completion l E X U).obj L) ≫
        dc.completionIso.hom.app L) ∧
  (restrictionDerived l E X b).map da.coefficientIso.hom ≫ db.coefficientIso.hom =
    (restrictionCompDerived l E X a b μ).hom.app (coefficient l E X U) ≫ dc.coefficientIso.hom

/-- The identity comparisons are identities after the prescribed identity transport.
Source: Stacks 03EH (blueprint: lem-sf-rational-slice-completed-evaluation). -/
def CompletedRestrictionComparisons.Identity (U : Option X.ProEt)
    (d : CompletedRestrictionComparisons l E X (restrictionId X U))
    (ε : restrictionModules l E X (restrictionId X U) ≅ 𝟭 (Mod l E X U)) : Prop :=
  (∀ L M : D l E X U,
    d.tensorIso.hom.app (L, M) ≫ (completedTensor l E X U).map
        (X := ((restrictionDerived l E X (restrictionId X U)).obj L,
          (restrictionDerived l E X (restrictionId X U)).obj M)) (Y := (L, M))
        ((restrictionIdDerived l E X U ε).hom.app L,
          (restrictionIdDerived l E X U ε).hom.app M) =
      (restrictionIdDerived l E X U ε).hom.app ((completedTensor l E X U).obj (L, M))) ∧
  (∀ L M : D l E X U,
    d.homIso.hom.app (op L, M) ≫ (hom l E X U).map
        (X := (op ((restrictionDerived l E X (restrictionId X U)).obj L),
          (restrictionDerived l E X (restrictionId X U)).obj M)) (Y := (op L, M))
        (((restrictionIdDerived l E X U ε).inv.app L).op,
          (restrictionIdDerived l E X U ε).hom.app M) =
      (restrictionIdDerived l E X U ε).hom.app ((hom l E X U).obj (op L, M))) ∧
  (∀ L : D l E X U,
    d.completionIso.hom.app L ≫
        (completion l E X U).map ((restrictionIdDerived l E X U ε).hom.app L) =
      (restrictionIdDerived l E X U ε).hom.app ((completion l E X U).obj L)) ∧
  d.coefficientIso.hom = (restrictionIdDerived l E X U ε).hom.app (coefficient l E X U)

/-- Sectionwise normalization makes the successive restriction comparisons canonical.
The heterogeneous equality says the underlying function is literally the identity;
its two module structures are the specified (possibly differently presented) restrictions.
Source: Stacks 03EH (blueprint: lem-sf-rational-slice-completed-evaluation). -/
def restrictionCompositionSections {U V W : Option X.ProEt}
    (a : RestrictionArrow X U V) (b : RestrictionArrow X V W)
    (μ : restrictionModules l E X a ⋙ restrictionModules l E X b ≅
      restrictionModules l E X (restrictionComp X a b)) : Prop :=
  ∀ (M : Mod l E X U) (Z : (Site X W)ᵒᵖ),
    HEq (fun x ↦ ((μ.hom.app M).val.app Z) x)
      (id : (((restrictionModules l E X a ⋙ restrictionModules l E X b).obj M).val.obj Z) →
        (((restrictionModules l E X a ⋙ restrictionModules l E X b).obj M).val.obj Z))

/-- The same sectionwise normalization for identity restriction.
Source: Stacks 03EH (blueprint: lem-sf-rational-slice-completed-evaluation). -/
def restrictionIdentitySections (U : Option X.ProEt)
    (ε : restrictionModules l E X (restrictionId X U) ≅ 𝟭 (Mod l E X U)) : Prop :=
  ∀ (M : Mod l E X U) (Z : (Site X U)ᵒᵖ),
    HEq (fun x ↦ ((ε.hom.app M).val.app Z) x)
      (id : (((restrictionModules l E X (restrictionId X U)).obj M).val.obj Z) →
        (((restrictionModules l E X (restrictionId X U)).obj M).val.obj Z))


/-- All comparisons compose with the canonical sectionwise restriction transports,
and the identity case is included on every site.
Source: Stacks 03EH (blueprint: lem-sf-rational-slice-completed-evaluation). -/
def CompletedRestrictionComparisons.Coherent
    (d : ∀ (U V : Option X.ProEt) (a : RestrictionArrow X U V),
      CompletedRestrictionComparisons l E X a) : Prop :=
  (∀ (U V W : Option X.ProEt) (a : RestrictionArrow X U V) (b : RestrictionArrow X V W),
    ∃ μ : restrictionModules l E X a ⋙ restrictionModules l E X b ≅
        restrictionModules l E X (restrictionComp X a b),
      restrictionCompositionSections l E X a b μ ∧
        CompletedRestrictionComparisons.Composition l E X a b
          (d U V a) (d V W b) (d U W (restrictionComp X a b)) μ) ∧
  (∀ U : Option X.ProEt,
    ∃ ε : restrictionModules l E X (restrictionId X U) ≅ 𝟭 (Mod l E X U),
      restrictionIdentitySections l E X U ε ∧
        CompletedRestrictionComparisons.Identity l E X U (d U U (restrictionId X U)) ε)

/-- Restriction commutes with reduction, completion, completed tensor, ambient derived
internal Hom, coefficient unit and the actual evaluation, before and after rationalization.

Source: main-20261015 blueprint, sec-six-functors/sk-prop-sf-dualizable-biduality,
termwise compatibility and unit argument; Stacks 03DJ, 08JB, 08TC, 099F;
Bhatt--Scholze Definitions 3.4.10, 3.5.2 and Lemma 3.4.11
(blueprint: lem-sf-rational-slice-completed-evaluation).

Proof (the ten DAG steps):
1. Exact restriction and exact extension by zero are adjoint. Their termwise derived
   adjunction makes restriction preserve products with the restricted projections.
   Sheaf-level limits and restriction of scalars are sectionwise.
   Uses: lem-pur-site-restriction-module-adjunction-exact, lem-pc-derived-adjoint-functors,
   lem-weil-pbc-module-sheaves-limits-sectionwise, def-pur-localized-ringed-site.
2. The localization ring map is the identity. Restriction preserves flat-term K-flats;
   the ordinary tensor comparison identifies each reduction, quotient transition and unit.
   Uses: lem-weil-pbc-ringed-topoi-derived-tensor-pullback, def-pur-integral-derived-operations.
3. Apply restriction to the completeness Roos triangle of K and M. The preceding product
   and reduction identifications carry its 1-s to precisely the slice 1-s, proving slice
   completeness, with no constructibility assertion on a slice.
   Uses: def-weil-derived-complete-integral-detailed, def-weil-derived-complete,
   lem-pur-site-restriction-module-adjunction-exact.
4. On strict good representatives restriction commutes with both product coordinates,
   shifts and the cone differential. It thus identifies the specified Cone(1-s)[-1]
   and its (reduction-units,0) augmentation, naturally in the representatives.
   Uses: def-pur-integral-derived-operations, lem-weil-proetale-countable-products-exact,
   lem-weil-derived-limit-existence, lem-pur-integral-operations-well-defined.
5. Restrict a K-injective second argument of Hom; local families of module maps and
   their differentials are unchanged. The published normalized Hom model gives the
   comparison, also for the coefficient object. Forgetting successive structural
   arrows gives the composition and identity comparisons.
   Uses: def-pur-integral-derived-operations, lem-weil-pbc-ringed-internal-hom-exact-restriction,
   lem-weil-pbc-ringed-slice-evaluation-transpose, def-pur-localized-ringed-site.
6. The valuation ring is a Noetherian DVR. Its two-term uniformizer-power resolutions,
   with transition (uniformizer,1), identify the quotient limit with the Cech/Koszul
   completion reflector, preserving its strict-tower unit on every slice.
   Uses: lem-weil-l-adic-extension-integers-dvr, lem-weil-pbc-completed-constant-sheaf-reduction,
   lem-weil-pbc-ringed-strict-tower-homotopy-limit, lem-weil-pbc-ringed-cech-koszul-dual-limit,
   lem-weil-pbc-extended-cech-completion-model.
7. The Roos condition implies local completeness. Currying twice and tensor symmetry
   give Hom(B[1/f],Hom(K,M))=Hom(K,Hom(B[1/f],M))=0 on every further slice. The reflector
   therefore gives the bijection extending arrows into Hom(K,M) along completion.
   Uses: def-weil-derived-complete, lem-weil-pbc-ringed-internal-hom-exact-restriction,
   lem-weil-pbc-ringed-slice-evaluation-transpose, lem-weil-pbc-extended-cech-completion-model,
   lem-weil-pbc-ringed-strict-tower-homotopy-limit.
8. Ordinary evaluation is the transpose of coefficient evaluation after reassociation
   and Koszul interchange. The published normalized slice evaluation/transpose theorem
   and ordinary tensor model identify this transpose with the slice transpose.
   Uses: lem-weil-pbc-ringed-slice-evaluation-transpose,
   lem-weil-pbc-ringed-topoi-derived-tensor-pullback.
9. The balanced finite tensor identity sends (p tensor q) tensor a to
   (p tensor 1) tensor (q tensor a), with inverse multiplying coefficients. It identifies
   completed tensor with completion of ordinary tensor, compatibly with strict units.
   Both transported completed evaluations extend the same ordinary evaluation; the
   reflector bijection makes them equal. The same argument preserves the completed
   coefficient unitor and proves coherence under successive restriction.
   Uses: def-pur-integral-derived-operations, lem-weil-pbc-site-derived-tensor-descent,
   lem-weil-pbc-extended-cech-completion-model.
10. Restriction is integral-linear on sections and hence on derived roofs. Extend its
   Hom maps by scalars, sending c tensor f to c tensor r(f). The tensor relations and
   functoriality give the localization functor. Apply it to the integral evaluation
   square; the identity and composition equalities are preserved as well.
   Uses: def-weil-linear-scalar-localization.
-/
theorem rationalSliceCompletedEvaluation
    (X : AlgebraicGeometry.Scheme.{u})
    (hInv : ∀ x : X, IsUnit (l : X.presheaf.stalk x))
    (K M : D l E X none)
    (_hK : sfIntegralConstructible l E X K) (_hM : sfIntegralConstructible l E X M) :
    ∃ (_hKcomplete : IsComplete l E X none K) (hM : IsComplete l E X none M)
      (d : ∀ (U V : Option X.ProEt) (a : RestrictionArrow X U V),
        CompletedRestrictionComparisons l E X a),
      (∀ (U V : Option X.ProEt) (a : RestrictionArrow X U V), (d U V a).Normalized) ∧
      (∀ B : X.ProEt,
        CompletedRestrictionComparisons.GlobalModel l E X B (d none (some B) PUnit.unit)) ∧
      CompletedRestrictionComparisons.Coherent l E X d ∧
      (∀ (U V : Option X.ProEt) (a : RestrictionArrow X U V) (L : D l E X U)
          (hL : IsComplete l E X U L),
        CompletedRestrictionComparisons.CoefficientUnit l E X hInv (d U V a) L hL
          (restrictionComplete l E X a L hL)) ∧
      (∀ B : X.ProEt,
        IsComplete l E X (some B) ((restrictionGlobal l E X (some B)).obj K) ∧
        IsComplete l E X (some B) ((restrictionGlobal l E X (some B)).obj M) ∧
        CompletedRestrictionComparisons.Evaluation l E X hInv
          (d none (some B) PUnit.unit) K M hM
          (restrictionComplete l E X (U := none) (V := some B) PUnit.unit M hM) ∧
        CompletedRestrictionComparisons.RationalEvaluation l E X hInv
          (d none (some B) PUnit.unit) K M hM
          (restrictionComplete l E X (U := none) (V := some B) PUnit.unit M hM)) ∧
      (∀ (B C : X.ProEt) (f : C ⟶ B),
        CompletedRestrictionComparisons.Evaluation l E X hInv
          (d (some B) (some C) f)
          ((restrictionGlobal l E X (some B)).obj K)
          ((restrictionGlobal l E X (some B)).obj M)
          (restrictionComplete l E X (U := none) (V := some B) PUnit.unit M hM)
          (restrictionComplete l E X (U := some B) (V := some C) f
            ((restrictionGlobal l E X (some B)).obj M)
            (restrictionComplete l E X (U := none) (V := some B) PUnit.unit M hM)) ∧
        CompletedRestrictionComparisons.RationalEvaluation l E X hInv
          (d (some B) (some C) f)
          ((restrictionGlobal l E X (some B)).obj K)
          ((restrictionGlobal l E X (some B)).obj M)
          (restrictionComplete l E X (U := none) (V := some B) PUnit.unit M hM)
          (restrictionComplete l E X (U := some B) (V := some C) f
            ((restrictionGlobal l E X (some B)).obj M)
            (restrictionComplete l E X (U := none) (V := some B) PUnit.unit M hM))) := by
  sorry

end WeilConjectures.IntegralOnSlice
