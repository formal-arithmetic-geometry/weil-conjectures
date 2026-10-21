/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NX
-/
module

public import Sheaf.SixFunctors.OpenTensorQuotientAugmentation
public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Sheaf.Paper.CompletedIntegralConstantMapOfUniverses
public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Sheaf.CategoryTheory.LocalizedModuleExactForSystems
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Sheaf.Paper.SfIntegralConstructible
public import Sheaf.Paper.IntegralReductionTowerCanonical
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import Sheaf.SixFunctors.OpenTensorNormalization
public import Sheaf.Paper.IntegralDerivedOperationsOnSlices
public import Sheaf.SixFunctors.ConstructibleTensorCompletion
public import Sheaf.Paper.ExactProductFunctorStrictLimit
public import Sheaf.Paper.ExchangeProjectionSuppliedDomains
import Sheaf.AlgebraicGeometry.ProEtaleRingedOpenExtensionProducts
import Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact
import Sheaf.CategoryTheory.StrictRoosComparison
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Sheaf.SixFunctors.OpenFactorTensorModel
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

/-! # The augmented open projection formula after Roos completion

Source: Stacks Project, proetale.tex, Tag 09BP, lemma-j-shriek-limits;
Bhatt--Scholze, Lemmas 6.5.5 and 6.5.8, pp.49--50; the augmentation-normalized
construction in the DAG (blueprint: lem-sf-open-projection-roos-completion).

The coefficient index n denotes the positive exponent n+1. The ambient categories
are the ordinary unbounded derived categories over the completed coefficient sheaf.
All comparison data below are conclusions, with their representative equations.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genInjectivity false
set_option genSizeOfSpec false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u a b c d wA wB
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.OpenProjectionRoos

section Roos
variable {A : Type a} {B : Type b} [Category.{c} A] [Category.{d} B]
  [Abelian A] [Abelian B] [HasCountableProducts A] [HasCountableProducts B]

/-- The boundary of the recorded strict Roos model, without changing its signs.
Source: Stacks 0941 (blueprint: lem-sf-open-projection-roos-completion). -/
abbrev boundary (T : ℕᵒᵖ ⥤ CochainComplex A ℤ) :=
  towerTransitionEndomorphism (K := fun n ↦ T.obj (op n)) (integralOperationsTowerStep T)

/-- Postcomposition of strict towers by the actual termwise functor.
Source: Stacks 0941 (blueprint: lem-sf-open-projection-roos-completion). -/
abbrev onTowers (F : A ⥤ B) [F.Additive] :=
  (Functor.whiskeringRight ℕᵒᵖ _ _).obj (F.mapHomologicalComplex (.up ℤ))

/-- The normalized exact-product comparison. The first and shifted projection
identities specify its action on both summands of the signed mapping fiber.
The augmentation clause supplies the maps with coordinates (a,0) and states their
actual equality, before localization; it does not infer equality from limit projections.
Source: Stacks 09BP and lem-cbc-exact-product-functor-strict-limit
(blueprint: lem-sf-open-projection-roos-completion). -/
structure RoosComparison (F : A ⥤ B) [F.Additive] where
  products : ∀ T : ℕᵒᵖ ⥤ CochainComplex A ℤ,
    (F.mapHomologicalComplex (.up ℤ)).obj (∏ᶜ fun n ↦ T.obj (op n)) ≅
      ∏ᶜ fun n ↦ ((onTowers F).obj T).obj (op n)
  projections : ∀ (T : ℕᵒᵖ ⥤ CochainComplex A ℤ) (n : ℕ),
    (products T).hom ≫ Pi.π (fun k ↦ ((onTowers F).obj T).obj (op k)) n =
      (F.mapHomologicalComplex (.up ℤ)).map (Pi.π (fun k ↦ T.obj (op k)) n)
  iso : integralOperationsRoosFunctor ⋙ F.mapHomologicalComplex (.up ℤ) ≅
    onTowers F ⋙ integralOperationsRoosFunctor
  first : ∀ (T : ℕᵒᵖ ⥤ CochainComplex A ℤ),
    (iso.hom.app T) ≫ CochainComplex.mappingCocone.fst (boundary ((onTowers F).obj T)) =
      (F.mapHomologicalComplex (.up ℤ)).map
        (CochainComplex.mappingCocone.fst (boundary T)) ≫ (products T).hom
  shifted : ∀ (T : ℕᵒᵖ ⥤ CochainComplex A ℤ) (i k : ℤ) (h : i + -1 = k),
    (iso.hom.app T).f i ≫
        (CochainComplex.mappingCocone.snd (boundary ((onTowers F).obj T))).v i k h =
      F.map ((CochainComplex.mappingCocone.snd (boundary T)).v i k h) ≫
        ((products T).hom.f k)
  augmentations : ∀ (T : ℕᵒᵖ ⥤ CochainComplex A ℤ) (P : CochainComplex A ℤ)
    (a : (Functor.const ℕᵒᵖ).obj P ⟶ T),
    ∃ (b : P ⟶ integralOperationsRoos T)
      (b' : (F.mapHomologicalComplex (.up ℤ)).obj P ⟶
        integralOperationsRoos ((onTowers F).obj T)),
      b ≫ CochainComplex.mappingCocone.fst (boundary T) =
          Pi.lift (fun n ↦ a.app (op n)) ∧
      (∀ (i k : ℤ) (h : i + -1 = k),
        b.f i ≫ (CochainComplex.mappingCocone.snd (boundary T)).v i k h = 0) ∧
      b' ≫ CochainComplex.mappingCocone.fst (boundary ((onTowers F).obj T)) =
          Pi.lift (fun n ↦ (F.mapHomologicalComplex (.up ℤ)).map (a.app (op n))) ∧
      (∀ (i k : ℤ) (h : i + -1 = k), b'.f i ≫
        (CochainComplex.mappingCocone.snd (boundary ((onTowers F).obj T))).v i k h = 0) ∧
      (F.mapHomologicalComplex (.up ℤ)).map b ≫ iso.hom.app T = b'

variable [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wB} B]

/-- The same lambda in the derived category, through the canonical exact-functor
comparison. Roos computes the total right derived limit by the recorded strict-Roos
comparison, including its augmentation. No new derived-limit object is chosen.
Source: Stacks 0941 (blueprint: lem-sf-open-projection-roos-completion). -/
def RoosComparison.derived (F : A ⥤ B) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (r : RoosComparison F) (T : ℕᵒᵖ ⥤ CochainComplex A ℤ) :
    F.mapDerivedCategory.obj (DerivedCategory.Q.obj (integralOperationsRoos T)) ≅
      DerivedCategory.Q.obj (integralOperationsRoos ((onTowers F).obj T)) :=
  F.mapDerivedCategoryFactors.app (integralOperationsRoos T) ≪≫
    DerivedCategory.Q.mapIso (r.iso.app T)
end Roos

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
  (o : IntegralOpenReduction.Operations l E j)

/-- The source pair insertion for the open projection formula.
Source: blueprint open factor (blueprint: lem-sf-open-projection-roos-completion). -/
abbrev leftInputs := (IntegralOpenReduction.shriek l E j o).prod
  (𝟭 (DerivedCategory (scalarReductionSource l E X)))

/-- The target pair insertion, with actual exact restriction.
Source: blueprint open factor (blueprint: lem-sf-open-projection-roos-completion). -/
abbrev rightInputs := (𝟭 (DerivedCategory (scalarReductionSource l E U))).prod
  (IntegralOpenReduction.star l E j o)

/-- Inclusion of precisely the two bounded constructible integral domains.
Source: Bhatt--Scholze 6.5.8 (blueprint: lem-sf-open-projection-roos-completion). -/
abbrev pairs := (sfIntegralConstructible l E U).ι.prod (sfIntegralConstructible l E X).ι

/-- The actual completed source functor on the stated constructible domain.
Source: Bhatt--Scholze 3.4.10 (blueprint: lem-sf-open-projection-roos-completion). -/
abbrev completedLeft := pairs l E (U := U) (X := X) ⋙ leftInputs l E j o ⋙
  integralCompletedTensor l E X

/-- The actual completed tensor on U, before its extension.
Source: Bhatt--Scholze 3.4.10 (blueprint: lem-sf-open-projection-roos-completion). -/
abbrev completedInside := pairs l E (U := U) (X := X) ⋙ rightInputs l E j o ⋙
  integralCompletedTensor l E U

/-- The actual completed target functor on the stated constructible domain.
Source: Bhatt--Scholze 3.4.10 (blueprint: lem-sf-open-projection-roos-completion). -/
abbrev completedRight := completedInside l E j o ⋙ IntegralOpenReduction.shriek l E j o

attribute [local irreducible] integralOperationsTensorTowerFunctor
  coefficientTotalTensor integralOperationsTensorLevel
  completedIntegralCommRingSheafUnrestricted completedIntegralCoefficientSheafUnrestricted
  unrestrictedIntegralComplexFunctor scalarReductionExistence unrestrictedIntegralReductionExistence

variable
  (SX : CoefficientDerivedSystemCalculus l E X)
  (SU : CoefficientDerivedSystemCalculus l E U)
  (AX : OpenSemilinearTensor.OrdinaryReduction l E X)
  (AU : OpenSemilinearTensor.OrdinaryReduction l E U)
  (st : IntegralOpenReduction.TensorComparison l E j o)
  (m : OpenSemilinearTensor.Comparison l E j o SX SU AX AU st)
  (c : IntegralOpenReduction.Comparison l E j o SX SU st)
  (q : OpenTensorQuotient.Comparison l E j o SX SU AX AU st m c)

set_option maxHeartbeats 800000 in
-- The predicate retains simultaneous natural transformations and all representative equations.
/-- The completion of the specified augmented square. Every isomorphism is pinned
by chain or unit equations, including restriction and every strict finite reduction.
`ordinary` is gamma^B, `gamma` is Gamma, `extension` is lambda_j.
Source: Stacks 09BP; Bhatt--Scholze 6.5.5, 6.5.8
(blueprint: lem-sf-open-projection-roos-completion). -/
def CompletionData
    [restrictionLimits : PreservesFiniteLimits (IntegralOpenReduction.restriction l E j o)]
    [restrictionColimits : PreservesFiniteColimits (IntegralOpenReduction.restriction l E j o)] :
    Prop :=
    ∃ (extension : RoosComparison (IntegralOpenReduction.extension l E j o)),
    ∃ (restriction : RoosComparison (IntegralOpenReduction.restriction l E j o)),
    ∃ (moduleUnit : 𝟭 (scalarReductionSource l E U) ≅
    IntegralOpenReduction.extension l E j o ⋙ IntegralOpenReduction.restriction l E j o),
    ∃ (_moduleUnit_hom : moduleUnit.hom = (IntegralOpenReduction.ordinaryAdjunction l E j o).unit),
    ∃ (unit : 𝟭 (DerivedCategory (scalarReductionSource l E U)) ≅
    IntegralOpenReduction.shriek l E j o ⋙ IntegralOpenReduction.star l E j o),
    ∃ (_unit_hom : unit.hom = (IntegralOpenReduction.openAdjunction l E j o).unit),
    ∃ (flat : ∀ (W : Scheme.{u}) (P : CochainComplex (scalarReductionSource l E W) ℤ),
    integralOperationsGoodComplex l E W P →
      proEtaleFlatRepresentatives W (completedIntegralCommRingSheafUnrestricted l E W) P),
    ∃ (extendGood : ∀ (P : CochainComplex (scalarReductionSource l E U) ℤ),
    integralOperationsGoodComplex l E U P → integralOperationsGoodComplex l E X
      ((OpenSemilinearTensor.extensionComplex l E j o).obj P)),
    ∃ (restrictGood : ∀ (P : CochainComplex (scalarReductionSource l E X) ℤ),
    integralOperationsGoodComplex l E X P → integralOperationsGoodComplex l E U
      ((OpenSemilinearTensor.restrictionComplex l E j o).obj P)),
    ∃ (ordinary : leftInputs l E j o ⋙ q.tensorX.ordinary.tensor ≅
    rightInputs l E j o ⋙ q.tensorU.ordinary.tensor ⋙ IntegralOpenReduction.shriek l E j o),
    ∃ (_ordinary_representative : ∀ (Q : CochainComplex (scalarReductionSource l E U) ℤ)
      (F : CochainComplex (scalarReductionSource l E X) ℤ)
      (hQ : integralOperationsGoodComplex l E U Q)
      (hF : integralOperationsGoodComplex l E X F),
    HEq (q.tensorX.ordinary.representative.hom.app
        (⟨(OpenSemilinearTensor.extensionComplex l E j o).obj Q,
          flat X _ (extendGood Q hQ)⟩, ⟨F, flat X F hF⟩) ≫
      q.tensorX.ordinary.tensor.map (Prod.mkHom
        ((IntegralOpenReduction.extension l E j o).mapDerivedCategoryFactors.inv.app Q) (𝟙 _)) ≫
      ordinary.hom.app (DerivedCategory.Q.obj Q, DerivedCategory.Q.obj F) ≫
      (IntegralOpenReduction.shriek l E j o).map
        (q.tensorU.ordinary.tensor.map (Prod.mkHom (𝟙 _)
          ((IntegralOpenReduction.restriction l E j o).mapDerivedCategoryFactors.hom.app F))) ≫
      (IntegralOpenReduction.shriek l E j o).map
        (q.tensorU.ordinary.representative.inv.app
          (⟨Q, flat U Q hQ⟩, ⟨(OpenSemilinearTensor.restrictionComplex l E j o).obj F,
            flat U _ (restrictGood F hF)⟩)) ≫
      (IntegralOpenReduction.extension l E j o).mapDerivedCategoryFactors.hom.app
        ((constructibleTensorTotal l E U).obj
          (Q, (OpenSemilinearTensor.restrictionComplex l E j o).obj F)))
      (DerivedCategory.Q.map (m.totalComparison.chain Q F).hom)),
    ∃ (gamma : completedLeft l E j o ≅ completedRight l E j o),
    ∃ (_units : ∀ K : sfIntegralConstructibleCategory l E U × sfIntegralConstructibleCategory l E X,
    (q.tensorX.chi l E).app ((leftInputs l E j o).obj (K.1.obj, K.2.obj)) ≫
        gamma.hom.app K =
      ordinary.hom.app (K.1.obj, K.2.obj) ≫
        (IntegralOpenReduction.shriek l E j o).map
          ((q.tensorU.chi l E).app ((rightInputs l E j o).obj (K.1.obj, K.2.obj)))),
    ∃ (_invertibleUnits : ∀ K :
      sfIntegralConstructibleCategory l E U × sfIntegralConstructibleCategory l E X,
    IsIso ((q.tensorX.chi l E).app ((leftInputs l E j o).obj (K.1.obj, K.2.obj))) ∧
      IsIso ((q.tensorU.chi l E).app ((rightInputs l E j o).obj (K.1.obj, K.2.obj)))),
    ∃ (_representative : ∀ (Q : CochainComplex (scalarReductionSource l E U) ℤ)
      (F : CochainComplex (scalarReductionSource l E X) ℤ)
      (hQ : integralOperationsGoodComplex l E U Q)
      (hF : integralOperationsGoodComplex l E X F)
      (hK : sfIntegralConstructible l E U (DerivedCategory.Q.obj Q))
      (hP : sfIntegralConstructible l E X (DerivedCategory.Q.obj F))
      (z : OpenTensorQuotient.StrictSquare l E j o m.totalComparison q.scalar st
        q.strictScalar Q F),
    OpenTensorQuotient.RoosNormalization l E X q.tensorX
      ((OpenSemilinearTensor.extensionComplex l E j o).obj Q) F z.upper →
    OpenTensorQuotient.RoosNormalization l E U q.tensorU Q
      ((OpenSemilinearTensor.restrictionComplex l E j o).obj F) z.lower →
    gamma.hom.app (⟨DerivedCategory.Q.obj Q, hK⟩, ⟨DerivedCategory.Q.obj F, hP⟩) ≫
      (IntegralOpenReduction.shriek l E j o).map
        ((integralCompletedTensor l E U).map (Prod.mkHom (𝟙 _)
          ((IntegralOpenReduction.restriction l E j o).mapDerivedCategoryFactors.hom.app F))) ≫
      (IntegralOpenReduction.shriek l E j o).map
        ((integralCompletedTensorComparison l E U).hom.app
          (⟨Q, hQ⟩, ⟨(OpenSemilinearTensor.restrictionComplex l E j o).obj F,
            restrictGood F hF⟩)) ≫
      (extension.derived (IntegralOpenReduction.extension l E j o)
        ((integralOperationsTensorTowerFunctor l E U).obj
          (Q, (OpenSemilinearTensor.restrictionComplex l E j o).obj F))).hom =
      (integralCompletedTensor l E X).map (Prod.mkHom
        ((IntegralOpenReduction.extension l E j o).mapDerivedCategoryFactors.hom.app Q) (𝟙 _)) ≫
      (integralCompletedTensorComparison l E X).hom.app
        (⟨(OpenSemilinearTensor.extensionComplex l E j o).obj Q, extendGood Q hQ⟩, ⟨F, hF⟩) ≫
      DerivedCategory.Q.map (integralOperationsRoosMap z.gamma.hom)),
    ∃ (tensorRestriction : completedLeft l E j o ⋙ IntegralOpenReduction.star l E j o ≅
    completedInside l E j o),
    ∃ (_restriction_identity : ∀ K :
      sfIntegralConstructibleCategory l E U × sfIntegralConstructibleCategory l E X,
    (IntegralOpenReduction.star l E j o).map (gamma.hom.app K) ≫
        unit.inv.app ((completedInside l E j o).obj K) = tensorRestriction.hom.app K),
    ∀ (Q : CochainComplex (scalarReductionSource l E U) ℤ)
      (F : CochainComplex (scalarReductionSource l E X) ℤ)
      (hQ : integralOperationsGoodComplex l E U Q)
      (hF : integralOperationsGoodComplex l E X F)
      (hK : sfIntegralConstructible l E U (DerivedCategory.Q.obj Q))
      (hP : sfIntegralConstructible l E X (DerivedCategory.Q.obj F))
      (z : OpenTensorQuotient.StrictSquare l E j o m.totalComparison q.scalar st
        q.strictScalar Q F),
    OpenTensorQuotient.RoosNormalization l E X q.tensorX
      ((OpenSemilinearTensor.extensionComplex l E j o).obj Q) F z.upper →
    OpenTensorQuotient.RoosNormalization l E U q.tensorU Q
      ((OpenSemilinearTensor.restrictionComplex l E j o).obj F) z.lower →
    ∃ delta : (onTowers (IntegralOpenReduction.restriction l E j o)).obj
        ((integralOperationsTensorTowerFunctor l E X).obj
          ((OpenSemilinearTensor.extensionComplex l E j o).obj Q, F)) ≅
      (integralOperationsTensorTowerFunctor l E U).obj
        (Q, (OpenSemilinearTensor.restrictionComplex l E j o).obj F),
    (∀ (n : ℕ) (i : ℤ),
      ((delta.hom.app (op n)).f i) =
        (IntegralOpenReduction.restriction l E j o).map ((z.gamma.hom.app (op n)).f i) ≫
          moduleUnit.inv.app
            ((((integralOperationsTensorTowerFunctor l E U).obj
              (Q, (OpenSemilinearTensor.restrictionComplex l E j o).obj F)).obj (op n)).X i)) ∧
    tensorRestriction.hom.app
        (⟨DerivedCategory.Q.obj Q, hK⟩, ⟨DerivedCategory.Q.obj F, hP⟩) ≫
      (integralCompletedTensor l E U).map (Prod.mkHom (𝟙 _)
        ((IntegralOpenReduction.restriction l E j o).mapDerivedCategoryFactors.hom.app F)) ≫
      (integralCompletedTensorComparison l E U).hom.app
        (⟨Q, hQ⟩, ⟨(OpenSemilinearTensor.restrictionComplex l E j o).obj F,
          restrictGood F hF⟩) =
      (IntegralOpenReduction.star l E j o).map
        ((integralCompletedTensor l E X).map (Prod.mkHom
          ((IntegralOpenReduction.extension l E j o).mapDerivedCategoryFactors.hom.app Q)
          (𝟙 _)) ≫
          (integralCompletedTensorComparison l E X).hom.app
            (⟨(OpenSemilinearTensor.extensionComplex l E j o).obj Q, extendGood Q hQ⟩,
              ⟨F, hF⟩)) ≫
      (restriction.derived (IntegralOpenReduction.restriction l E j o)
        ((integralOperationsTensorTowerFunctor l E X).obj
          ((OpenSemilinearTensor.extensionComplex l E j o).obj Q, F))).hom ≫
      DerivedCategory.Q.map (integralOperationsRoosMap delta.hom)

/-- Exactness together with the specified comparison predicate. The exactness
witnesses are supplied by the conclusion, not imposed as additional hypotheses.
Source: Stacks 09BP (blueprint: lem-sf-open-projection-roos-completion). -/
def Completion : Prop :=
  ∃ (hL : PreservesFiniteLimits (IntegralOpenReduction.restriction l E j o))
    (hC : PreservesFiniteColimits (IntegralOpenReduction.restriction l E j o)),
  CompletionData l E j o SX SU AX AU st m c q
    (restrictionLimits := hL) (restrictionColimits := hC)

attribute [local irreducible] CompletionData Completion

/-- The augmented open projection square has the specified Roos completion and actual
completion-unit normalization, naturally on the integral constructible domain.

Source: Stacks 09BP; Bhatt--Scholze 6.5.5, 6.5.8, pp.49--50; the open-factor paragraph
of prop-sf-pf-coherence (blueprint: lem-sf-open-projection-roos-completion).

Proof:
1. Finite type over the field makes U and X Noetherian, hence qcqs. The structure
map of X is quasi-separated, so the Nagata quasi-compactness lemma gives qc j.
The prime l is invertible. No separatedness over k is required.
2. Apply lem-pur-site-restriction-module-adjunction-exact and
lem-cbc-ringed-open-extension-products to the completed ring. Countable products
are exact by lem-weil-proetale-countable-products-exact. The normalized comparison
lem-cbc-exact-product-functor-strict-limit gives extension, its two coordinate
identities and preservation of every strict augmentation.
3. Apply the Roos functor to the single strict isomorphism gamma of
lem-sf-open-tensor-quotient-augmentation and compose with inverse lambda. Descend
through the recorded completed-tensor comparisons. This gives gamma and naturality.
4. The strict augmentation square is equal before localization. In signed Roos
coordinates both routes have the same first component and zero second component.
lem-weil-strict-roos-comparison and the augmentation clause of the exact-product
comparison therefore give equality of the actual induced derived maps.
5. The two augmentations are the actual chi maps by
lem-fix-constructible-tensor-completion and def-sf-tensor-completion-comparison.
Cancel lambda to obtain units, the displayed completion square.
6. Open extension and restriction preserve integral constructibility by the quotient
augmentation theorem. Apply constructible tensor completion to both pairs to get
invertibleUnits, without any finite-Tor condition over the quotient rings.
7. Restriction is exact and preserves the sectionwise products and quotient rings.
The same exact-product comparison gives restriction and its augmentation clause.
8. The canonical open units are invertible. At every finite level restriction of
the ordinary tensor map is identity through those units. Consequently delta is
the restriction comparison for the same strict quotient systems. On both Roos
summands the restricted lambda is the product of the units, as follows after
each product projection. The representative equations give restriction_identity.
9. Inverting the two actual chi maps expresses gamma as their conjugate of the
ordinary map. Its strict finite reductions are exactly z.gamma, with the given
quotient transitions and augmentation square. Thus this supplies precisely the
integral open tensor component requested in def-exchange-projection; it asserts
none of that definition's independent proper or other coefficient-stage data. -/
theorem openProjectionRoosCompletion (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    [U.Over (Spec (.of D.k))] [X.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (U ↘ Spec (.of D.k))] [QuasiCompact (U ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [j.IsOver (Spec (.of D.k))] :
    Completion l E j o SX SU AX AU st m c q := by
  sorry

end WeilConjectures.OpenProjectionRoos
