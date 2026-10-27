/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q70
-/
module

public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients
public import Sheaf.Paper.CompletedIntegralConstantMapOfUniverses
public import Sheaf.Paper.CompletedCondensedCoefficients
public import Sheaf.Paper.SfCompletedScalarComparisonData
public import Sheaf.Paper.LocallyFiniteAdicConstructibleRealization
public import Sheaf.Paper.RationalScalarBalancedLocalization
public import Sheaf.Paper.BoundedConstructibleTower
public import Sheaf.Paper.SfScalarExtensionComposition
public import Sheaf.AlgebraicGeometry.FiniteLocallyClosedStratification
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree

import Sheaf.NumberTheory.Padics.ExtensionIntegersDvr
import Sheaf.CategoryTheory.InternalSectionTensorComparison
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit
import Sheaf.AlgebraicGeometry.CondensedFieldLfpLocalTriviality
import Sheaf.Paper.CondensedQbarLfpLocalTriviality
import Sheaf.Algebra.Homology.OrdinaryDerivedChangeOfRings
import Sheaf.AlgebraicGeometry.FiniteTypeNoetherianSpectrum
import Sheaf.Paper.CompletedScalarShift

/-! # Exact descent of an adic realization cocone

Source: Bhatt--Scholze, Proposition 6.8.14; Hemo--Richarz--Scholbach,
Proposition 5.2 and Lemma 7.9 (blueprint: lem-sf-adic-common-stage-descent-equivalence).

Finite coefficient rings are the continuous-function presentation of the completed
integral localization. The algebraic-closure ring is the native locally finite
continuous ring in its ordinary section-module presentation. All coefficient maps
retain their specified residue and pointwise function normalizations.

## Main statements

* `commonStageDescentEquivalence`: exact descent with the explicit object, arrow,
  Hom-colimit, essential image, and finite-stage shift formulas.
* The coefficient and shift helpers retain the uniquely normalized constructions
  needed to type those formulas in the ordinary section-module category.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
attribute [local irreducible] HasDerivedCategory.standard

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale
open scoped Obj

namespace WeilConjectures.SfAdicCommonStageDescent

variable (l : ℕ) [Fact l.Prime] (T : Scheme.{u})

/-- The small model of one actual finite subfield, as in the recorded stage diagram.
Source: common-field convention (blueprint: lem-sf-adic-common-stage-descent-equivalence). -/
abbrev coefficient (E : PadicAlgCl.FiniteIntermediateField l) :=
  AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E

/-- Continuous finite coefficients; BS 6.8.2 identifies these with B_E[1/pi_E].
Source: BS 6.8.1--6.8.2
(blueprint: lem-sf-adic-common-stage-descent-equivalence). -/
abbrev finiteRing (E : PadicAlgCl.FiniteIntermediateField l) :=
  rationalCoefficientSheaf l T (coefficient.{u} l E)

/-- Cache the inherited raw localized coefficient action at the recorded stage alias.
Source: raw localization convention
(blueprint: lem-sf-adic-common-stage-descent-equivalence). -/
noncomputable instance finiteStageLinear (E : PadicAlgCl.FiniteIntermediateField l) :
    Linear (Localization.Away (Padic.coefficientExtensionUniformizer l (coefficient.{u} l E)))
      (GeneralAlgebraicallyClosedCoefficients.Stage l (PadicAlgCl l) T E) :=
  ScalarLocalization.linear (Padic.coefficientExtensionIntegers l (coefficient.{u} l E))
    (sfIntegralConstructibleCategory l (coefficient.{u} l E) T)
    (Padic.coefficientExtensionUniformizer l (coefficient.{u} l E))

/-- The field action on modules is the constant-section action already used in realization.
Source: BS 6.8.1; rationalModuleConstantMap
(blueprint: lem-sf-adic-common-stage-descent-equivalence). -/
def fieldScalarSections (E : PadicAlgCl.FiniteIntermediateField l) :
    coefficient.{u} l E →+* RingCat.sectionsSubring
      ((finiteRing l T E).obj ⋙ forget₂ CommRingCat RingCat) :=
  letI := coefficientExtensionNormedField l (coefficient.{u} l E)
  { toFun := fun a ↦ ⟨fun _ ↦ ContinuousMap.const _ (ULift.up a), fun _ ↦ rfl⟩
    map_one' := rfl
    map_mul' := fun _ _ ↦ rfl
    map_zero' := rfl
    map_add' := fun _ _ ↦ rfl }

/-- Restrict the existing global-section action along constant continuous coefficients.
Source: BS 6.8.1; Stacks 03DA
(blueprint: lem-sf-adic-common-stage-descent-equivalence). -/
noncomputable instance finiteModuleLinear (E : PadicAlgCl.FiniteIntermediateField l) :
    Linear (coefficient.{u} l E) (pbcModules T (finiteRing l T E)) :=
  letI : Linear (RingCat.sectionsSubring
      ((finiteRing l T E).obj ⋙ forget₂ CommRingCat RingCat))
      (pbcModules T (finiteRing l T E)) :=
    SheafOfModules.homLinear (finiteRing l T E).obj
      (((adicLisseForget T).obj (finiteRing l T E)).property)
  { homModule := fun M N ↦ Module.compHom (M ⟶ N) (fieldScalarSections l T E)
    smul_comp := fun M N P a f g ↦
      Linear.smul_comp M N P (fieldScalarSections l T E a) f g
    comp_smul := fun M N P f a g ↦
      Linear.comp_smul M N P f (fieldScalarSections l T E a) g }

/-- The ordinary derived category inherits the specified pointwise constant-field action.
Source: BS 6.8.1 (blueprint: lem-sf-adic-common-stage-descent-equivalence). -/
noncomputable instance finiteDerivedLinear (E : PadicAlgCl.FiniteIntermediateField l) :
    Linear (coefficient.{u} l E) (DerivedCategory (pbcModules T (finiteRing l T E))) :=
  inferInstance

/-- The native locally finite function ring has commutative pointwise multiplication.
Source: BS 6.8.1--6.8.2
(blueprint: lem-sf-adic-common-stage-descent-equivalence).
Proof: multiplication and the unit are pointwise on finite-subextension-valued functions.
They commute on every section; forgetting the constant-field action preserves this equation. -/
theorem closure_commutative : IsCommMonObj (LocallyFiniteAdicRealization.abRing l T) := by
  sorry

attribute [instance] closure_commutative

/-- The actual locally finite continuous algebraic-closure coefficient ring.
Source: BS 6.8.1--6.8.2
(blueprint: lem-sf-adic-common-stage-descent-equivalence). -/
abbrev closureRing := LocallyFiniteAdicRealization.ringSheaf l T

/-- All the completion/localization identifications are uniquely fixed on residues and functions.
Source: BS Lemma 6.8.2; the normalized coefficient presentation of the recorded realization
(blueprint: lem-sf-adic-common-stage-descent-equivalence).
Proof: continuous integral functions are the inverse limit of their finite residues.
The finite constant sheaf agrees with continuous finite-valued functions, fixed on constants.
Localization sends an integral function divided by a uniformizer power to that quotient.
Finite-field inclusion acts pointwise. These formulas give the presentation. Joint monicity
of the inverse-limit projections, the localization universal property, and sheaf generation
by finite constants prove uniqueness of all its fields. -/
theorem presentation_existsUnique (E : PadicAlgCl.FiniteIntermediateField l) :
    ∃! C : LocallyFiniteAdicRealization.CoefficientPresentation l T
      (coefficient.{u} l E) (LocallyFiniteAdicRealization.embedding l E),
      C.integralInclusion = integralRationalCoefficientMap l (coefficient.{u} l E) T := by
  sorry

/-- The normalized coefficient presentation, determined by its residue and function formulas.
Source: BS 6.8.2 (blueprint: lem-sf-adic-common-stage-descent-equivalence). -/
def presentation (E : PadicAlgCl.FiniteIntermediateField l) :=
  (presentation_existsUnique l T E).exists.choose

/-- The structural map from completed integral to continuous rational coefficients.
Source: BS 6.8.2 (blueprint: lem-sf-adic-common-stage-descent-equivalence). -/
def integralMap (E : PadicAlgCl.FiniteIntermediateField l) :
    completedIntegralCommRingSheafUnrestricted l (coefficient.{u} l E) T ⟶ finiteRing l T E :=
  (presentation l T E).integral.inv ≫ (presentation l T E).integralInclusion

/-- Finite scalar inclusion is actual postcomposition by the recorded field embedding.
Source: BS 6.8.14 (blueprint: lem-sf-adic-common-stage-descent-equivalence). -/
def finiteMap {E F : PadicAlgCl.FiniteIntermediateField l} (h : E ≤ F) :
    finiteRing l T E ⟶ finiteRing l T F :=
  rationalBalancedCoefficient l (coefficient.{u} l E) (coefficient.{u} l F)
    (AlgebraicallyClosedCoefficients.coefficientInclusion l (PadicAlgCl l) E F h) T

/-- The finite-subfield leg into the locally finite closure ring, fixed pointwise.
Source: BS 6.8.14 (blueprint: lem-sf-adic-common-stage-descent-equivalence). -/
def closureMap (E : PadicAlgCl.FiniteIntermediateField l) :
    finiteRing l T E ⟶ closureRing l T :=
  (presentation l T E).rationalInclusion

/-- The coefficient square for the actual completed scalar extension.
Source: BS 6.8.2 (blueprint: lem-sf-adic-common-stage-descent-equivalence).
Proof: compose with all finite residue projections. Both maps apply the same field
embedding to the residue of the same function. The limit projections determine the map. -/
theorem integralMap_comp {E F : PadicAlgCl.FiniteIntermediateField l} (h : E ≤ F) :
    completedIntegralScalarCoefficientMap l (coefficient.{u} l E) (coefficient.{u} l F)
        (AlgebraicallyClosedCoefficients.coefficientInclusion l (PadicAlgCl l) E F h) T ≫
      integralMap l T F = integralMap l T E ≫ finiteMap l T h := by
  sorry

/-- Finite and closure scalar inclusions form their specified cocone.
Source: BS 6.8.14 (blueprint: lem-sf-adic-common-stage-descent-equivalence).
Proof: every composite is postcomposition of functions by the same field inclusion. -/
theorem closureMap_comp {E F : PadicAlgCl.FiniteIntermediateField l} (h : E ≤ F) :
    finiteMap l T h ≫ closureMap l T F = closureMap l T E := by
  sorry

/-- Tower equation for the actual finite scalar maps.
Source: BS 6.8.14 (blueprint: lem-sf-adic-common-stage-descent-equivalence).
Proof: postcomposition of continuous functions respects composition of field embeddings. -/
theorem finiteMap_comp {E F H : PadicAlgCl.FiniteIntermediateField l}
    (h : E ≤ F) (k : F ≤ H) :
    finiteMap l T h ≫ finiteMap l T k = finiteMap l T (h.trans k) := by
  sorry

/-- The identity coefficient embedding acts as the identity on every section.
Source: BS 6.8.14 (blueprint: lem-sf-adic-common-stage-descent-equivalence).
Proof: the coefficient embedding at a repeated field is identity, as is postcomposition. -/
theorem finiteMap_id (E : PadicAlgCl.FiniteIntermediateField l) :
    finiteMap l T (E := E) le_rfl = 𝟙 (finiteRing l T E) := by
  sorry

/-- Normalize derived scalar shift on K-flat complexes by its universal computation counit.
Source: Stacks 011G, 06YT; BS 6.8.14
(blueprint: lem-sf-adic-common-stage-descent-equivalence). -/
def scalarShiftNormalized
    {A B : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (φ : A ⟶ B)
    (c : (pbcDerivedExtend φ).CommShift ℤ) : Prop :=
  ∀ (P : CochainComplex (pbcModules T A) ℤ)
    (_ : CochainComplex.IsKFlatIndependentCoefficients (R := A) P) (m : ℤ),
    (Functor.commShiftIso (pbcDerivedExtend φ) (self := c) m).hom.app
        (DerivedCategory.Q.obj P) ≫ (pbcComplexCounit φ P)⟦m⟧' =
      (pbcDerivedExtend φ).map ((DerivedCategory.Q.commShiftIso m).inv.app P) ≫
        pbcComplexCounit φ (P⟦m⟧) ≫
        DerivedCategory.Q.map (((pbcExtend φ).mapCochainComplexShiftIso m).hom.app P) ≫
        (DerivedCategory.Q.commShiftIso m).hom.app ((pbcExtend φ).mapHomologicalComplex _ |>.obj P)

/-- The universal K-flat counit determines exactly one compatible shift comparison.
Source: Stacks 011G, 06YT; BS 6.8.14
(blueprint: lem-sf-adic-common-stage-descent-equivalence).
Proof: derive the degreewise tensor reindexing. On K-flat complexes the counit is
invertible, so the displayed square uniquely determines the shift component.
Every derived object has a K-flat representative. Naturality and the zero and addition
laws descend from those of the cochain tensor reindexing. -/
theorem scalarShift_existsUnique
    {A B : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (φ : A ⟶ B) :
    ∃! c : (pbcDerivedExtend φ).CommShift ℤ, scalarShiftNormalized T φ c := by
  sorry

/-- The derived tensor shift fixed by its K-flat counit, with no arbitrary shift choices.
Source: Stacks 06YT (blueprint: lem-sf-adic-common-stage-descent-equivalence). -/
@[instance_reducible] noncomputable def scalarCommShift
    {A B : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (φ : A ⟶ B) :
    (pbcDerivedExtend φ).CommShift ℤ :=
  (scalarShift_existsUnique T φ).exists.choose

attribute [local instance] scalarCommShift

/-- The bounded stratified locally finite free condition in the ordinary derived category.
The finite stratification may depend on the cohomological degree; every stratum has
its own pro-etale local finite free models, including rank zero.
Source: BS Definition 6.8.8; HRS Proposition 5.2 and Lemma 7.9
(blueprint: lem-sf-adic-common-stage-descent-equivalence). -/
def constructible (A : Sheaf (ProEt.topology T) CommRingCat.{u + 1}) :
    ObjectProperty (DerivedCategory (pbcModules T A)) := fun K ↦
  (∃ a b : ℤ, K.IsGE a ∧ K.IsLE b) ∧
    ∀ n : ℤ, ∃ s : Scheme.FiniteLocallyClosedStratification T,
      ∀ i : Fin s.n,
        ((proEtaleModuleInverseImage (s.immersion i) A).obj
          ((DerivedCategory.homologyFunctor _ n).obj K)).IsFiniteLocallyFree

/-- The functors G_E = R_T tensor over E_T with J_E.
Source: BS 6.8.14; HRS Lemma 7.9
(blueprint: lem-sf-adic-common-stage-descent-equivalence). -/
def extended
    (J : ∀ E : PadicAlgCl.FiniteIntermediateField l,
      GeneralAlgebraicallyClosedCoefficients.Stage l (PadicAlgCl l) T E ⥤
        DerivedCategory (pbcModules T (finiteRing l T E)))
    (E : PadicAlgCl.FiniteIntermediateField l) :=
  J E ⋙ pbcDerivedExtend (closureMap l T E)

/-- The shift of G_E is the composite of J_E's shift and the normalized tensor shift.
Source: BS 6.8.14 (blueprint: lem-sf-adic-common-stage-descent-equivalence). -/
noncomputable instance extendedCommShift
    (J : ∀ E : PadicAlgCl.FiniteIntermediateField l,
      GeneralAlgebraicallyClosedCoefficients.Stage l (PadicAlgCl l) T E ⥤
        DerivedCategory (pbcModules T (finiteRing l T E)))
    [∀ E, (J E).CommShift ℤ] (E : PadicAlgCl.FiniteIntermediateField l) :
    (extended l T J E).CommShift ℤ :=
  inferInstanceAs ((J E ⋙ pbcDerivedExtend (closureMap l T E)).CommShift ℤ)

/-- The specified comparison gamma is j followed by balanced multiplication.
Source: node proof step 4, BS 6.8.14; HRS Lemma 7.9
(blueprint: lem-sf-adic-common-stage-descent-equivalence). -/
def gamma
    (J : ∀ E : PadicAlgCl.FiniteIntermediateField l,
      GeneralAlgebraicallyClosedCoefficients.Stage l (PadicAlgCl l) T E ⥤
        DerivedCategory (pbcModules T (finiteRing l T E)))
    (j : ∀ (E F : PadicAlgCl.FiniteIntermediateField l) (h : E ≤ F),
      GeneralAlgebraicallyClosedCoefficients.stageTransition l (PadicAlgCl l) T E F h ⋙
        J F ≅ J E ⋙ pbcDerivedExtend (finiteMap l T h))
    (E F : PadicAlgCl.FiniteIntermediateField l) (h : E ≤ F)
    (K : GeneralAlgebraicallyClosedCoefficients.Stage l (PadicAlgCl l) T E) :
    (extended l T J F).obj
        ((GeneralAlgebraicallyClosedCoefficients.stageTransition l (PadicAlgCl l) T E F h).obj
          K) ≅ (extended l T J E).obj K :=
  (pbcDerivedExtend (closureMap l T F)).mapIso ((j E F h).app K) ≪≫
    pbcReductionNormalization (finiteMap l T h) (closureMap l T F) (closureMap l T E)
      (closureMap_comp l T h) ((J E).obj K)

/-- The cocone identity and tower equations, using the actual source scalar comparisons.
Source: node hypotheses and proof step 4; BS 6.8.14, HRS Lemma 7.9
(blueprint: lem-sf-adic-common-stage-descent-equivalence). -/
def coherent
    (J : ∀ E : PadicAlgCl.FiniteIntermediateField l,
      GeneralAlgebraicallyClosedCoefficients.Stage l (PadicAlgCl l) T E ⥤
        DerivedCategory (pbcModules T (finiteRing l T E)))
    (j : ∀ (E F : PadicAlgCl.FiniteIntermediateField l) (h : E ≤ F),
      GeneralAlgebraicallyClosedCoefficients.stageTransition l (PadicAlgCl l) T E F h ⋙
        J F ≅ J E ⋙ pbcDerivedExtend (finiteMap l T h)) : Prop :=
  (∀ (E : PadicAlgCl.FiniteIntermediateField l)
    (K : GeneralAlgebraicallyClosedCoefficients.Stage l (PadicAlgCl l) T E),
    HEq (gamma l T J j E E le_rfl K).hom
      ((extended l T J E).map
        ((GeneralAlgebraicallyClosedCoefficients.unitor l (PadicAlgCl l) T E).hom.app K))) ∧
  ∀ (E F H : PadicAlgCl.FiniteIntermediateField l) (h : E ≤ F) (k : F ≤ H)
    (K : GeneralAlgebraicallyClosedCoefficients.Stage l (PadicAlgCl l) T E),
    (extended l T J H).map
        (((GeneralAlgebraicallyClosedCoefficients.stageSystem l (PadicAlgCl l) T).assoc h k).hom.app
          K) ≫ (gamma l T J j E H (h.trans k) K).hom =
      (gamma l T J j F H k
        ((GeneralAlgebraicallyClosedCoefficients.stageTransition l (PadicAlgCl l) T E F h).obj
          K)).hom ≫ (gamma l T J j E F h K).hom

/-- The scalar comparison is the quotient-completion comparison followed by balanced tensor.
The equation is imposed on integral objects; raw localization has the same objects and
extends it uniquely over all fractions.
Source: BS 6.8.2, 6.8.14; node hypothesis specifying j
(blueprint: lem-sf-adic-common-stage-descent-equivalence). -/
def scalarNormalized
    (J : ∀ E : PadicAlgCl.FiniteIntermediateField l,
      GeneralAlgebraicallyClosedCoefficients.Stage l (PadicAlgCl l) T E ⥤
        DerivedCategory (pbcModules T (finiteRing l T E)))
    (α : ∀ E : PadicAlgCl.FiniteIntermediateField l,
      sfRationalConstructibleLocalization l (coefficient.{u} l E) T ⋙ J E ≅
        ObjectProperty.ι (sfIntegralConstructible l (coefficient.{u} l E) T) ⋙
          pbcDerivedExtend (integralMap l T E))
    (j : ∀ (E F : PadicAlgCl.FiniteIntermediateField l) (h : E ≤ F),
      GeneralAlgebraicallyClosedCoefficients.stageTransition l (PadicAlgCl l) T E F h ⋙
        J F ≅ J E ⋙ pbcDerivedExtend (finiteMap l T h)) : Prop :=
  ∀ (E F : PadicAlgCl.FiniteIntermediateField l) (h : E ≤ F)
    (K : sfIntegralConstructibleCategory l (coefficient.{u} l E) T),
    HEq
      ((j E F h).hom.app
          ((sfRationalConstructibleLocalization l (coefficient.{u} l E) T).obj K) ≫
        (pbcDerivedExtend (finiteMap l T h)).map ((α E).hom.app K) ≫
        (pbcReductionNormalization (integralMap l T E) (finiteMap l T h)
          (integralMap l T E ≫ finiteMap l T h) rfl K.obj).hom ≫
        (pbcReductionNormalization
          (completedIntegralScalarCoefficientMap l (coefficient.{u} l E) (coefficient.{u} l F)
            (AlgebraicallyClosedCoefficients.coefficientInclusion l (PadicAlgCl l) E F h) T)
          (integralMap l T F) (integralMap l T E ≫ finiteMap l T h)
          (integralMap_comp l T h) K.obj).inv ≫
        (pbcDerivedExtend (integralMap l T F)).map
          ((completedIntegralScalarComparison l (coefficient.{u} l E) (coefficient.{u} l F)
            (AlgebraicallyClosedCoefficients.coefficientInclusion l (PadicAlgCl l) E F h)
            T).app K.obj))
      ((α F).hom.app
        ((GeneralAlgebraicallyClosedCoefficients.integralTransition l (PadicAlgCl l) T
          E F h).obj K))

/-- The finite tower equation with the actual completed associator and balanced multiplication.
Source: BS 6.8.14; node identity/tower hypotheses
(blueprint: lem-sf-adic-common-stage-descent-equivalence). -/
def finiteCoherent
    (J : ∀ E : PadicAlgCl.FiniteIntermediateField l,
      GeneralAlgebraicallyClosedCoefficients.Stage l (PadicAlgCl l) T E ⥤
        DerivedCategory (pbcModules T (finiteRing l T E)))
    (j : ∀ (E F : PadicAlgCl.FiniteIntermediateField l) (h : E ≤ F),
      GeneralAlgebraicallyClosedCoefficients.stageTransition l (PadicAlgCl l) T E F h ⋙
        J F ≅ J E ⋙ pbcDerivedExtend (finiteMap l T h)) : Prop :=
  ∀ (E F H : PadicAlgCl.FiniteIntermediateField l) (h : E ≤ F) (k : F ≤ H)
    (K : GeneralAlgebraicallyClosedCoefficients.Stage l (PadicAlgCl l) T E),
    (J H).map
        (((GeneralAlgebraicallyClosedCoefficients.stageSystem l (PadicAlgCl l) T).assoc h k).hom.app
          K) ≫ (j E H (h.trans k)).hom.app K =
      (j F H k).hom.app
          ((GeneralAlgebraicallyClosedCoefficients.stageTransition l (PadicAlgCl l) T E F h).obj
            K) ≫
        (pbcDerivedExtend (finiteMap l T k)).map ((j E F h).hom.app K) ≫
        (pbcReductionNormalization (finiteMap l T h) (finiteMap l T k)
          (finiteMap l T (h.trans k)) (finiteMap_comp l T h k) ((J E).obj K)).hom

/-- Identity comparison, with its ordinary multiplication and derived counit normalization.
Source: BS 6.8.14; node identity hypothesis
(blueprint: lem-sf-adic-common-stage-descent-equivalence). -/
def finiteIdentity
    (J : ∀ E : PadicAlgCl.FiniteIntermediateField l,
      GeneralAlgebraicallyClosedCoefficients.Stage l (PadicAlgCl l) T E ⥤
        DerivedCategory (pbcModules T (finiteRing l T E)))
    (j : ∀ (E F : PadicAlgCl.FiniteIntermediateField l) (h : E ≤ F),
      GeneralAlgebraicallyClosedCoefficients.stageTransition l (PadicAlgCl l) T E F h ⋙
        J F ≅ J E ⋙ pbcDerivedExtend (finiteMap l T h)) : Prop :=
  ∀ E : PadicAlgCl.FiniteIntermediateField l,
    ∃ (o : pbcExtend (finiteMap l T (E := E) le_rfl) ≅ 𝟭 _)
      (d : pbcDerivedExtend (finiteMap l T (E := E) le_rfl) ≅ 𝟭 _),
      (∀ (M : pbcModules T (finiteRing l T E)) (U : T.ProEtᵒᵖ)
        (a : (finiteRing l T E).obj.obj U) (x : M.val.obj U),
        (o.hom.app M).val.app U
          (pbcTensorSection (finiteMap l T (E := E) le_rfl) M U a x) = a • x) ∧
      (∀ P : CochainComplex (pbcModules T (finiteRing l T E)) ℤ,
        d.hom.app (DerivedCategory.Q.obj P) =
          pbcComplexCounit (finiteMap l T (E := E) le_rfl) P ≫
            DerivedCategory.Q.map ((NatIso.mapHomologicalComplex o (.up ℤ)).hom.app P)) ∧
      ∀ K : GeneralAlgebraicallyClosedCoefficients.Stage l (PadicAlgCl l) T E,
        HEq ((j E E le_rfl).hom.app K ≫ d.hom.app ((J E).obj K))
          ((J E).map
            ((GeneralAlgebraicallyClosedCoefficients.unitor l (PadicAlgCl l) T E).hom.app K))

/-- Descent of the given finite exact realization equivalences, with the specified
object and arrow formulas, canonical Hom-colimit bijections, exactness and essential image.
Source: BS Proposition 6.8.14; HRS Proposition 5.2 and Lemma 7.9
(blueprint: lem-sf-adic-common-stage-descent-equivalence).

Proof. (1) Finite type over the geometric field gives Noetherianity and qcqs; a finite
affine cover and the subspace argument give Noetherianity of every stratum.
(2) completedCondensedIntegral/Rational identify the actual completed and localized
rings, with inversion of l equivalent to inversion of a uniformizer by the DVR theorem.
The internal/section module equivalence is exact and preserves the balanced tensor maps.
(3) The finite and closure local-triviality lemmas identify the finite-free stratified
conditions with the lfp conditions of the condensed two-colimit theorem, including rank zero.
(4) Put G_E = J_E followed by extension to R_T. Naturality of j and the assumed tower
and identity equations give gamma_H/E = gamma_H/F followed by gamma_F/E. Conjugating
G_F(u) by the two endpoint gammas is therefore unchanged at a larger field. Eventual
equality gives independence of representatives. At one field cancellation gives the
functor laws. (5) Full faithfulness of J_F identifies the finite Hom groups. Their
transition maps agree, so the Hom surjectivity and eventual equality of the condensed
two-colimit theorem give exactly the asserted canonical bijections on their colimits.
(6) Descend a target object to a finite field, lift it through J_E and extend its
isomorphism to R_T. The Hom bijections construct a quasi-inverse on the full image.
(7) Derived change of rings and J_E are exact. The quotient-completion scalar shift
comparison and termwise balanced multiplication identify their shift comparisons
across fields. Finite-stage shifted objects and distinguished triangles therefore
have precisely their scalar-extended images, including the connecting morphism.
Full faithfulness lifts target cones, so the full essential image is triangulated. -/
theorem commonStageDescentEquivalence
    (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    (a : T ⟶ Spec (CommRingCat.of D.k))
    [IsSeparated a] [LocallyOfFiniteType a] [QuasiCompact a]
    (J : ∀ E : PadicAlgCl.FiniteIntermediateField l,
      GeneralAlgebraicallyClosedCoefficients.Stage l (PadicAlgCl l) T E ⥤
        DerivedCategory (pbcModules T (finiteRing l T E)))
    [∀ E, (J E).CommShift ℤ]
    (hJ : ∀ E, (J E).IsTriangulated ∧
      (∀ K L, Function.Bijective ((J E).map : (K ⟶ L) → (_ ⟶ _))) ∧
      ∀ M, constructible T (finiteRing l T E) M ↔ ∃ K, Nonempty ((J E).obj K ≅ M))
    (hlinear : ∀ (E : PadicAlgCl.FiniteIntermediateField l)
      (K L : GeneralAlgebraicallyClosedCoefficients.Stage l (PadicAlgCl l) T E)
      (f : K ⟶ L)
      (b : Localization.Away (Padic.coefficientExtensionUniformizer l (coefficient.{u} l E))),
      (J E).map (b • f) = sfRationalCoefficientEquiv l (coefficient.{u} l E) b • (J E).map f)
    (α : ∀ E : PadicAlgCl.FiniteIntermediateField l,
      sfRationalConstructibleLocalization l (coefficient.{u} l E) T ⋙ J E ≅
        ObjectProperty.ι (sfIntegralConstructible l (coefficient.{u} l E) T) ⋙
          pbcDerivedExtend (integralMap l T E))
    (hα : ∀ E, (α E).hom.CommShift ℤ)
    (j : ∀ (E F : PadicAlgCl.FiniteIntermediateField l) (h : E ≤ F),
      GeneralAlgebraicallyClosedCoefficients.stageTransition l (PadicAlgCl l) T E F h ⋙
        J F ≅ J E ⋙ pbcDerivedExtend (finiteMap l T h))
    (hn : scalarNormalized l T J α j)
    (hidentity : finiteIdentity l T J j)
    (hfinite : finiteCoherent l T J j)
    (hj : coherent l T J j) :
    ∃ ρ : GeneralAlgebraicallyClosedCoefficients.Pair l (PadicAlgCl l) T ⥤
        DerivedCategory (pbcModules T (closureRing l T)),
      (∀ A, ρ.obj A = (extended l T J A.stage).obj A.obj) ∧
      (∀ (A B : GeneralAlgebraicallyClosedCoefficients.Pair l (PadicAlgCl l) T)
        (F : PadicAlgCl.FiniteIntermediateField l) (hA : A.stage ≤ F) (hB : B.stage ≤ F)
        (f : A.toStage hA ⟶ B.toStage hB),
        HEq (ρ.map (StageSystem.PairCategory.mkHom F hA hB f))
          ((gamma l T J j A.stage F hA A.obj).inv ≫ (extended l T J F).map f ≫
            (gamma l T J j B.stage F hB B.obj).hom)) ∧
      (∀ A B, Function.Bijective (fun z : GeneralAlgebraicallyClosedCoefficients.ColimitHom A B ↦
        ρ.map ((GeneralAlgebraicallyClosedCoefficients.homCoordinates A B).symm z))) ∧
      (∀ M, constructible T (closureRing l T) M ↔ ∃ A, Nonempty (ρ.obj A ≅ M)) ∧
      (∃ e : GeneralAlgebraicallyClosedCoefficients.Pair l (PadicAlgCl l) T ≌
          (constructible T (closureRing l T)).FullSubcategory,
        Nonempty (e.functor ⋙ (constructible T (closureRing l T)).ι ≅ ρ)) ∧
      ∃ c : ρ.CommShift ℤ,
        (fun [commInst : ρ.CommShift ℤ] ↦ ρ.IsTriangulated ∧
          ∀ (E : PadicAlgCl.FiniteIntermediateField l)
            (K : GeneralAlgebraicallyClosedCoefficients.Stage l (PadicAlgCl l) T E) (m : ℤ),
            HEq
              (ρ.map
                  (((GeneralAlgebraicallyClosedCoefficients.inclusion
                    (l := l) (Ω := PadicAlgCl l) (Y := T) E).commShiftIso m).hom.app K) ≫
                (ρ.commShiftIso m).hom.app
                  ((GeneralAlgebraicallyClosedCoefficients.inclusion
                    (l := l) (Ω := PadicAlgCl l) (Y := T) E).obj K))
              (((extended l T J E).commShiftIso m).hom.app K)) (commInst := c) := by
  sorry

end WeilConjectures.SfAdicCommonStageDescent
