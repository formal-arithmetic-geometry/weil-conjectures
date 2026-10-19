/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q46
-/
module
public import Sheaf.Paper.CoefDerivedSystemEvaluationCalculus
public import Sheaf.Paper.SemilinearDerivedSections
public import Sheaf.Paper.IntegralScalarExtensionUniverses
public import Sheaf.Paper.IntegralReductionTowerCanonical
public import Sheaf.Paper.CompletedIntegralConstantMapOfUniverses
import Sheaf.Paper.NormalizedDVREffectivity
import Sheaf.Paper.NormalizedDVRTower
import Sheaf.Paper.IntegralScalarExtensionWellDefined
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Algebra.Homology.ChangeOfRingsKFlat
import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import Sheaf.Algebra.Category.ModuleCat.Presheaf.SheafificationBilinearExtension
import Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
import Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
/-! # Coherent finite reduction of completed coefficient extension

Source: main-20261015 blueprint, sec-proetale-coefficients/sk-def-sf-operations,
def-weil-derived-pullback-tensor-hom, integral operations; Stacks 06YS, 0G7E, 06YY.
(blueprint: lem-pur-coefficient-extension-reduction-model).
Positive exponent m is encoded by n=m-1. All derived categories are unbounded,
and the small pro-etale site's object and morphism universes remain independent.

## Main definitions

- `CoefficientExtensionReductionData`: simultaneous models and their canonical counit.
- `coefficientExtensionReductionIso`: that counit as a coherent-system isomorphism.

## Main statements

- `coefficientExtensionReductionModel`: existence on the entire unbounded derived category.
- `coefficientExtensionReduction_identity`: normalization for identity coefficients.
- `coefficientExtensionReduction_composition`: compatibility for three coefficient fields.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures
section ScalarZero
universe c v r
variable {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
  [EssentiallySmall.{r} C] {R S : Sheaf J CommRingCat.{r}} {f : R ⟶ S}
/-- Zero preservation from the actual additive structure, with the coefficient
universe explicitly retained. Source: Stacks 06YY
(blueprint: lem-pur-coefficient-extension-reduction-model). -/
instance coefficientScalarModelZero (A : SemilinearSections.ScalarData.{c, v, r} f) :
    A.model.E.PreservesZeroMorphisms :=
  @Functor.preservesZeroMorphisms_of_additive _ _ _ _ _ _ A.model.E A.model.additive
end ScalarZero

section ScalarAssociation
universe c v r
variable {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
  [EssentiallySmall.{max c v r} C]
  {R S T : Sheaf J CommRingCat.{max c v r}} {f : R ⟶ S} {g : S ⟶ T} {h : R ⟶ T}
  (A : SemilinearSections.ScalarData.{c, v, max c v r} f)
  (B : SemilinearSections.ScalarData.{c, v, max c v r} g)
  (D : SemilinearSections.ScalarData.{c, v, max c v r} h)

/-- Canonical scalar association, normalized on local tensors and on K-flat complexes.
It applies in particular on the actual coefficient sequence site.
Source: integral operations, node proof steps 2 and 7
(blueprint: lem-pur-coefficient-extension-reduction-model). -/
structure CoefficientScalarAssociation where
  /-- Ordinary balanced tensor association. -/
  ordinary : A.model.E ⋙ B.model.E ≅ D.model.E
  /-- The balanced formula, including arbitrary coefficients in both factors. -/
  section_formula : ∀ (M : SemilinearSections.Mod.{c, v, max c v r} J R) (U : Cᵒᵖ)
    (s : S.obj.obj U) (t : T.obj.obj U) (x : M.val.obj U),
    (ordinary.hom.app M).val.app U
      (t • SemilinearSections.scalarExtensionSection.{c, v, r} g B (A.model.E.obj M) U
        (s • SemilinearSections.scalarExtensionSection.{c, v, r} f A M U x)) =
      (((g.hom.app U) s * t) • SemilinearSections.scalarExtensionSection.{c, v, r} h D M U x)
  /-- The association in the coherent derived category. -/
  derived : A.T ⋙ B.T ≅ D.T
  /-- It is the localization of the same balanced association on K-flat models. -/
  model : ∀ (P : CochainComplex (SemilinearSections.Mod.{c, v, max c v r} J R) ℤ)
    (_hP : CochainComplex.IsKFlatIndependentCoefficients (R := R) P),
    derived.hom.app (DerivedCategory.Q.obj P) ≫ D.model.ε.app P =
      B.T.map (A.model.ε.app P) ≫
        B.model.ε.app ((A.model.E.mapHomologicalComplex (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex ordinary.hom (.up ℤ)).app P)

/-- The identity extension unitor with its ordinary and derived normalizations.
Source: integral operations, node proof step 6
(blueprint: lem-pur-coefficient-extension-reduction-model). -/
structure CoefficientScalarUnit {f : R ⟶ R}
    (A : SemilinearSections.ScalarData.{c, v, max c v r} f) where
  /-- Ordinary action unitor. -/
  ordinary : A.model.E ≅ 𝟭 (SemilinearSections.Mod.{c, v, max c v r} J R)
  /-- The unitor multiplies the tensor coefficient. -/
  section_formula : ∀ (M : SemilinearSections.Mod.{c, v, max c v r} J R) (U : Cᵒᵖ)
    (a : R.obj.obj U) (x : M.val.obj U),
    (ordinary.hom.app M).val.app U
      (a • SemilinearSections.scalarExtensionSection.{c, v, r} f A M U x) = a • x
  /-- Its derived localization. -/
  derived : A.T ≅ 𝟭 (SemilinearSections.D.{c, v, max c v r} J R)
  /-- The derived unitor is the ordinary one through the canonical K-flat counit. -/
  model : ∀ (P : CochainComplex (SemilinearSections.Mod.{c, v, max c v r} J R) ℤ)
    (_hP : CochainComplex.IsKFlatIndependentCoefficients (R := R) P),
    derived.hom.app (DerivedCategory.Q.obj P) =
      A.model.ε.app P ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex ordinary.hom (.up ℤ)).app P)
end ScalarAssociation

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L) (W : Scheme.{t})

/-- The actual finite quotient inclusions commute with quotient transitions.
Source: the integral operations clause and integralScalarQuotientMap_transition
(blueprint: lem-pur-coefficient-extension-reduction-model).
Proof: both ring maps send the residue of x to the residue of ι(x). Apply quotient
induction, then functorial constant sheafification. This includes ramified inclusions. -/
theorem coefficientExtensionQuotient_naturality (n : ℕ) :
    integralScalarQuotientSheafMap l E L ι W (n + 1) ≫
        coefficientSequenceCommRingTransition l L W n =
      coefficientSequenceCommRingTransition l E W n ≫
        integralScalarQuotientSheafMap l E L ι W n := by
  sorry

/-- The dependency's canonical semilinear scalar-extension data for the actual
quotient inclusions; no replacement functor or arbitrary coefficient map is used.
Source: integral operations and lem-coef-semilinear-derived-sections
(blueprint: lem-pur-coefficient-extension-reduction-model). -/
abbrev CoefficientExtensionSystems :=
  SemilinearSections.ScalarSystems.{t + 1, t, u} (Scheme.ProEt.topology W)
    (integralCoefficientCommRingSheaf l E W) (coefficientSequenceCommRingTransition l E W)
    (integralCoefficientCommRingSheaf l L W) (coefficientSequenceCommRingTransition l L W)
    (integralScalarQuotientSheafMap l E L ι W)
    (coefficientExtensionQuotient_naturality l E L ι W)

variable (SE : CoefficientDerivedSystemCalculus l E W)
  (SL : CoefficientDerivedSystemCalculus l L W)
  (A : CoefficientExtensionSystems l E L ι W)

/-- The coherent system C(K), formed by actual derived extension of the reduction
system; its evaluation is K_m tensor over A_m with B_m by A.evaluation.
Source: integral operations, simultaneous coefficient extension
(blueprint: lem-pur-coefficient-extension-reduction-model). -/
abbrev coefficientExtensionSystem :
    DerivedCategory (scalarReductionSource l E W) ⥤ coefficientSequenceDerived l L W :=
  SE.reduction ⋙ A.scalar.T

/-- The actual comparison: inverse of the completed-limit identification, followed
by the coherent counit. Associativity and unitors only display its functorial type.
Source: node proof step 4, φ=a⁻¹e, expressed with C already associated
(blueprint: lem-pur-coefficient-extension-reduction-model). -/
def coefficientExtensionCounit
    (δ : coefficientExtensionSystem l E L ι W SE A ⋙ coefficientSequenceLimit l L W ≅
      integralScalarExtensionOfUniverses l E L ι W) :
    integralScalarExtensionOfUniverses l E L ι W ⋙ SL.reduction ⟶
      coefficientExtensionSystem l E L ι W SE A :=
  (Functor.isoWhiskerRight δ.symm SL.reduction).hom ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft (coefficientExtensionSystem l E L ι W SE A) SL.adjunction.counit ≫
    (Functor.rightUnitor _).hom

/-- The existing additive structure of the finite scalar-extension model.
Source: Stacks 06YY (blueprint: lem-pur-coefficient-extension-reduction-model). -/
instance coefficientExtensionFiniteAdditive (n : ℕ) : ((A.levels n).model.E).Additive :=
  (A.levels n).model.additive

/-- Finite scalar extension preserves zero maps via its own additive structure.
Source: Stacks 06YY (blueprint: lem-pur-coefficient-extension-reduction-model). -/
instance coefficientExtensionFiniteZero (n : ℕ) :
    (A.levels n).model.E.PreservesZeroMorphisms :=
  @Functor.preservesZeroMorphisms_of_additive _ _ _ _ _ _ _ (A.levels n).model.additive

/-- Zero preservation from the published additive finite reduction.
Source: Stacks 06YY (blueprint: lem-pur-coefficient-extension-reduction-model). -/
instance coefficientExtensionReductionZero (n : ℕ) :
    (scalarReductionExtension l E W n).PreservesZeroMorphisms :=
  @Functor.preservesZeroMorphisms_of_additive _ _ _ _ _ _ _
    (coefficientFiniteExtensionAdditive l E W n)

/-- Zero preservation from the published additive direct scalar extension.
Source: Stacks 06YY (blueprint: lem-pur-coefficient-extension-reduction-model). -/
instance coefficientExtensionDirectZero (n : ℕ) :
    (integralScalarReduction l E L ι W n).PreservesZeroMorphisms :=
  @Functor.preservesZeroMorphisms_of_additive _ _ _ _ _ _ _
    (integralScalarReduction_additive l E L ι W n)

/-- Zero preservation for the same ordinary association source functor.
Source: Stacks 06YY (blueprint: lem-pur-coefficient-extension-reduction-model). -/
instance coefficientExtensionCompositeZero (n : ℕ) :
    (scalarReductionExtension l E W n ⋙ (A.levels n).model.E).PreservesZeroMorphisms :=
  letI := coefficientExtensionFiniteZero l E L ι W A n
  Functor.preservesZeroMorphisms_comp _ _

/-- Apply ordinary scalar association degree by degree. The explicit zero-map
instances expose the existing additive witnesses without changing any functor.
Source: integral operations, node proof step 2
(blueprint: lem-pur-coefficient-extension-reduction-model). -/
def coefficientExtensionAssociationChain (n : ℕ)
    (a : scalarReductionExtension l E W n ⋙ (A.levels n).model.E ≅
      integralScalarReduction l E L ι W n)
    (P : CochainComplex (scalarReductionSource l E W) ℤ) :=
  letI := coefficientExtensionFiniteZero l E L ι W A n
  letI := coefficientExtensionDirectZero l E L ι W n
  letI := coefficientExtensionCompositeZero l E L ι W A n
  (NatTrans.mapHomologicalComplex a.hom (.up ℤ)).app P

/-- The existing shifted Roos cone's actual nth projection, with its tower explicit.
Source: integral operations and completed scalar extension, node proof step 4
(blueprint: lem-pur-coefficient-extension-reduction-model). -/
def coefficientExtensionRoosProjection
    (P : CochainComplex (integralTowerModules l E W) ℤ) (n : ℕ) :
    (integralScalarComplexFunctor l E L ι W).obj P ⟶
      (integralScalarLevel l E L ι W n).obj P :=
  CochainComplex.mappingCocone.fst
      (towerTransitionEndomorphism
        (K := fun k ↦ ((integralScalarTowerFunctor l E L ι W).obj P).obj (op k))
        (integralOperationsTowerStep ((integralScalarTowerFunctor l E L ι W).obj P))) ≫
    Pi.π (fun k ↦ ((integralScalarTowerFunctor l E L ι W).obj P).obj (op k)) n

/-- The balanced scalar-association formula on every local tensor section.
Source: integral operations, node proof step 2
(blueprint: lem-pur-coefficient-extension-reduction-model). -/
def IsCoefficientExtensionAssociation
    (association : ∀ n : ℕ,
    scalarReductionExtension l E W n ⋙ (A.levels n).model.E ≅
      integralScalarReduction l E L ι W n) : Prop :=
  ∀ (n : ℕ) (M : scalarReductionSource l E W) (U : W.ProEtᵒᵖ)
    (a : (integralCoefficientCommRingSheaf l E W n).obj.obj U)
    (b : (integralCoefficientCommRingSheaf l L W n).obj.obj U) (x : M.val.obj U),
    ((association n).hom.app M).val.app U
      (b • SemilinearSections.scalarExtensionSection.{t + 1, t, u}
        (integralScalarQuotientSheafMap l E L ι W n) (A.levels n)
        ((scalarReductionExtension l E W n).obj M) U
        (a • @id (((scalarReductionExtension l E W n).obj M).val.obj U)
          (((scalarReductionExtension_adjunction l E W n).choose.unit.app M).val.app U x))) =
      integralScalarTensorSection l E L ι W n M U
        (((integralScalarQuotientSheafMap l E L ι W n).hom.app U) a * b) x

/-- Simultaneous ordinary scalar association on the actual finite quotient models.
The section formula fixes the balanced association on arbitrary tensor coefficients.
Source: integral operations, node proof steps 1--2
(blueprint: lem-pur-coefficient-extension-reduction-model). -/
structure CoefficientExtensionAssociationData where
  /-- Ordinary simultaneous scalar association. -/
  association : ∀ n : ℕ,
    scalarReductionExtension l E W n ⋙ (A.levels n).model.E ≅
      integralScalarReduction l E L ι W n
  /-- On local tensors, (x⊗a)⊗b maps to x⊗ι(a)b. -/
  association_section : IsCoefficientExtensionAssociation l E L ι W A association

/-- The direct quotient model has exactly the published quotient transitions.
Source: integral operations, node proof steps 2--3
(blueprint: lem-pur-coefficient-extension-reduction-model). -/
def IsCoefficientExtensionStrictTransition
    (direct : (integralOperationsGoodComplex l E W).FullSubcategory ⥤
      CochainComplex (coefficientSequenceModules l L W) ℤ)
    (directEvaluation : ∀ n : ℕ,
      direct ⋙ (coefficientSequenceEvaluation l L W n).mapHomologicalComplex (.up ℤ) ≅
        (integralOperationsGoodComplex l E W).ι ⋙ integralScalarFiniteComplex l E L ι W n) : Prop :=
  ∀ (P : (integralOperationsGoodComplex l E W).FullSubcategory)
    (n : ℕ) (i : ℤ) (U : W.ProEtᵒᵖ)
    (x : (((coefficientSequenceEvaluation l L W (n + 1)).obj
      ((direct.obj P).X i)).val.obj U)),
    HEq ((((coefficientSequenceTransition l L W (Nat.le_succ n)).app
        ((direct.obj P).X i)).val.app U).hom x)
      (((((directEvaluation n).inv.app P).f i).val.app U).hom
        ((((integralScalarTransition l E L ι W n).app P.obj).f i).val.app U
          ((((directEvaluation (n + 1)).hom.app P).f i).val.app U x)))

/-- The actual strict quotient model and its ordinary scalar association.
Source: integral operations, node proof steps 1--3
(blueprint: lem-pur-coefficient-extension-reduction-model). -/
structure CoefficientExtensionStrictModel extends
    CoefficientExtensionAssociationData l E L ι W A where
  /-- The direct quotient models as one functor of strict system complexes. -/
  direct : (integralOperationsGoodComplex l E W).FullSubcategory ⥤
    CochainComplex (coefficientSequenceModules l L W) ℤ
  /-- Its finite values are the actual P tensor B_m, simultaneously. -/
  directEvaluation : ∀ n : ℕ,
    direct ⋙ (coefficientSequenceEvaluation l L W n).mapHomologicalComplex (.up ℤ) ≅
      (integralOperationsGoodComplex l E W).ι ⋙ integralScalarFiniteComplex l E L ι W n
  /-- The strict transitions are the actual quotient maps on every section. -/
  direct_transition : IsCoefficientExtensionStrictTransition l E L ι W direct directEvaluation

/-- The representative-normalized coherent counit comparison, with its completion.
Source: integral operations, node proof steps 4--6
(blueprint: lem-pur-coefficient-extension-reduction-model). -/
structure CoefficientExtensionReductionData extends
    CoefficientExtensionStrictModel l E L ι W A where
  /-- One coherent representative comparison, natural on the resolving category. -/
  model : integralOperationsGoodLocalization l E W ⋙
      coefficientExtensionSystem l E L ι W SE A ≅ direct ⋙ DerivedCategory.Q
  /-- This coherent comparison evaluates to derived scalar association through the
  canonical universal counits, using the same P at every level. -/
  model_evaluation : ∀ (P : (integralOperationsGoodComplex l E W).FullSubcategory) (n : ℕ),
    (coefficientSequenceDerivedEvaluation l L W n).map (model.hom.app P) ≫
        (coefficientSequenceEvaluation l L W n).mapDerivedCategoryFactors.hom.app
          (direct.obj P) ≫ DerivedCategory.Q.map ((directEvaluation n).hom.app P) =
      (A.evaluation n).hom.app (SE.reduction.obj (DerivedCategory.Q.obj P.obj)) ≫
        (A.levels n).T.map ((SE.reductionEvaluation n).hom.app
          (DerivedCategory.Q.obj P.obj)) ≫
        (A.levels n).T.map (coefficientFiniteReductionModel l E W P.obj P.property.1 n).hom ≫
        (A.levels n).model.ε.app
          (((scalarReductionExtension l E W n).mapHomologicalComplex (.up ℤ)).obj P.obj) ≫
        DerivedCategory.Q.map
          (coefficientExtensionAssociationChain l E L ι W A n (association n) P.obj)
  /-- The system is normalized without any boundedness or constructibility condition. -/
  normalized : ∀ K : DerivedCategory (scalarReductionSource l E W),
    IsNormalizedCoefficientSequence l L W
      ((coefficientExtensionSystem l E L ι W SE A).obj K)
  /-- Its total limit is the specified completed scalar extension. -/
  completion : coefficientExtensionSystem l E L ι W SE A ⋙ coefficientSequenceLimit l L W ≅
    integralScalarExtensionOfUniverses l E L ι W
  /-- The completion identification uses the actual Roos projections on good models. -/
  completion_projection :
    ∀ (P : (integralOperationsGoodComplex l E W).FullSubcategory) (n : ℕ),
    completion.inv.app (DerivedCategory.Q.obj P.obj) ≫
        (coefficientSequenceProjection l L W n).app
          ((coefficientExtensionSystem l E L ι W SE A).obj (DerivedCategory.Q.obj P.obj)) ≫
        (coefficientFiniteDerivedRestriction l L W n).map
          ((coefficientSequenceDerivedEvaluation l L W n).map (model.hom.app P) ≫
            (coefficientSequenceEvaluation l L W n).mapDerivedCategoryFactors.hom.app
              (direct.obj P) ≫ DerivedCategory.Q.map ((directEvaluation n).hom.app P)) ≫
        (scalarReductionRestriction l L W n).mapDerivedCategoryFactors.hom.app
          ((integralScalarFiniteComplex l E L ι W n).obj P.obj) =
      (integralScalarExtensionComparisonOfUniverses l E L ι W).hom.app P ≫
        DerivedCategory.Q.map
          (coefficientExtensionRoosProjection l E L ι W P.obj n)
  /-- The specified coherent counit comparison is an isomorphism. -/
  comparison_isIso : IsIso (coefficientExtensionCounit l E L ι W SE SL A completion)

/-- The natural isomorphism of coherent quotient systems, with its specified counit.
Source: integral operations, node proof step 4
(blueprint: lem-pur-coefficient-extension-reduction-model). -/
def coefficientExtensionReductionIso
    (d : CoefficientExtensionReductionData l E L ι W SE SL A) :
    integralScalarExtensionOfUniverses l E L ι W ⋙ SL.reduction ≅
      coefficientExtensionSystem l E L ι W SE A :=
  @asIso _ _ _ _ (coefficientExtensionCounit l E L ι W SE SL A d.completion) d.comparison_isIso

/-- Coherent finite reduction of completed scalar extension on the entire derived category.
Source: integral operations, Stacks 06YS, 0G7E, 06YY
(blueprint: lem-pur-coefficient-extension-reduction-model).
Proof: choose one flat-term K-flat P. Change of rings preserves K-flatness and flat
terms even for ramified quotient maps. The balanced maps (x⊗a)⊗b ↦ x⊗ι(a)b and
x⊗b ↦ (x⊗1)⊗b are inverse and commute with differentials. Quotient reduction
commutes with these formulas, giving a strict system isomorphism and normalization
by the same association with B_m→B_n. Its cocycle is the quotient cocycle. The
Roos construction computes the specified total limit and its projections, hence
completion. Apply normalized DVR effectivity with coefficient field L: its counit
is invertible and normalized by the actual limit projections. Transport it through
the simultaneous association to obtain exactly coefficientExtensionCounit.
Naturality on chain maps descends through the localization of flat-term K-flat
complexes; quasi-isomorphisms and roofs give the canonical resolution comparisons,
including their composition for a third representative. The equations hold for all
m≥n, including identities, because the comparison is a map of coherent systems.
For identity extension scalar association is the action unitor, so this is the
usual reduction counit of the completion, without assuming K itself complete.
For three fields the two scalar associations multiply the same coefficients.
Apply coefficient extension to this coherent counit and then use counit naturality
h e_H = e_J R_F L_F(h). This is an equality of system maps before evaluation,
and gives the composition equation stated below. No finiteness of K is used. -/
theorem coefficientExtensionReductionModel
    (_hl : IsUnit (l : Γ(W, ⊤))) :
    Nonempty (CoefficientExtensionReductionData l E L ι W SE SL A) := by
  sorry

section SuccessiveExtension
variable (F : Type u) [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
  (j : L →ₐ[ℚ_[l]] F) (SF : CoefficientDerivedSystemCalculus l F W)
  (B : CoefficientExtensionSystems l L F j W)
  (D : CoefficientExtensionSystems l E F (j.comp ι) W)
  (dEL : CoefficientExtensionReductionData l E L ι W SE SL A)
  (dLF : CoefficientExtensionReductionData l L F j W SL SF B)
  (dEF : CoefficientExtensionReductionData l E F (j.comp ι) W SE SF D)

/-- Successive finite extension: extend the coherent E,L counit, then associate scalars.
Source: integral operations, node proof step 7
(blueprint: lem-pur-coefficient-extension-reduction-model). -/
def coefficientExtensionSuccessiveSystemIso
    (a : CoefficientScalarAssociation.{t + 1, t, u} A.scalar B.scalar D.scalar) :
    integralScalarExtensionOfUniverses l E L ι W ⋙
        coefficientExtensionSystem l L F j W SL B ≅
      coefficientExtensionSystem l E F (j.comp ι) W SE D :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (coefficientExtensionReductionIso l E L ι W SE SL A dEL)
      B.scalar.T ≪≫
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft SE.reduction a.derived

/-- The completed successive-extension comparison is the total limit of the same
coherent finite-system comparison.
Source: integral operations, node proof step 8
(blueprint: lem-pur-coefficient-extension-reduction-model). -/
def coefficientExtensionSuccessiveIso
    (a : CoefficientScalarAssociation.{t + 1, t, u} A.scalar B.scalar D.scalar) :
    integralScalarExtensionOfUniverses l E L ι W ⋙
        integralScalarExtensionOfUniverses l L F j W ≅
      integralScalarExtensionOfUniverses l E F (j.comp ι) W :=
  Functor.isoWhiskerLeft (integralScalarExtensionOfUniverses l E L ι W)
      dLF.completion.symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (coefficientExtensionSuccessiveSystemIso l E L ι W SE SL A F j B D dEL a)
      (coefficientSequenceLimit l F W) ≪≫ dEF.completion

/-- The direct and successive reduction comparisons agree as coherent system maps.
Source: integral operations, node proof steps 7--8
(blueprint: lem-pur-coefficient-extension-reduction-model).
Proof: the ordinary associator and its inverse are balanced multiplication and
insertion of 1. They commute with every quotient transition; on three tensor factors
the two formulas multiply the same coefficients. K-flat change of rings and the
universal counits descend this strict association to coherent systems. Let h be
coefficientExtensionSuccessiveSystemIso. Naturality of the actual reduction/limit
counit gives h e_H = e_J R_F(L_F h). Substitute the normalized completion
identifications and the definitions of the three reduction comparisons. The
result is the displayed equation, before any evaluation. -/
theorem coefficientExtensionReduction_composition
    (_hl : IsUnit (l : Γ(W, ⊤))) :
    ∃ a : CoefficientScalarAssociation.{t + 1, t, u} A.scalar B.scalar D.scalar,
      ∀ K : DerivedCategory (scalarReductionSource l E W),
        (coefficientExtensionReductionIso l L F j W SL SF B dLF).hom.app
            ((integralScalarExtensionOfUniverses l E L ι W).obj K) ≫
          (coefficientExtensionSuccessiveSystemIso l E L ι W SE SL A F j B D dEL a).hom.app K =
        SF.reduction.map
            ((coefficientExtensionSuccessiveIso l E L ι W SE SL A F j SF
              B D dEL dLF dEF a).hom.app K) ≫
          (coefficientExtensionReductionIso l E F (j.comp ι) W SE SF D dEF).hom.app K := by
  sorry
end SuccessiveExtension

/-- For identity extension, association is the action unitor and the comparison is
exactly the usual reduction counit of the completion. K need not be complete.
Source: integral operations, node proof step 6
(blueprint: lem-pur-coefficient-extension-reduction-model).
Proof: multiplication (x⊗a)⊗b ↦ x⊗ab is the action unitor when L=E.
Its localization has the stated universal-counit normalization. Naturality of the
coherent counit with this unitor gives the displayed equation. -/
theorem coefficientExtensionReduction_identity
    (A₀ : CoefficientExtensionSystems l E E (AlgHom.id ℚ_[l] E) W)
    (d : CoefficientExtensionReductionData l E E (AlgHom.id ℚ_[l] E) W SE SE A₀) :
    ∃ a : CoefficientScalarUnit.{t + 1, t, u} A₀.scalar,
      ∀ K : DerivedCategory (scalarReductionSource l E W),
        (coefficientExtensionReductionIso l E E (AlgHom.id ℚ_[l] E) W SE SE A₀ d).hom.app K ≫
          (Functor.isoWhiskerLeft SE.reduction a.derived ≪≫
            Functor.rightUnitor SE.reduction).hom.app K =
        SE.reduction.map (d.completion.inv.app K ≫
          (coefficientSequenceLimit l E W).map
            ((Functor.isoWhiskerLeft SE.reduction a.derived ≪≫
              Functor.rightUnitor SE.reduction).hom.app K)) ≫
          SE.adjunction.counit.app (SE.reduction.obj K) := by
  sorry

end WeilConjectures
