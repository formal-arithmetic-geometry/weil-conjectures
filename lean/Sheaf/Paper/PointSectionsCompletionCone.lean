/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q13
-/
module

public import Sheaf.Paper.PointProEtaleSectionsExact
public import Sheaf.Paper.SfIntegralConstructible
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Sheaf.Paper.IntegralOperationsWellDefined
public import Sheaf.Paper.DerivedPullbackTensorHom
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Sheaf.Paper.TraceFormulaCoefficientConventions
public import Sheaf.Paper.CompletedStalkReparametrizationCoherence
public import Sheaf.Paper.FiniteFreeCompletedScalarComparison
public import Sheaf.AlgebraicGeometry.FrobeniusDetailed
public import Sheaf.Paper.CompletedIntegralConstantMapOfUniverses
public import Sheaf.Paper.AdicCoefficientDatum
public import Sheaf.Paper.InverseImagePullbackComparisonDerived
import all Sheaf.Paper.PointQuotientAugmentationDiagram
import all Sheaf.Paper.IntegralOperationsWellDefined
import all Sheaf.Paper.FiniteFreeCompletedScalarComparison
import Sheaf.Paper.CompletedLineTensorCoherence

/-! # Point sections of the specified completion cone

Source: blueprint main-20261015, sec-trace-formula/sk-d-weil,
prop-trf-rational-frobenius-integral-model.proof.md, clause (3), sectionwise cone
and canonical completion comparisons; Stacks Tag 0941
(blueprint: lem-trf-point-sections-completion-cone).

The chain comparison and its two projections are the existing `CompletedStalk.sectionsRoos`,
`roosFirst`, and `roosSecond`. Sections retain their canonical integral scalar action.
The natural-number index n denotes exponent n+1. All derived comparisons are normalized
on every flat-term K-flat representative, including unbounded representatives.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective


universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.PointSectionsCompletionCone

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology
attribute [-instance] WeilConjectures.PrincipalKoszulStrictReplacement.abSheafify
attribute [-instance] WeilConjectures.PrincipalKoszulStrictReplacement.abLocallyBijective
attribute [-instance] WeilConjectures.PrincipalKoszulStrictReplacement.siteSmall
attribute [-instance] WeilConjectures.integralOperationsAbSheafify
attribute [-instance] WeilConjectures.integralOperationsAbLocallyBijective
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
attribute [-instance] WeilConjectures.integralOperationsCommHasDerivedCategory
attribute [local instance 5000] WeilConjectures.integralTowerHasDerivedCategory
attribute [local irreducible] CategoryTheory.constantSheaf HasDerivedCategory.standard
  CategoryTheory.Limits.limit completedIntegralCommRingSheafUnrestricted
  completedIntegralCoefficientSheafUnrestricted pointIntegralSectionMap
  completedScalarIdentityUnit integralScalarExtensionOfUniverses
  integralScalarExtensionComparisonOfUniverses HasDerivedCategory.ofIsGrothendieckAbelian
  HasDerivedCategory.ofHasKInjectiveResolutions DerivedCategory.Q Functor.mapDerivedCategory
  Functor.mapDerivedCategoryFactors
  completedScalarComparison completedDerivedScalarExtension completedScalarCounit
  CompletedLineTensor.ordinaryUnit integralOperationsRoosMap
  PointQuotientAugmentation.roosComparison CompletedStalk.sectionsRoos


/-- Spec of the specified geometric field Frobenius, on the original algebraic closure.
Source: blueprint clause (3), coefficient convention
(blueprint: lem-trf-point-sections-completion-cone). -/
def frobenius : Spec (.of D.k) ⟶ Spec (.of D.k) :=
  letI := Fintype.ofFinite D.k₀
  Spec.map (CommRingCat.ofHom
    (FiniteField.geometricFrobeniusAlgEquivOfAlgebraic D.k₀ D.k).toRingHom)

/-- The existing section complex functor, with its canonical integral coefficient action.
Source: blueprint clause (3); Stacks 0941
(blueprint: lem-trf-point-sections-completion-cone). -/
abbrev sections := CompletedStalk.sectionsComplex D l E

/-- The existing ordinary-module localization used by integral point sections.
Source: blueprint clause (3); Stacks 05RU
(blueprint: lem-trf-point-sections-completion-cone). -/
abbrev moduleQ := CompletedStalk.moduleQ l E

/-- Exact sections' specified comparison with termwise sections on representatives.
Source: blueprint clause (3); Stacks 0941
(blueprint: lem-trf-point-sections-completion-cone). -/
def factors : DerivedCategory.Q ⋙ pointFibreIntegralAmbient D l E ≅
    sections D l E ⋙ moduleQ l E :=
  @Functor.mapDerivedCategoryFactors _ _ _ (HasDerivedCategory.standard _)
    _ _ _ (HasDerivedCategory.ofIsGrothendieckAbelian _)
    (pointIntegralSections l E D.k) (pointIntegralSectionsAdditive l E D.k)
    (pointFibreIntegralLimits D l E) (pointFibreIntegralColimits D l E)

/-- The strict reduction tower P_n, with its actual quotient transitions.
Source: blueprint clause (3); identity-extension specialization of the recorded tower
(blueprint: lem-trf-point-sections-completion-cone). -/
abbrev reductions := integralScalarTowerFunctor l E E (AlgHom.id ℚ_[l] E) (Spec (.of D.k))

/-- The completed identity coefficient extension, before applying sections.
Source: blueprint clause (3); Bhatt--Scholze 3.4.10
(blueprint: lem-trf-point-sections-completion-cone). -/
abbrev completion :=
  integralScalarExtensionOfUniverses l E E (AlgHom.id ℚ_[l] E) (Spec (.of D.k))

/-- The derived reduction-limit functor followed by exact sections.
Source: blueprint clause (3); Stacks 0941
(blueprint: lem-trf-point-sections-completion-cone). -/
def completedSections := completion D l E ⋙ pointFibreIntegralAmbient D l E

/-- The specified identity-extension model, followed by exact sections and the
identity on both sectionwise cone coordinates. No Roos-triangle filler is chosen.
Source: blueprint clause (3); Stacks 0941
(blueprint: lem-trf-point-sections-completion-cone). -/
def completionModel
    (P : (integralOperationsGoodComplex l E (Spec (.of D.k))).FullSubcategory) :
    (completedSections D l E).obj (DerivedCategory.Q.obj P.obj) ≅
      (moduleQ l E).obj
        (integralOperationsRoos ((reductions D l E).obj P.obj ⋙ sections D l E)) :=
  (pointFibreIntegralAmbient D l E).mapIso
      ((integralScalarExtensionComparisonOfUniverses l E E (AlgHom.id ℚ_[l] E)
        (Spec (.of D.k))).app P) ≪≫
    (factors D l E).app
      ((integralScalarComplexFunctor l E E (AlgHom.id ℚ_[l] E)
        (Spec (.of D.k))).obj P.obj) ≪≫
    (moduleQ l E).mapIso (CompletedStalk.sectionsRoos D l E ((reductions D l E).obj P.obj))

/-- The same model at any representative isomorphism q:Q(P) ≅ N.
Source: blueprint clause (3); Stacks 0941
(blueprint: lem-trf-point-sections-completion-cone). -/
def completionModelAt
    (N : sfIntegralConstructibleCategory l E (Spec (.of D.k)))
    (P : (integralOperationsGoodComplex l E (Spec (.of D.k))).FullSubcategory)
    (q : DerivedCategory.Q.obj P.obj ≅ N.obj) :=
  (completedSections D l E).mapIso q.symm ≪≫ completionModel D l E P

/-- The defining pullback representative, exact sections, and c_C, in that order.
Source: blueprint clause (3); Stacks 0941
(blueprint: lem-trf-point-sections-completion-cone). -/
def pullbackModel
    (P : (integralOperationsGoodComplex l E (Spec (.of D.k))).FullSubcategory) :
    (pointFibreIntegralAmbient D l E).obj
        ((integralDerivedPullback l E (frobenius D)).obj (DerivedCategory.Q.obj P.obj)) ≅
      (moduleQ l E).obj (integralOperationsRoos
        ((integralOperationsPullbackTowerFunctor l E (frobenius D)).obj P.obj ⋙
          sections D l E)) :=
  (pointFibreIntegralAmbient D l E).mapIso
      ((integralDerivedPullbackComparison l E (frobenius D)).app P) ≪≫
    (factors D l E).app
      ((integralOperationsPullbackComplexFunctor l E (frobenius D)).obj P.obj) ≪≫
    (moduleQ l E).mapIso (CompletedStalk.sectionsRoos D l E
      ((integralOperationsPullbackTowerFunctor l E (frobenius D)).obj P.obj))

/-- The specified beta on every resolution, using the defining pullback comparison.
Source: blueprint clause (3); Stacks 0941
(blueprint: lem-trf-point-sections-completion-cone). -/
def beta
    (N : sfIntegralConstructibleCategory l E (Spec (.of D.k)))
    (P : (integralOperationsGoodComplex l E (Spec (.of D.k))).FullSubcategory)
    (q : DerivedCategory.Q.obj P.obj ≅ N.obj) :=
  (pointFibreIntegralAmbient D l E).mapIso
      ((integralDerivedPullback l E (frobenius D)).mapIso q.symm) ≪≫
    pullbackModel D l E P

/-- The augmentation a_P: exact sections of the specified completion unit, followed
by the identity on both sectionwise product coordinates. Its shifted coordinate is zero.
Source: blueprint clause (3); Bhatt--Scholze 3.5.2; Stacks 0941
(blueprint: lem-trf-point-sections-completion-cone). -/
def augmentation (P : CochainComplex (integralTowerModules l E (Spec (.of D.k))) ℤ) :=
  (sections D l E).map ((completedScalarIdentityUnit l E (Spec (.of D.k))).app P) ≫
    (CompletedStalk.sectionsRoos D l E ((reductions D l E).obj P)).hom

/-- The normalization predicate fixes the actual completion map on every flat-term
K-flat resolution, rather than its composites with just the finite reductions.
Source: blueprint clause (3); Stacks 0941
(blueprint: lem-trf-point-sections-completion-cone). -/
def CompletionNormalization
    (α : (sfIntegralConstructible l E (Spec (.of D.k))).ι ⋙
        pointFibreIntegralAmbient D l E ≅
      (sfIntegralConstructible l E (Spec (.of D.k))).ι ⋙ completedSections D l E) : Prop :=
  ∀ (N : sfIntegralConstructibleCategory l E (Spec (.of D.k)))
    (P : (integralOperationsGoodComplex l E (Spec (.of D.k))).FullSubcategory)
    (q : DerivedCategory.Q.obj P.obj ≅ N.obj),
    (pointFibreIntegralAmbient D l E).map q.hom ≫ α.hom.app N ≫
        (completionModelAt D l E N P q).hom =
      (factors D l E).hom.app P.obj ≫ (moduleQ l E).map (augmentation D l E P.obj)

section Proof
attribute [local irreducible] factors


private instance pointProducts :
    PreservesLimitsOfShape (Discrete ℕ) (pointIntegralSections l E D.k) :=
  PointQuotientAugmentation.sectionsProducts l E D.k

section FoldedRoos
attribute [local irreducible] pointIntegralSections
  PointQuotientAugmentation.coneComparison
attribute [local semireducible] CompletedStalk.sectionsRoos
attribute [local instance 3000] Algebra.toModule


private theorem sectionsRoos_eq
    (T : ℕᵒᵖ ⥤ CochainComplex (integralTowerModules l E (Spec (.of D.k))) ℤ) :
    CompletedStalk.sectionsRoos D l E T =
      (PointQuotientAugmentation.roosComparison (pointIntegralSections l E D.k)).app T := by
  apply (CompletedStalk.sectionsRoos_existsUnique D l E T).unique
  · exact (CompletedStalk.sectionsRoos_existsUnique D l E T).exists.choose_spec
  · have h := PointQuotientAugmentation.roosComparison_coordinates
      (pointIntegralSections l E D.k)
    constructor
    · intro n i
      simpa only [CompletedStalk.roosFirst, integralOperationsTowerStep,
        CompletedStalk.sectionsComplex, integralOperationsRoosFunctor,
        Functor.comp_obj, Iso.app_hom, Category.assoc] using! h.1 T n i
    · intro n i
      simpa only [CompletedStalk.roosSecond, integralOperationsTowerStep,
        CompletedStalk.sectionsComplex, integralOperationsRoosFunctor,
        Functor.comp_obj, Iso.app_hom, Category.assoc] using! h.2 T n i


end FoldedRoos
attribute [local instance 3000] Algebra.toModule


private theorem sectionsRoos_coordinates
    (T : ℕᵒᵖ ⥤ CochainComplex (integralTowerModules l E (Spec (.of D.k))) ℤ) :
    (∀ (n : ℕ) (i : ℤ), (CompletedStalk.sectionsRoos D l E T).hom.f i ≫
        CompletedStalk.roosFirst (T ⋙ sections D l E) n i =
      (pointIntegralSections l E D.k).map (CompletedStalk.roosFirst T n i)) ∧
    (∀ (n : ℕ) (i : ℤ), (CompletedStalk.sectionsRoos D l E T).hom.f i ≫
        CompletedStalk.roosSecond (T ⋙ sections D l E) n i =
      (pointIntegralSections l E D.k).map (CompletedStalk.roosSecond T n i)) := by
  unfold CompletedStalk.sectionsRoos
  exact (CompletedStalk.sectionsRoos_existsUnique D l E T).exists.choose_spec


private def completionUnit : 𝟭 _ ⟶ completion D l E :=
  (CompletedLineTensor.ordinaryUnit l E (Spec (.of D.k))).inv ≫
    completedScalarComparison l E E (AlgHom.id ℚ_[l] E) (Spec (.of D.k))


private theorem completionUnit_spec
    (P : (integralOperationsGoodComplex l E (Spec (.of D.k))).FullSubcategory) :
    (completionUnit D l E).app (DerivedCategory.Q.obj P.obj) ≫
        (integralScalarExtensionComparisonOfUniverses l E E (AlgHom.id ℚ_[l] E)
          (Spec (.of D.k))).hom.app P =
      DerivedCategory.Q.map ((completedScalarIdentityUnit l E (Spec (.of D.k))).app P.obj) := by
  have h := (finiteFreeCompletedScalarComparison l E E (AlgHom.id ℚ_[l] E)
    (Spec (.of D.k))).2.2 P
  have hμ : (CompletedLineTensor.ordinaryUnit l E (Spec (.of D.k))).hom.app
      (DerivedCategory.Q.obj P.obj) =
        completedScalarCounit l E E (AlgHom.id ℚ_[l] E) (Spec (.of D.k)) P.obj ≫
          DerivedCategory.Q.map
            ((completedScalarIdentityMultiplication l E (Spec (.of D.k))).hom.app P.obj) := by
    simpa only [CompletedLineTensor.ordinaryUnit] using
      (CompletedLineTensor.ordinaryUnit_existsUnique l E (Spec (.of D.k))).exists.choose_spec P
  change (_ ≫ (completedScalarComparison l E E (AlgHom.id ℚ_[l] E)
    (Spec (.of D.k))).app _) ≫ _ = _
  have h' : (completedScalarComparison l E E (AlgHom.id ℚ_[l] E)
      (Spec (.of D.k))).app (DerivedCategory.Q.obj P.obj) ≫
        (integralScalarExtensionComparisonOfUniverses l E E (AlgHom.id ℚ_[l] E)
          (Spec (.of D.k))).hom.app P =
      (CompletedLineTensor.ordinaryUnit l E (Spec (.of D.k))).hom.app
        (DerivedCategory.Q.obj P.obj) ≫
          DerivedCategory.Q.map
            ((completedScalarIdentityUnit l E (Spec (.of D.k))).app P.obj) := by
    rw [hμ, Category.assoc]
    exact h
  erw [Category.assoc, h']
  exact (CompletedLineTensor.ordinaryUnit l E (Spec (.of D.k))).inv_hom_id_app_assoc _ _


private theorem completionUnit_isIso [Fact (l ≠ D.p)]
    (N : sfIntegralConstructibleCategory l E (Spec (.of D.k))) :
    IsIso ((completionUnit D l E).app N.obj) := by
  have hcomplete : IsDerivedCompleteUnrestricted l E (Spec (.of D.k)) N.obj :=
    CompletedLineTensor.intrinsic_complete l E (Spec (.of D.k)) N
  have := ((finiteFreeCompletedScalarComparison l E E (AlgHom.id ℚ_[l] E)
    (Spec (.of D.k))).2.1 N.obj hcomplete).1
  dsimp only [completionUnit, NatTrans.comp_app]
  infer_instance



private theorem combine_iso_unit
    {C B A : Type*} [Category C] [Category B] [Category A]
    (F : C ⥤ B) (H : A ⥤ B) {X Y Z : C} {U V W : A}
    (a : X ⟶ Y) (b : Y ≅ Z) (g : X ⟶ Z)
    (d : F.obj Z ≅ H.obj V) (e : F.obj X ≅ H.obj U)
    (z : U ⟶ V) (c : V ≅ W)
    (h : a ≫ b.hom = g) (h' : F.map g ≫ d.hom = e.hom ≫ H.map z) :
    F.map a ≫ (F.mapIso b ≪≫ d ≪≫ H.mapIso c).hom =
      e.hom ≫ H.map (z ≫ c.hom) := by
  simpa only [Iso.trans_hom, Functor.mapIso_hom, Functor.map_comp, Category.assoc] using
    PointQuotientAugmentation.combine_unit F a b.hom g d.hom e.hom (H.map z)
      (H.map c.hom) h h'

/-- The canonical completion comparison is an isomorphism, uniquely fixed by its
zero shifted coordinate and quotient augmentation on all resolutions.
Source: blueprint clause (3); Stacks 0941
(blueprint: lem-trf-point-sections-completion-cone).
Proof: apply finiteFreeCompletedScalarComparison to the identity extension. Its
chain normalization is completedScalarIdentityUnit, with zero shifted component
and quotient units on the other component. Derived completeness of N makes it
invertible. Compose with exact sections. The representative comparison followed
by c_P is completionModelAt, giving the displayed whole-map equality. Naturality
of the identity-extension comparison supplies a natural isomorphism for every
derived morphism. Every constructible object has a good representative; cancellation
of its localized quasi-isomorphism proves uniqueness and resolution independence. -/
theorem completionComparison_existsUnique [Fact (l ≠ D.p)] :
    ∃! α : (sfIntegralConstructible l E (Spec (.of D.k))).ι ⋙
        pointFibreIntegralAmbient D l E ≅
      (sfIntegralConstructible l E (Spec (.of D.k))).ι ⋙ completedSections D l E,
      CompletionNormalization D l E α := by
  classical
  let η := completionUnit D l E
  let α : (sfIntegralConstructible l E (Spec (.of D.k))).ι ⋙
      pointFibreIntegralAmbient D l E ≅
      (sfIntegralConstructible l E (Spec (.of D.k))).ι ⋙ completedSections D l E :=
    NatIso.ofComponents (fun N ↦ by
      haveI : IsIso (η.app N.obj) := completionUnit_isIso D l E N
      exact (pointFibreIntegralAmbient D l E).mapIso (asIso (η.app N.obj))) (by
        intro N N' f
        change (pointFibreIntegralAmbient D l E).map f.hom ≫
          (pointFibreIntegralAmbient D l E).map (η.app N'.obj) =
          (pointFibreIntegralAmbient D l E).map (η.app N.obj) ≫
            (pointFibreIntegralAmbient D l E).map ((completion D l E).map f.hom)
        simpa only [← Functor.map_comp, Functor.id_map] using
          congrArg (pointFibreIntegralAmbient D l E).map (η.naturality f.hom))
  have hα : CompletionNormalization D l E α := by
    intro N P q
    dsimp only [α, NatIso.ofComponents_hom_app, Functor.mapIso_hom, asIso_hom]
    change (pointFibreIntegralAmbient D l E).map q.hom ≫
      (pointFibreIntegralAmbient D l E).map (η.app N.obj) ≫ _ = _
    apply PointQuotientAugmentation.transport_unit_spec
      (pointFibreIntegralAmbient D l E) (completion D l E) η q
      (completionModel D l E P) (completionModelAt D l E N P q)
      rfl
    have hn := (factors D l E).hom.naturality
      ((completedScalarIdentityUnit l E (Spec (.of D.k))).app P.obj)
    exact combine_iso_unit (pointFibreIntegralAmbient D l E) (moduleQ l E)
      (η.app (DerivedCategory.Q.obj P.obj))
      ((integralScalarExtensionComparisonOfUniverses l E E (AlgHom.id ℚ_[l] E)
        (Spec (.of D.k))).app P)
      (DerivedCategory.Q.map
        ((completedScalarIdentityUnit l E (Spec (.of D.k))).app P.obj))
      ((factors D l E).app
        ((integralScalarComplexFunctor l E E (AlgHom.id ℚ_[l] E)
          (Spec (.of D.k))).obj P.obj))
      ((factors D l E).app P.obj)
      ((sections D l E).map ((completedScalarIdentityUnit l E (Spec (.of D.k))).app P.obj))
      (CompletedStalk.sectionsRoos D l E ((reductions D l E).obj P.obj))
      (completionUnit_spec D l E P) hn
  refine ⟨α, hα, ?_⟩
  intro α' hα'
  apply Iso.ext
  apply NatTrans.ext
  funext N
  have := integralOperationsGoodLocalization_isLocalization l E (Spec (.of D.k))
  let W := (HomologicalComplex.quasiIso (integralTowerModules l E (Spec (.of D.k)))
    (.up ℤ)).inverseImage (integralOperationsGoodComplex l E (Spec (.of D.k))).ι
  let := Localization.essSurj (integralOperationsGoodLocalization l E (Spec (.of D.k))) W
  let P := (integralOperationsGoodLocalization l E (Spec (.of D.k))).objPreimage N.obj
  let q : DerivedCategory.Q.obj P.obj ≅ N.obj :=
    (integralOperationsGoodLocalization l E (Spec (.of D.k))).objObjPreimageIso N.obj
  apply (cancel_epi ((pointFibreIntegralAmbient D l E).map q.hom)).1
  apply (cancel_mono (completionModelAt D l E N P q).hom).1
  simpa only [Category.assoc] using (hα' N P q).trans (hα N P q).symm


/-- The completion comparison selected by its unique whole-cone normalization.
Source: blueprint clause (3); Stacks 0941
(blueprint: lem-trf-point-sections-completion-cone). -/
def completionComparison [Fact (l ≠ D.p)] :=
  (completionComparison_existsUnique D l E).exists.choose

/-- The specified alpha_N on every resolution, with its actual evaluated quotient cone.
Source: blueprint clause (3); Stacks 0941
(blueprint: lem-trf-point-sections-completion-cone). -/
def alpha [Fact (l ≠ D.p)]
    (N : sfIntegralConstructibleCategory l E (Spec (.of D.k)))
    (P : (integralOperationsGoodComplex l E (Spec (.of D.k))).FullSubcategory)
    (q : DerivedCategory.Q.obj P.obj ≅ N.obj) :=
  (completionComparison D l E).app N ≪≫ completionModelAt D l E N P q

/-- The derived-limit property of the entire evaluated tower. The existential product
witness asserts existence; it makes no choice of a derived-limit comparison.
Source: blueprint clause (3); Stacks 08TC
(blueprint: lem-trf-point-sections-completion-cone). -/
def ModuleDerivedLimit
    (T : ℕᵒᵖ ⥤ CochainComplex
      (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E))) ℤ) : Prop :=
  ∃ hP : HasProduct (fun n : ℕ ↦ (moduleQ l E).obj (T.obj (op n))),
    @IsDerivedLimit _ _ _ _ _ (fun _n : ℤ ↦ inferInstance) _
      (fun n : ℕ ↦ (moduleQ l E).obj (T.obj (op n))) hP
      (fun n : ℕ ↦ (moduleQ l E).map (integralOperationsTowerStep T n))
      ((moduleQ l E).obj (integralOperationsRoos T))

/-- The map on H(D) induced by the already descended reduction construction, using
its specified model comparisons. It is defined independently of alpha.
Source: blueprint clause (3), derived naturality
(blueprint: lem-trf-point-sections-completion-cone). -/
def reductionMap
    {N N' : sfIntegralConstructibleCategory l E (Spec (.of D.k))} (f : N ⟶ N')
    (P P' : (integralOperationsGoodComplex l E (Spec (.of D.k))).FullSubcategory)
    (q : DerivedCategory.Q.obj P.obj ≅ N.obj)
    (q' : DerivedCategory.Q.obj P'.obj ≅ N'.obj) :=
  (completionModelAt D l E N P q).inv ≫ (completedSections D l E).map f.hom ≫
    (completionModelAt D l E N' P' q').hom

/-- The map on H(B) induced by completed pullback and its defining model comparisons.
It is defined independently of alpha and of any chosen Roos-triangle filler.
Source: blueprint clause (3), derived naturality
(blueprint: lem-trf-point-sections-completion-cone). -/
def pullbackMap
    {N N' : sfIntegralConstructibleCategory l E (Spec (.of D.k))} (f : N ⟶ N')
    (P P' : (integralOperationsGoodComplex l E (Spec (.of D.k))).FullSubcategory)
    (q : DerivedCategory.Q.obj P.obj ≅ N.obj)
    (q' : DerivedCategory.Q.obj P'.obj ≅ N'.obj) :=
  (beta D l E N P q).inv ≫ (pointFibreIntegralAmbient D l E).map
    ((integralDerivedPullback l E (frobenius D)).map f.hom) ≫
      (beta D l E N' P' q').hom

/-- Both canonical comparisons are natural for every derived morphism and every pair
of flat-term K-flat representatives. Taking f to be the identity gives independence
under the specified resolution comparisons.
Source: blueprint clause (3), comparison descent; Stacks 0941
(blueprint: lem-trf-point-sections-completion-cone). -/
def DerivedNaturality [Fact (l ≠ D.p)] : Prop :=
  ∀ (N N' : sfIntegralConstructibleCategory l E (Spec (.of D.k))) (f : N ⟶ N')
    (P P' : (integralOperationsGoodComplex l E (Spec (.of D.k))).FullSubcategory)
    (q : DerivedCategory.Q.obj P.obj ≅ N.obj)
    (q' : DerivedCategory.Q.obj P'.obj ≅ N'.obj),
    (alpha D l E N P q).hom ≫ reductionMap D l E f P P' q q' =
        (pointFibreIntegralAmbient D l E).map f.hom ≫ (alpha D l E N' P' q').hom ∧
      (beta D l E N P q).hom ≫ pullbackMap D l E f P P' q q' =
        (pointFibreIntegralAmbient D l E).map
          ((integralDerivedPullback l E (frobenius D)).map f.hom) ≫
            (beta D l E N' P' q').hom


private theorem sectionsRoos_natural
    (T U : ℕᵒᵖ ⥤ CochainComplex (integralTowerModules l E (Spec (.of D.k))) ℤ)
    (w : T ⟶ U) :
    (sections D l E).map (integralOperationsRoosMap w) ≫
        (CompletedStalk.sectionsRoos D l E U).hom =
      (CompletedStalk.sectionsRoos D l E T).hom ≫
        integralOperationsRoosMap (Functor.whiskerRight w (sections D l E)) := by
  simpa only [sectionsRoos_eq] using!
    (PointQuotientAugmentation.roosComparison
      (pointIntegralSections l E D.k)).hom.naturality w

attribute [local irreducible] frobenius completionUnit
  integralDerivedPullback integralDerivedPullbackComparison
  integralOperationsPullbackTowerFunctor


private theorem compose_naturality
    {C : Type*} [Category* C] {X₀ X₁ X₂ X₃ Y₀ Y₁ Y₂ Y₃ : C}
    (a : X₀ ⟶ X₁) (b : X₁ ⟶ X₂) (c : X₂ ⟶ X₃)
    (a' : Y₀ ⟶ Y₁) (b' : Y₁ ⟶ Y₂) (c' : Y₂ ⟶ Y₃)
    (v₀ : X₀ ⟶ Y₀) (v₁ : X₁ ⟶ Y₁) (v₂ : X₂ ⟶ Y₂) (v₃ : X₃ ⟶ Y₃)
    (h₁ : v₀ ≫ a' = a ≫ v₁) (h₂ : v₁ ≫ b' = b ≫ v₂)
    (h₃ : v₂ ≫ c' = c ≫ v₃) :
    v₀ ≫ a' ≫ b' ≫ c' = a ≫ b ≫ c ≫ v₃ := by
  rw [← Category.assoc v₀, h₁, Category.assoc, ← Category.assoc v₁,
    h₂, Category.assoc, h₃]


private theorem map_square
    {C : Type*} [Category* C] {B : Type*} [Category* B] (F : C ⥤ B)
    {X Y X' Y' : C} {a : X ⟶ Y} {a' : X' ⟶ Y'} {v : X ⟶ X'} {v' : Y ⟶ Y'}
    (h : v ≫ a' = a ≫ v') :
    F.map v ≫ F.map a' = F.map a ≫ F.map v' := by
  rw [← F.map_comp, h, F.map_comp]


private theorem compose_iso_naturality
    {C B A : Type*} [Category* C] [Category* B] [Category* A]
    (F : C ⥤ B) (H : A ⥤ B)
    {X X' Y Y' : C} {U U' V V' : A}
    (a : X ≅ Y) (a' : X' ≅ Y') (b : F.obj Y ≅ H.obj U)
    (b' : F.obj Y' ≅ H.obj U') (c : U ≅ V) (c' : U' ≅ V')
    (v₀ : X ⟶ X') (v₁ : Y ⟶ Y') (v₂ : U ⟶ U') (v₃ : V ⟶ V')
    (h₁ : F.map v₀ ≫ F.map a'.hom = F.map a.hom ≫ F.map v₁)
    (h₂ : F.map v₁ ≫ b'.hom = b.hom ≫ H.map v₂)
    (h₃ : H.map v₂ ≫ H.map c'.hom = H.map c.hom ≫ H.map v₃) :
    F.map v₀ ≫ (F.mapIso a' ≪≫ b' ≪≫ H.mapIso c').hom =
      (F.mapIso a ≪≫ b ≪≫ H.mapIso c).hom ≫ H.map v₃ := by
  simpa only [Iso.trans_hom, Functor.mapIso_hom, Category.assoc] using
    compose_naturality _ _ _ _ _ _ _ _ _ _ h₁ h₂ h₃


section FoldedModels
attribute [local irreducible] pointIntegralSections
  integralOperationsRoos integralScalarTowerFunctor

private theorem completionModel_naturality
    {P P' : (integralOperationsGoodComplex l E (Spec (.of D.k))).FullSubcategory}
    (w : P ⟶ P') :
    (completedSections D l E).map (DerivedCategory.Q.map w.hom) ≫
        (completionModel D l E P').hom =
      (completionModel D l E P).hom ≫ (moduleQ l E).map
        (integralOperationsRoosMap
          (Functor.whiskerRight ((reductions D l E).map w.hom) (sections D l E))) := by
  have h₁ := map_square (pointFibreIntegralAmbient D l E)
    ((integralScalarExtensionComparisonOfUniverses l E E (AlgHom.id ℚ_[l] E)
      (Spec (.of D.k))).hom.naturality w)
  have h₂ := (factors D l E).hom.naturality
    ((integralScalarComplexFunctor l E E (AlgHom.id ℚ_[l] E)
      (Spec (.of D.k))).map w.hom)
  have h₃ := map_square (moduleQ l E)
    (sectionsRoos_natural D l E _ _ ((reductions D l E).map w.hom))
  dsimp only [Functor.comp_map, integralOperationsGoodLocalization,
    ObjectProperty.ι_map] at h₁ h₂
  exact compose_iso_naturality (pointFibreIntegralAmbient D l E) (moduleQ l E)
    ((integralScalarExtensionComparisonOfUniverses l E E (AlgHom.id ℚ_[l] E)
      (Spec (.of D.k))).app P)
    ((integralScalarExtensionComparisonOfUniverses l E E (AlgHom.id ℚ_[l] E)
      (Spec (.of D.k))).app P')
    ((factors D l E).app ((integralScalarComplexFunctor l E E (AlgHom.id ℚ_[l] E)
      (Spec (.of D.k))).obj P.obj))
    ((factors D l E).app ((integralScalarComplexFunctor l E E (AlgHom.id ℚ_[l] E)
      (Spec (.of D.k))).obj P'.obj))
    (CompletedStalk.sectionsRoos D l E ((reductions D l E).obj P.obj))
    (CompletedStalk.sectionsRoos D l E ((reductions D l E).obj P'.obj))
    ((completion D l E).map (DerivedCategory.Q.map w.hom))
    (DerivedCategory.Q.map ((integralScalarComplexFunctor l E E (AlgHom.id ℚ_[l] E)
      (Spec (.of D.k))).map w.hom))
    ((sections D l E).map ((integralScalarComplexFunctor l E E (AlgHom.id ℚ_[l] E)
      (Spec (.of D.k))).map w.hom))
    _ h₁ h₂ h₃


private theorem pullbackModel_naturality
    {P P' : (integralOperationsGoodComplex l E (Spec (.of D.k))).FullSubcategory}
    (w : P ⟶ P') :
    (pointFibreIntegralAmbient D l E).map
        ((integralDerivedPullback l E (frobenius D)).map (DerivedCategory.Q.map w.hom)) ≫
        (pullbackModel D l E P').hom =
      (pullbackModel D l E P).hom ≫ (moduleQ l E).map
        (integralOperationsRoosMap
          (Functor.whiskerRight
            ((integralOperationsPullbackTowerFunctor l E (frobenius D)).map w.hom)
            (sections D l E))) := by
  have h₁ := map_square (pointFibreIntegralAmbient D l E)
    ((integralDerivedPullbackComparison l E (frobenius D)).hom.naturality w)
  have h₂ := (factors D l E).hom.naturality
    ((integralOperationsPullbackComplexFunctor l E (frobenius D)).map w.hom)
  have h₃ := map_square (moduleQ l E)
    (sectionsRoos_natural D l E _ _
      ((integralOperationsPullbackTowerFunctor l E (frobenius D)).map w.hom))
  dsimp only [Functor.comp_map, integralOperationsGoodLocalization,
    ObjectProperty.ι_map] at h₁ h₂
  exact compose_iso_naturality (pointFibreIntegralAmbient D l E) (moduleQ l E)
    ((integralDerivedPullbackComparison l E (frobenius D)).app P)
    ((integralDerivedPullbackComparison l E (frobenius D)).app P')
    ((factors D l E).app ((integralOperationsPullbackComplexFunctor
      l E (frobenius D)).obj P.obj))
    ((factors D l E).app ((integralOperationsPullbackComplexFunctor
      l E (frobenius D)).obj P'.obj))
    (CompletedStalk.sectionsRoos D l E
      ((integralOperationsPullbackTowerFunctor l E (frobenius D)).obj P.obj))
    (CompletedStalk.sectionsRoos D l E
      ((integralOperationsPullbackTowerFunctor l E (frobenius D)).obj P'.obj))
    ((integralDerivedPullback l E (frobenius D)).map (DerivedCategory.Q.map w.hom))
    (DerivedCategory.Q.map
      ((integralOperationsPullbackComplexFunctor l E (frobenius D)).map w.hom))
    ((sections D l E).map
      ((integralOperationsPullbackComplexFunctor l E (frobenius D)).map w.hom))
    _ h₁ h₂ h₃


end FoldedModels

private theorem naturality_with_model
    {C B : Type*} [Category* C] [Category* B] {F G : C ⥤ B}
    (a : F ≅ G) {X Y : C} (f : X ⟶ Y) {U V : B}
    (e : G.obj X ≅ U) (e' : G.obj Y ≅ V) :
    (a.app X ≪≫ e).hom ≫ (e.inv ≫ G.map f ≫ e'.hom) =
      F.map f ≫ (a.app Y ≪≫ e').hom := by
  simp only [Iso.trans_hom, Category.assoc, Iso.hom_inv_id_assoc]
  simpa only [Category.assoc, Iso.app_hom] using
    (congrArg (· ≫ e'.hom) (a.hom.naturality f)).symm


private theorem cancel_model
    {C : Type*} [Category* C] {X Y U V : C}
    (e : X ≅ U) (e' : Y ≅ V) (f : X ⟶ Y) :
    e.hom ≫ (e.inv ≫ f ≫ e'.hom) = f ≫ e'.hom := by
  exact e.hom_inv_id_assoc _


private theorem project_square
    {C : Type*} [Category* C] {X X' Y Y' Z Z' : C}
    (f : X ⟶ X') (b : X' ⟶ Y') (c : X ⟶ Y) (d : Y ⟶ Y')
    (p : Y' ⟶ Z') (r : Y ⟶ Z) (e : Z ⟶ Z')
    (h : f ≫ b = c ≫ d) (hπ : d ≫ p = r ≫ e) :
    f ≫ (b ≫ p) = (c ≫ r) ≫ e := by
  rw [← Category.assoc, h, Category.assoc, hπ, ← Category.assoc]


private theorem strictMap_coordinates
    {A : Type*} [Category* A] [Abelian A] [HasCountableProducts A]
    (T U : ℕᵒᵖ ⥤ CochainComplex A ℤ) (w : T ⟶ U) (n : ℕ) (i : ℤ) :
    (integralOperationsRoosMap w).f i ≫ CompletedStalk.roosFirst U n i =
        CompletedStalk.roosFirst T n i ≫ (w.app (op n)).f i ∧
      (integralOperationsRoosMap w).f i ≫ CompletedStalk.roosSecond U n i =
        CompletedStalk.roosSecond T n i ≫ (w.app (op n)).f (i + -1) := by
  constructor
  · obtain ⟨p, rfl⟩ : ∃ p : ℤ, i = p + 1 := ⟨i - 1, by omega⟩
    have hπ := congrArg (fun z ↦ z.f (p + 1))
      (Limits.Pi.map_π (fun n ↦ w.app (op n)) n)
    dsimp only [HomologicalComplex.comp_f] at hπ
    exact project_square _ _ _ _ _ _ _ (PointQuotientAugmentation.roosMap_fst w p) hπ
  · have hπ := congrArg (fun z ↦ z.f (i + -1))
      (Limits.Pi.map_π (fun n ↦ w.app (op n)) n)
    dsimp only [HomologicalComplex.comp_f] at hπ
    exact project_square _ _ _ _ _ _ _
      (PointQuotientAugmentation.roosMap_snd' w i (i + -1) rfl) hπ



private theorem augmentation_coordinates
    (P : CochainComplex (integralTowerModules l E (Spec (.of D.k))) ℤ) (i : ℤ) :
    (∀ (n : ℕ) (z : ((sections D l E).obj P).X i),
      (((augmentation D l E P).f i ≫
        CompletedStalk.roosFirst ((reductions D l E).obj P ⋙ sections D l E) n i).hom z) =
          integralScalarTensorSection l E E (AlgHom.id ℚ_[l] E) (Spec (.of D.k)) n
            (P.X i) (op (ProEt.mk (𝟙 (Spec (.of D.k))))) 1 z) ∧
    (∀ n : ℕ, (augmentation D l E P).f i ≫
      CompletedStalk.roosSecond ((reductions D l E).obj P ⋙ sections D l E) n i = 0) := by
  have hc := sectionsRoos_coordinates D l E ((reductions D l E).obj P)
  have hη := completedScalarIdentityUnit_spec l E (Spec (.of D.k))
  constructor
  · intro n z
    dsimp only [augmentation, HomologicalComplex.comp_f]
    erw [Category.assoc, hc.1 n i]
    change (((pointIntegralSections l E D.k).map
      (((completedScalarIdentityUnit l E (Spec (.of D.k))).app P).f i) ≫
      (pointIntegralSections l E D.k).map
        (CompletedStalk.roosFirst ((reductions D l E).obj P) n i)).hom) z = _
    erw [← Functor.map_comp]
    exact hη.1 P i n _ z
  · intro n
    dsimp only [augmentation, HomologicalComplex.comp_f]
    erw [Category.assoc, hc.2 n i]
    change (pointIntegralSections l E D.k).map
      (((completedScalarIdentityUnit l E (Spec (.of D.k))).app P).f i) ≫
        (pointIntegralSections l E D.k).map
          (CompletedStalk.roosSecond ((reductions D l E).obj P) n i) = 0
    erw [← Functor.map_comp]
    have hz : ((completedScalarIdentityUnit l E (Spec (.of D.k))).app P).f i ≫
        CompletedStalk.roosSecond ((reductions D l E).obj P) n i = 0 := by
      dsimp only [CompletedStalk.roosSecond]
      have hh := congrArg (fun z ↦ z ≫
        (Pi.π (fun m ↦ ((reductions D l E).obj P).obj (op m)) n).f (i + -1))
        (hη.2 P i)
      simpa only [Category.assoc, zero_comp, sub_eq_add_neg] using! hh
    rw [hz, Functor.map_zero]



private theorem sectionsRoos_quasiIso
    {T U : ℕᵒᵖ ⥤ CochainComplex (integralTowerModules l E (Spec (.of D.k))) ℤ}
    (w : T ⟶ U) (hw : ∀ n : ℕ, QuasiIso (w.app (op n))) :
    QuasiIso (integralOperationsRoosMap (Functor.whiskerRight w (sections D l E))) := by
  have : QuasiIso (integralOperationsRoosMap w) :=
    integralOperationsRoosQuasiIsoInvariant.{u, u} l E (Spec (.of D.k)) w hw
  have : QuasiIso ((sections D l E).map (integralOperationsRoosMap w)) := inferInstance
  have hn := sectionsRoos_natural D l E T U w
  have : QuasiIso ((CompletedStalk.sectionsRoos D l E T).hom ≫
      integralOperationsRoosMap (Functor.whiskerRight w (sections D l E))) := by
    erw [← hn]
    infer_instance
  exact quasiIso_of_comp_left (CompletedStalk.sectionsRoos D l E T).hom _


attribute [local irreducible] completionModel completionModelAt pullbackModel beta
  completionComparison

/-- Exact sections commute with the normalized completion cone, its diagonal maps,
and its localized comparisons, with the specified alpha and beta.
Source: blueprint main-20261015, prop-trf-rational-frobenius-integral-model,
proof clause (3), sectionwise cone and comparison descent; Stacks 0941
(blueprint: lem-trf-point-sections-completion-cone).

Proof, following all eight DAG steps:
1. Pro-etale products are sectionwise by lem-weil-proetale-countable-products-exact.
Exact point sections are additive and preserve binary biproducts. The product
identifications on both summands give the existing sectionsRoos, with precisely
its two projection normalizations.
2. In the signed coordinates (b,a), the differential on either side is
(-db-(1-s)a,da). Strict compatibility gives (1-s_Y)W=W(1-s_X).
Thus the existing RoosMap is diagonal on the two components, and sectionsRoos is
natural for all strict tower maps, not only maps between individual levels.
3. Products of surjections of modules are surjective by coordinatewise lifting.
The sheaf-module and ordinary-module categories therefore have exact countable
products. Apply lem-weil-derived-limit-products-core to both whole towers. Their
mapping-cocone triangles are Roos triangles, proving both derived-limit assertions.
4. Exact products preserve levelwise quasi-isomorphisms, so the cone does too.
Exact sections preserve quasi-isomorphisms. The naturality square consequently
also holds for their inverses after localization, and then for arbitrary roofs.
This is the strict-cone descent of lem-weil-strict-roos-comparison.
5. Derived change of rings computes all N_n on the single good representative P;
finite exact inverse image computes g_n*P_n. The actual quotient transitions are
those of reductions and integralOperationsPullbackTowerFunctor. Thus the two
evaluated cones represent exactly the two claimed derived inverse limits.
6. The identity-extension specialization of finiteFreeCompletedScalarComparison
is the specified completeness unit. On P its shifted coordinate is zero and its
unshifted coordinates are x mapped to x tensor 1. Composing exact sections with
sectionsRoos is exactly augmentation. Derived completeness makes it invertible.
7. The defining integralDerivedPullbackComparison identifies Lg*N with the
actual Roos complex on C. Exact sections, factors, and sectionsRoos on C are
precisely beta, fixing both its product components.
8. The two descended constructions and their representative comparisons are
natural on every derived morphism. Combine their naturality with step 2 to obtain
DerivedNaturality, including identity morphisms between any two resolutions.
No arbitrary comparison between separately chosen Roos triangles enters. -/
theorem pointSectionsCompletionCone [Fact (l ≠ D.p)] :
    (∀ T : ℕᵒᵖ ⥤ CochainComplex (integralTowerModules l E (Spec (.of D.k))) ℤ,
      (∀ (n : ℕ) (i : ℤ),
        (CompletedStalk.sectionsRoos D l E T).hom.f i ≫
            CompletedStalk.roosFirst (T ⋙ sections D l E) n i =
          (pointIntegralSections l E D.k).map (CompletedStalk.roosFirst T n i)) ∧
      (∀ (n : ℕ) (i : ℤ),
        (CompletedStalk.sectionsRoos D l E T).hom.f i ≫
            CompletedStalk.roosSecond (T ⋙ sections D l E) n i =
          (pointIntegralSections l E D.k).map (CompletedStalk.roosSecond T n i)) ∧
      integralOperationsDerivedLimitProperty l E (Spec (.of D.k)) T
          (DerivedCategory.Q.obj (integralOperationsRoos T)) ∧
        ModuleDerivedLimit l E (T ⋙ sections D l E)) ∧
    (∀ (T U : ℕᵒᵖ ⥤ CochainComplex (integralTowerModules l E (Spec (.of D.k))) ℤ)
      (w : T ⟶ U),
      (sections D l E).map (integralOperationsRoosMap w) ≫
          (CompletedStalk.sectionsRoos D l E U).hom =
        (CompletedStalk.sectionsRoos D l E T).hom ≫
          integralOperationsRoosMap (Functor.whiskerRight w (sections D l E))) ∧
    (∀ (T U : ℕᵒᵖ ⥤ CochainComplex (integralTowerModules l E (Spec (.of D.k))) ℤ)
      (w : T ⟶ U) (n : ℕ) (i : ℤ),
      (integralOperationsRoosMap w).f i ≫ CompletedStalk.roosFirst U n i =
          CompletedStalk.roosFirst T n i ≫ (w.app (op n)).f i ∧
        (integralOperationsRoosMap w).f i ≫ CompletedStalk.roosSecond U n i =
          CompletedStalk.roosSecond T n i ≫ (w.app (op n)).f (i + -1)) ∧
    (∀ (T U : ℕᵒᵖ ⥤ CochainComplex (integralTowerModules l E (Spec (.of D.k))) ℤ)
      (w : T ⟶ U),
      (∀ n : ℕ, QuasiIso (w.app (op n))) →
        QuasiIso (integralOperationsRoosMap w) ∧
        QuasiIso (integralOperationsRoosMap (Functor.whiskerRight w (sections D l E)))) ∧
    (∀ (P : CochainComplex (integralTowerModules l E (Spec (.of D.k))) ℤ)
      (i : ℤ),
      (∀ (n : ℕ) (z : ((sections D l E).obj P).X i),
        (((augmentation D l E P).f i ≫
          CompletedStalk.roosFirst ((reductions D l E).obj P ⋙ sections D l E) n i).hom z) =
            integralScalarTensorSection l E E (AlgHom.id ℚ_[l] E) (Spec (.of D.k)) n
              (P.X i) (op (ProEt.mk (𝟙 (Spec (.of D.k))))) 1 z) ∧
      (∀ n : ℕ, (augmentation D l E P).f i ≫
        CompletedStalk.roosSecond ((reductions D l E).obj P ⋙ sections D l E) n i = 0)) ∧
    (∀ (N : sfIntegralConstructibleCategory l E (Spec (.of D.k)))
      (P : (integralOperationsGoodComplex l E (Spec (.of D.k))).FullSubcategory)
      (q : DerivedCategory.Q.obj P.obj ≅ N.obj),
      (pointFibreIntegralAmbient D l E).map q.hom ≫ (alpha D l E N P q).hom =
        (factors D l E).hom.app P.obj ≫ (moduleQ l E).map (augmentation D l E P.obj)) ∧
    (∀ (N N' : sfIntegralConstructibleCategory l E (Spec (.of D.k))) (f : N ⟶ N')
      (P P' : (integralOperationsGoodComplex l E (Spec (.of D.k))).FullSubcategory)
      (q : DerivedCategory.Q.obj P.obj ≅ N.obj)
      (q' : DerivedCategory.Q.obj P'.obj ≅ N'.obj) (w : P ⟶ P'),
      q.hom ≫ f.hom = DerivedCategory.Q.map w.hom ≫ q'.hom →
        reductionMap D l E f P P' q q' =
            (moduleQ l E).map (integralOperationsRoosMap
              (Functor.whiskerRight ((reductions D l E).map w.hom) (sections D l E))) ∧
          pullbackMap D l E f P P' q q' =
            (moduleQ l E).map (integralOperationsRoosMap
              (Functor.whiskerRight
                ((integralOperationsPullbackTowerFunctor l E (frobenius D)).map w.hom)
                (sections D l E)))) ∧
    DerivedNaturality D l E := by
  refine ⟨?_, sectionsRoos_natural D l E, strictMap_coordinates, ?_,
    augmentation_coordinates D l E, ?_, ?_, ?_⟩
  · intro T
    have hc := sectionsRoos_coordinates D l E T
    refine ⟨hc.1, hc.2, integralOperationsRoosDerivedLimit l E (Spec (.of D.k)) T, ?_⟩
    exact PointQuotientAugmentation.module_roos_limit
      (ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E)) (T ⋙ sections D l E)
  · intro T U w hw
    exact ⟨integralOperationsRoosQuasiIsoInvariant.{u, u} l E (Spec (.of D.k)) w hw,
      sectionsRoos_quasiIso D l E w hw⟩
  · intro N P q
    change (pointFibreIntegralAmbient D l E).map q.hom ≫
      (completionComparison D l E).hom.app N ≫ (completionModelAt D l E N P q).hom = _
    unfold completionComparison
    exact (completionComparison_existsUnique D l E).exists.choose_spec N P q
  · intro N N' f P P' q q' w hw
    constructor
    · exact PointQuotientAugmentation.transport_map_spec (completedSections D l E) q q'
        (completionModel D l E P) (completionModel D l E P')
        (completionModelAt D l E N P q) (completionModelAt D l E N' P' q')
        (by unfold completionModelAt; rfl) (by unfold completionModelAt; rfl)
        f.hom (DerivedCategory.Q.map w.hom) _ hw (completionModel_naturality D l E w)
    · exact PointQuotientAugmentation.transport_map_spec
        (integralDerivedPullback l E (frobenius D) ⋙ pointFibreIntegralAmbient D l E)
        q q' (pullbackModel D l E P) (pullbackModel D l E P')
        (beta D l E N P q) (beta D l E N' P' q')
        (by unfold beta; rfl) (by unfold beta; rfl)
        f.hom (DerivedCategory.Q.map w.hom) _ hw (pullbackModel_naturality D l E w)
  · intro N N' f P P' q q'
    constructor
    · exact naturality_with_model (completionComparison D l E) f
        (completionModelAt D l E N P q) (completionModelAt D l E N' P' q')
    · exact cancel_model (beta D l E N P q) (beta D l E N' P' q')
        ((pointFibreIntegralAmbient D l E).map
          ((integralDerivedPullback l E (frobenius D)).map f.hom))


end Proof

end WeilConjectures.PointSectionsCompletionCone
