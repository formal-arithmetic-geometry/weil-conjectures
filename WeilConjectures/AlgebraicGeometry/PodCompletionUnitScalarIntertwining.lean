/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.PodCompletionScalarFormulas
public import WeilConjectures.AlgebraicGeometry.FiniteCoefficientPoint
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralCoefficientGerm
public import WeilConjectures.AlgebraicGeometry.CoefDerivedSystemEvaluationCalculus
public import WeilConjectures.AlgebraicGeometry.CompletionUnitStrictQuotientModel
public import WeilConjectures.AlgebraicGeometry.DerivedCompleteOnSlices
public import WeilConjectures.AlgebraicGeometry.PurNormalizedReconstructionAdjunctionCalculus
public import WeilConjectures.Algebra.Homology.OrdinaryDerivedChangeOfRings
public import WeilConjectures.AlgebraicGeometry.IntegralScalarExtensionWellDefined
public import WeilConjectures.AlgebraicGeometry.FiniteFreeCompletedScalarComparison
import all WeilConjectures.AlgebraicGeometry.FiniteFreeCompletedScalarComparison
import all WeilConjectures.Algebra.Homology.FiniteFreeCompletionExchange
import WeilConjectures.AlgebraicGeometry.CompletedIntegralPrincipalUnitCriterion
import WeilConjectures.AlgebraicGeometry.PodQuotientAdjunctionRealization
import WeilConjectures.AlgebraicGeometry.PodScalarMultiplicationRealization
import WeilConjectures.AlgebraicGeometry.PodSameIndexUnitDescent
public import WeilConjectures.Algebra.Homology.FiniteFreeCompletionExchange
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import WeilConjectures.CategoryTheory.StrictRoosComparison
public import WeilConjectures.CategoryTheory.RingedStrictTowerHomotopyLimitOfUniverses
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import WeilConjectures.CategoryTheory.Limits.TowerTransitionEndomorphism
public import WeilConjectures.CategoryTheory.StrictRoosDerivation
public import WeilConjectures.CategoryTheory.StrictRoosModel
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.Algebra.Homology.Functor
public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCocone
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
public import WeilConjectures.Algebra.Homology.RoosComplex
public import WeilConjectures.Algebra.Homology.DerivedCategory.TowerLimit
public import WeilConjectures.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
public import WeilConjectures.CategoryTheory.Sites.RGammaDerivedLimitSupplement
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.CategoryTheory.Adjunction.Evaluation
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import WeilConjectures.CategoryTheory.StrictRoosNormalization
public import WeilConjectures.AlgebraicGeometry.PrincipalKoszulStrictReplacement
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
public import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.RingTheory.Flat.CategoryTheory
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
public import Mathlib.CategoryTheory.Limits.Final
import WeilConjectures.AlgebraicGeometry.ProEtaleProductsExact
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import WeilConjectures.AlgebraicGeometry.ProEtaleSectionsLimitsColimits
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.CategoryTheory.Sites.Sheaf
import WeilConjectures.CategoryTheory.Sites.WeaklyContractible
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.CategoryTheory.Limits.HasLimits
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Colimits
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import WeilConjectures.AlgebraicGeometry.ProEtaleWeaklyContractibleEvaluationColimitsSupplement
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
import WeilConjectures.CategoryTheory.Sites.RGammaDerivedLimitSupplement
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Coseparator
import WeilConjectures.AlgebraicGeometry.ProEtale.SectionsConservative
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
import WeilConjectures.AlgebraicGeometry.WContractibleAffineCover
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import WeilConjectures.RingTheory.ProEtale.WContractible
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.RingTheory.RingHom.FaithfullyFlat
import WeilConjectures.RingTheory.IndPrincipalZariski
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.CategoryTheory.Limits.Preserves.Limits
import WeilConjectures.Algebra.Homology.PrincipalQuotientCompletionExists
import WeilConjectures.Algebra.Homology.FiniteFreeQuotientRoosComparison
import Mathlib.Algebra.CharP.CharAndCard

/-! # Completion units and coefficient scalar extension at the geometric point

Source: the first sentence of the proof of lem-pod-point-dualizing-complex,
Bhatt--Scholze Definitions 3.5.2--3.5.3, Lemmas 3.5.7 and 6.8.2(1).
(blueprint: lem-pod-completion-unit-scalar-intertwining).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology
attribute [-instance] WeilConjectures.integralOperationsCommHasDerivedCategory
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
attribute [-instance] WeilConjectures.integralOperationsAbLocallyBijective
attribute [-instance] WeilConjectures.integralOperationsAbSheafify
attribute [-instance] WeilConjectures.PrincipalKoszulStrictReplacement.abSheafify
attribute [-instance] WeilConjectures.PrincipalKoszulStrictReplacement.abLocallyBijective
attribute [-instance] WeilConjectures.PrincipalKoszulStrictReplacement.siteSmall


attribute [local irreducible] WeilConjectures.completedCoefficientMap
attribute [local irreducible] WeilConjectures.completedScalarChangeData
attribute [local irreducible] HasDerivedCategory.standard
attribute [local instance 5000] WeilConjectures.integralTowerHasDerivedCategory
attribute [local irreducible] CategoryTheory.PrincipalQuotientCompletion.quotientTower
  CategoryTheory.roosF SheafOfModules.monoidalCategory

universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open CategoryTheory.PrincipalQuotientCompletion
namespace WeilConjectures.PodCompletionScalar

/-- The geometric point fixed by the global finite-field datum.
Source: blueprint point dualizing complex, first proof sentence
(blueprint: lem-pod-completion-unit-scalar-intertwining). -/
abbrev point (D : FiniteFieldDatum.{t}) : Scheme.{t} := Spec (.of D.k)

variable (D : FiniteFieldDatum.{t}) (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)

/-- The actual reduction followed by total inverse limit, with its given adjunction.
Source: Bhatt--Scholze Definition 3.5.2 and the evaluation calculus
(blueprint: lem-pod-completion-unit-scalar-intertwining). -/
abbrev completion (A : CoefficientDerivedSystemCalculus l E (point D)) :=
  A.reduction ⋙ coefficientSequenceLimit l E (point D)

/-- The existing strict quotient completion interface, at the coefficient sizes of
this point. Source: Bhatt--Scholze Definition 3.5.2
(blueprint: lem-pod-completion-unit-scalar-intertwining). -/
abbrev quotientModel :=
  @Model.{t + 1, t, max u (t + 1), max u (t + 1) + 1}
    (point D).ProEt inferInstance (essentiallySmallSelf.{u} _)
    (Scheme.ProEt.topology (point D)) inferInstance
    (integralCoefficientAbSheafify.{t, u} (point D))
    (integralCoefficientAbLocallyBijective.{t, u} (point D))
    (completedIntegralCommRingSheafUnrestricted l E (point D))
    (integralTowerHasDerivedCategory l E (point D))
    (PrincipalKoszulStrictReplacement.uniformizer l E (point D))

/-- The existing ordinary/derived change-of-rings interface at the unchanged site sizes.
Source: Stacks 06YT, used in the scalar comparison
(blueprint: lem-pod-completion-unit-scalar-intertwining). -/
abbrev scalarModel :=
  @SheafOfModules.DerivedChangeOfRingsCochainModel.{t + 1, t, max u (t + 1),
    max u (t + 1) + 1, max u (t + 1) + 1}
    (point D).ProEt inferInstance (essentiallySmallSelf.{u} _)
    (Scheme.ProEt.topology (point D)) inferInstance
    (integralCoefficientAbLocallyBijective.{t, u} (point D))
    (integralCoefficientAbSheafify.{t, u} (point D))
    (completedIntegralCommRingSheafUnrestricted l E (point D))
    (completedIntegralCommRingSheafUnrestricted l L (point D))
    (completedCoefficientMap l E L ι (point D))
    (integralTowerHasDerivedCategory l E (point D))
    (integralTowerHasDerivedCategory l L (point D))

/-- The strict quotient cone is identified with the actual simultaneous reduction/limit
functor on every flat-term K-flat representative. The tower comparison is fixed by
its quotient augmentations, so it includes every quotient transition.
Source: Bhatt--Scholze Definitions 3.5.2--3.5.3; the unit-model normalization
(blueprint: lem-pod-completion-unit-scalar-intertwining). -/
def QuotientRealization (A : CoefficientDerivedSystemCalculus l E (point D))
    (M : CompletionUnit.OrdinaryModel l E (point D))
    (N : CompletionUnit.DerivedModel l E (point D) A M)
    (CR : quotientModel D l E) (α : CR.completion ≅ completion D l E A) : Prop :=
  ModelData.QuotientRealization l E (point D) A M N CR α


/-- The actual quotient identifications commute with the consecutive quotient maps.
Source: extracted coefficient calculation, proof step 1
(blueprint: lem-pod-completion-unit-scalar-intertwining). -/
def QuotientTransitions : Prop :=
  ∀ n : ℕ,
    principalReductionTransition
        (completedIntegralCommRingSheafUnrestricted l E (point D))
        (PrincipalKoszulStrictReplacement.uniformizer l E (point D)) n ≫
        (CochainComplex.singleFunctor (integralTowerModules l E (point D)) 0).map
          (PrincipalKoszulStrictReplacement.quotientComparison l E (point D) n) =
      (CochainComplex.singleFunctor (integralTowerModules l E (point D)) 0).map
          (PrincipalKoszulStrictReplacement.quotientComparison l E (point D) (n + 1)) ≫
        (CochainComplex.singleFunctor (integralTowerModules l E (point D)) 0).map
          (PrincipalKoszulStrictReplacement.residueStep l E (point D) n)

/-- The same-index scalar map before localization. Its finite maps are fixed by
quotient augmentations (equivalently, the balanced residue formula); the product
comparison and both signed cone coordinates are prescribed, independently of a basis.
Source: the extracted coefficient calculation, proof steps 5--6
(blueprint: lem-pod-completion-unit-scalar-intertwining). -/
def SameIndexFormula (F : scalarModel D l E L ι)
    (CR : quotientModel D l E) (CS : quotientModel D l L)
    (b : CR.completion ⋙ F.T ⟶ F.T ⋙ CS.completion)
    (P : CochainComplex (integralTowerModules l E (point D)) ℤ) : Prop :=
  ModelData.SameIndexFormula l E L ι (point D) F CR CS b P


/-- Multiplication identifies the target principal quotient tower with the specified
finite-coefficient tower. The formula on quotient tensor generators fixes multiplication
and its inverse, and both Roos coordinates fix its cone realization.
Source: Bhatt--Scholze Lemma 6.8.2(1), extracted proof step 3
(blueprint: lem-pod-completion-unit-scalar-intertwining). -/
def MultiplicationFormula (F : scalarModel D l E L ι)
    (hE : F.E = completedOrdinaryScalarExtension l E L ι (point D))
    (CS : quotientModel D l L)
    (c : F.T ⋙ CS.completion ≅ integralScalarExtensionOfUniverses l E L ι (point D))
    (P : (integralOperationsGoodComplex l E (point D)).FullSubcategory) : Prop :=
  ModelData.MultiplicationFormula l E L ι (point D) F hE CS c P

/-- Transport the explicitly specified quotient-cone scalar map to the actual
completion functors and the recorded derived scalar extension, by their canonical
comparison isomorphisms. This definition only composes the supplied comparisons.
Source: extracted coefficient calculation, proof steps 2, 5--6
(blueprint: lem-pod-completion-unit-scalar-intertwining). -/
def actualSameIndex (A : CoefficientDerivedSystemCalculus l E (point D))
    (B : CoefficientDerivedSystemCalculus l L (point D))
    (F : scalarModel D l E L ι)
    (σ : F.T ≅ completedDerivedScalarExtension l E L ι (point D))
    (CR : quotientModel D l E) (CS : quotientModel D l L)
    (α : CR.completion ≅ completion D l E A)
    (γ : CS.completion ≅ completion D l L B)
    (b : CR.completion ⋙ F.T ⟶ F.T ⋙ CS.completion) :
    completion D l E A ⋙ completedDerivedScalarExtension l E L ι (point D) ⟶
      completedDerivedScalarExtension l E L ι (point D) ⋙ completion D l L B :=
  Functor.whiskerRight α.inv (completedDerivedScalarExtension l E L ι (point D)) ≫
    Functor.whiskerLeft CR.completion σ.inv ≫ b ≫
    Functor.whiskerLeft F.T γ.hom ≫ Functor.whiskerRight σ.hom (completion D l L B)

private theorem quotientTransitions : QuotientTransitions D l E := by
  intro n
  rw [principalReductionTransition, ← Functor.map_comp, ← Functor.map_comp]
  apply congrArg (CochainComplex.singleFunctor (integralTowerModules l E (point D)) 0).map
  apply (cancel_epi
    (cokernel.π (PrincipalKoszulStrictReplacement.multiplication l E (point D) (n + 1)))).1
  have hp : PrincipalKoszulStrictReplacement.projection l E (point D) (n + 1) ≫
      PrincipalKoszulStrictReplacement.residueStep l E (point D) n =
        PrincipalKoszulStrictReplacement.projection l E (point D) n := by
    apply (PrincipalKoszulStrictReplacement.residue l E (point D) n).unitHomEquiv.injective
    rw [SheafOfModules.unitHomEquiv_comp_apply]
    simp only [PrincipalKoszulStrictReplacement.projection, Equiv.apply_symm_apply]
    ext U
    change (integralCoefficientSheafTransition l E (point D) n).hom.app U 1 = 1
    exact map_one _
  simpa only [PrincipalKoszulStrictReplacement.quotientComparison,
    cokernel.π_desc_assoc, cokernel.π_desc] using hp.symm

private theorem sameIndex_actual_unit
    (A : CoefficientDerivedSystemCalculus l E (point D))
    (B : CoefficientDerivedSystemCalculus l L (point D))
    (F : scalarModel D l E L ι)
    (σ : F.T ≅ completedDerivedScalarExtension l E L ι (point D))
    (CR : quotientModel D l E) (CS : quotientModel D l L)
    (α : CR.completion ≅ completion D l E A)
    (γ : CS.completion ≅ completion D l L B)
    (b : CR.completion ⋙ F.T ⟶ F.T ⋙ CS.completion)
    (hα : ∀ K, CR.unit.app K ≫ α.hom.app K = A.adjunction.unit.app K)
    (hγ : ∀ K, CS.unit.app K ≫ γ.hom.app K = B.adjunction.unit.app K)
    (hb : ∀ K, F.T.map (CR.unit.app K) ≫ b.app K = CS.unit.app (F.T.obj K))
    (K : DerivedCategory (integralTowerModules l E (point D))) :
    (completedDerivedScalarExtension l E L ι (point D)).map
        (A.adjunction.unit.app K) ≫
      (actualSameIndex D l E L ι A B F σ CR CS α γ b).app K =
        B.adjunction.unit.app
          ((completedDerivedScalarExtension l E L ι (point D)).obj K) := by
  let T := completedDerivedScalarExtension l E L ι (point D)
  have ha : A.adjunction.unit.app K ≫ α.inv.app K = CR.unit.app K := by
    rw [← hα K]
    simp only [Category.assoc, Iso.hom_inv_id_app, Category.comp_id]
  dsimp only [actualSameIndex, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app]
  simp only [← Category.assoc]
  rw [← T.map_comp, ha]
  rw [σ.inv.naturality (CR.unit.app K)]
  simp only [Category.assoc]
  rw [reassoc_of% (hb K), reassoc_of% (hγ (F.T.obj K))]
  rw [← B.adjunction.unit.naturality (σ.hom.app K)]
  change σ.inv.app K ≫ σ.hom.app K ≫ _ = _
  rw [Iso.inv_hom_id_app_assoc]

private theorem conjugated_unit
    {C H : Type*} [Category C] [Category H]
    (R : C ⥤ C) (S : H ⥤ H) (T U : C ⥤ H)
    (u : 𝟭 C ⟶ R) (v : 𝟭 H ⟶ S) (χ : T ⟶ U)
    (b : R ⋙ T ⟶ T ⋙ S) (K : C)
    (uK : K ≅ R.obj K) (huK : uK.hom = u.app K)
    (χK : T.obj K ≅ U.obj K) (hχK : χK.hom = χ.app K)
    (χH : T.obj (R.obj K) ≅ U.obj (R.obj K))
    (hχH : χH.hom = χ.app (R.obj K))
    (uX : U.obj K ≅ S.obj (U.obj K)) (huX : uX.hom = v.app (U.obj K))
    (hb : T.map (u.app K) ≫ b.app K = v.app (T.obj K)) :
    let β := (U.mapIso uK).symm ≪≫ uX
    β.hom = χH.inv ≫ b.app K ≫ S.map χK.hom ∧
      β.hom ≫ uX.inv = U.map uK.inv := by
  dsimp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_inv]
  constructor
  · apply (cancel_epi χH.hom).1
    simp only [Iso.hom_inv_id_assoc]
    have hn := χ.naturality uK.inv
    rw [← hχK, ← hχH] at hn
    rw [← Category.assoc, ← hn, Category.assoc, huX]
    have hv : χK.hom ≫ v.app (U.obj K) = v.app (T.obj K) ≫ S.map χK.hom :=
      v.naturality χK.hom
    rw [hv]
    have ht : T.map uK.inv ≫ v.app (T.obj K) = b.app K := by
      rw [← hb, ← Category.assoc, ← T.map_comp, ← huK, Iso.inv_hom_id,
        CategoryTheory.Functor.map_id, Category.id_comp]
    simpa only [Category.assoc] using congrArg (fun f ↦ f ≫ S.map χK.hom) ht
  · simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem normalizedScalarModel :
      ∃ (F : scalarModel D l E L ι)
        (hE : F.E = completedOrdinaryScalarExtension l E L ι (point D))
        (σ : F.T ≅ completedDerivedScalarExtension l E L ι (point D)),
        ∀ P : CochainComplex (integralTowerModules l E (point D)) ℤ,
          σ.hom.app (DerivedCategory.Q.obj P) ≫
              completedScalarCounit l E L ι (point D) P =
            F.ε.app P ≫ DerivedCategory.Q.map
              ((NatIso.mapHomologicalComplex (eqToIso hE) (.up ℤ)).hom.app P) := by
  let F : scalarModel D l E L ι := completedScalarCochainModel l E L ι (point D)
  let hE : F.E = completedOrdinaryScalarExtension l E L ι (point D) := rfl
  let σ : F.T ≅ completedDerivedScalarExtension l E L ι (point D) := Iso.refl _
  have hσ (P : CochainComplex (integralTowerModules l E (point D)) ℤ) :
      σ.hom.app (DerivedCategory.Q.obj P) ≫ completedScalarCounit l E L ι (point D) P =
        F.ε.app P ≫ DerivedCategory.Q.map
          ((NatIso.mapHomologicalComplex (eqToIso hE) (.up ℤ)).hom.app P) := by
    have hmap : (NatIso.mapHomologicalComplex (eqToIso hE) (.up ℤ)).hom.app P =
        𝟙 ((F.E.mapHomologicalComplex (.up ℤ)).obj P) := by
      exact NatTrans.congr_app (NatTrans.mapHomologicalComplex_id (.up ℤ) F.E) P
    rw [hmap, DerivedCategory.Q.map_id]
    exact (Category.id_comp _).trans
      ((completedScalarCochainModel_counit l E L ι (point D) P).symm.trans
        (Category.comp_id _).symm)
  exact ⟨F, hE, σ, hσ⟩

attribute [local irreducible] WeilConjectures.integralScalarExtensionOfUniverses
  WeilConjectures.integralScalarExtensionComparisonOfUniverses
  WeilConjectures.integralScalarTowerFunctor WeilConjectures.integralScalarComplexFunctor
  WeilConjectures.integralScalarTensorSection WeilConjectures.completedScalarTensorSection
  WeilConjectures.completedScalarRoosEndomorphism WeilConjectures.completedScalarComparison

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- The coefficient quotient identifications, the same-index cone comparison and its
completed conjugation intertwine the actual reconstruction inverses at the geometric point.
Source: the first sentence of lem-pod-point-dualizing-complex.proof.md;
Bhatt--Scholze Definitions 3.5.2--3.5.3, Lemmas 3.5.7 and 6.8.2(1).
(blueprint: lem-pod-completion-unit-scalar-intertwining).

Proof plan, following the nine DAG steps:
1. Principal Koszul strict replacement identifies the actual projected quotients and
   their transitions for E and L, and makes both uniformizers regular.
2. Exact countable products and strict Roos comparison compute the reduction/limit
   completion. CompletionUnit's strict quotient model identifies its entire augmentation,
   including zero shifted coordinate, with the actual adjunction unit.
3. Change of rings preserves K-flatness and flat terms. Multiplication identifies
   (P tensor S) tensor B_L,n with P tensor B_L,n, naturally in the strict towers and
   both cone coordinates, and identifies chi with the actual target unit.
4. Completed integral finite freeness and the DVR ramification t=a w^e, e positive,
   verify finite-free completion exchange. It gives the arithmetic-subsequence exchange
   and its whole-unit equation; ordinary scalar extension is exact.
5. Construct the same-index balanced maps from the actual commuting residue projections.
   Their product map commutes with 1-shift; applying it to both signed cone coordinates
   gives a chain map, independent of the basis used to check finite-free tensor/product.
6. Derived change of rings and strict Roos invariance invert quasi-isomorphisms of
   resolving complexes. Site tensor descent and localization's natural-transformation
   universal property descend that chain map naturally and independently of representatives.
7. Its composite with the actual source unit has quotient coordinates p tensor residue(z)
   and zero shifted coordinate, hence is the entire target unit by step 2.
8. On complete inputs reconstruction inverts the source unit. Cancel it in the two
   unit equations to identify the already constructed same-index map with exchange.
9. Naturality of the actual target unit and chi gives the displayed conjugation beta.
   Its composite with the inverse target unit equals completed extension of the inverse
   source unit. Finite-free scalar comparison supplies all completeness and invertibility
   assertions. No boundedness, constructibility or finite Tor amplitude is used; e may
   exceed one, so ramified extensions are included. -/
theorem completionUnitScalarIntertwining (_hl : l ≠ D.p) :
    (∀ n : ℕ, IsIso (PrincipalKoszulStrictReplacement.quotientComparison l E (point D) n) ∧
      IsIso (PrincipalKoszulStrictReplacement.quotientComparison l L (point D) n)) ∧
    QuotientTransitions D l E ∧ QuotientTransitions D l L ∧
    ∃ (A : CoefficientDerivedSystemCalculus l E (point D))
      (B : CoefficientDerivedSystemCalculus l L (point D))
      (ME : CompletionUnit.OrdinaryModel l E (point D))
      (ML : CompletionUnit.OrdinaryModel l L (point D))
      (NE : CompletionUnit.DerivedModel l E (point D) A ME)
      (NL : CompletionUnit.DerivedModel l L (point D) B ML)
      (CR : quotientModel D l E) (CS : quotientModel D l L)
      (α : CR.completion ≅ completion D l E A)
      (γ : CS.completion ≅ completion D l L B)
      (F : scalarModel D l E L ι)
      (hE : F.E = completedOrdinaryScalarExtension l E L ι (point D))
      (σ : F.T ≅ completedDerivedScalarExtension l E L ι (point D))
      (c : F.T ⋙ CS.completion ≅ integralScalarExtensionOfUniverses l E L ι (point D))
      (b : CR.completion ⋙ F.T ⟶ F.T ⋙ CS.completion)
      (ε : CR.completion ⋙ F.T ≅ F.T ⋙ CS.completion) (e : ℕ),
      QuotientRealization D l E A ME NE CR α ∧
      QuotientRealization D l L B ML NL CS γ ∧
      (∀ P : CochainComplex (integralTowerModules l E (point D)) ℤ,
        σ.hom.app (DerivedCategory.Q.obj P) ≫
            completedScalarCounit l E L ι (point D) P =
          F.ε.app P ≫ DerivedCategory.Q.map
            ((NatIso.mapHomologicalComplex (eqToIso hE) (.up ℤ)).hom.app P)) ∧
      (∀ P : (integralOperationsGoodComplex l E (point D)).FullSubcategory,
        MultiplicationFormula D l E L ι F hE CS c P) ∧
      (∀ K : DerivedCategory (integralTowerModules l E (point D)),
        (completedScalarComparison l E L ι (point D)).app K =
          σ.inv.app K ≫ CS.unit.app (F.T.obj K) ≫ c.hom.app K) ∧
      (∀ P : (integralOperationsGoodComplex l E (point D)).FullSubcategory,
        SameIndexFormula D l E L ι F CR CS b P.obj) ∧
      (∀ K : DerivedCategory (integralTowerModules l E (point D)),
        F.T.map (CR.unit.app K) ≫ b.app K = CS.unit.app (F.T.obj K)) ∧
      1 ≤ e ∧
      (∀ P : (integralOperationsGoodComplex l E (point D)).FullSubcategory,
        Nonempty (@CategoryTheory.PrincipalQuotientCompletion.RepresentativeComparison.{t + 1, t,
          max u (t + 1), max u (t + 1) + 1, max u (t + 1) + 1}
          (point D).ProEt inferInstance (essentiallySmallSelf.{u} _)
          (Scheme.ProEt.topology (point D)) inferInstance
          (integralCoefficientAbSheafify.{t, u} (point D))
          (integralCoefficientAbLocallyBijective.{t, u} (point D))
          (completedIntegralCommRingSheafUnrestricted l E (point D))
          (completedIntegralCommRingSheafUnrestricted l L (point D))
          (completedCoefficientMap l E L ι (point D))
          (integralTowerHasDerivedCategory l E (point D))
          (integralTowerHasDerivedCategory l L (point D)) F
          (PrincipalKoszulStrictReplacement.uniformizer l E (point D))
          (PrincipalKoszulStrictReplacement.uniformizer l L (point D)) e CR CS ε P.obj)) ∧
      (∀ K : DerivedCategory (integralTowerModules l E (point D)),
        F.T.map (CR.unit.app K) ≫ ε.hom.app K = CS.unit.app (F.T.obj K)) ∧
      ∀ (K : DerivedCategory (integralTowerModules l E (point D)))
        (_hK : IntegralOnSlice.IsComplete l E (point D) none K),
        b.app K = ε.hom.app K ∧
        IntegralOnSlice.IsComplete l E (point D) none ((completion D l E A).obj K) ∧
        IntegralOnSlice.IsComplete l L (point D) none
          ((completedDerivedScalarExtension l E L ι (point D)).obj K) ∧
        IntegralOnSlice.IsComplete l L (point D) none
          ((integralScalarExtensionOfUniverses l E L ι (point D)).obj K) ∧
        ∃ (uK : K ≅ (completion D l E A).obj K)
          (χK : (completedDerivedScalarExtension l E L ι (point D)).obj K ≅
            (integralScalarExtensionOfUniverses l E L ι (point D)).obj K)
          (χH : (completedDerivedScalarExtension l E L ι (point D)).obj
              ((completion D l E A).obj K) ≅
            (integralScalarExtensionOfUniverses l E L ι (point D)).obj
              ((completion D l E A).obj K))
          (uX : (integralScalarExtensionOfUniverses l E L ι (point D)).obj K ≅
            (completion D l L B).obj
              ((integralScalarExtensionOfUniverses l E L ι (point D)).obj K))
          (β : (integralScalarExtensionOfUniverses l E L ι (point D)).obj
              ((completion D l E A).obj K) ≅
            (completion D l L B).obj
              ((integralScalarExtensionOfUniverses l E L ι (point D)).obj K)),
          uK.hom = A.adjunction.unit.app K ∧
          χK.hom = (completedScalarComparison l E L ι (point D)).app K ∧
          χH.hom = (completedScalarComparison l E L ι (point D)).app
            ((completion D l E A).obj K) ∧
          uX.hom = B.adjunction.unit.app
            ((integralScalarExtensionOfUniverses l E L ι (point D)).obj K) ∧
          β.hom = χH.inv ≫
            (actualSameIndex D l E L ι A B F σ CR CS α γ b).app K ≫
            (completion D l L B).map χK.hom ∧
          β.hom ≫ uX.inv =
            (integralScalarExtensionOfUniverses l E L ι (point D)).map uK.inv := by
  classical
  let : Fintype D.k₀ := Fintype.ofFinite D.k₀
  let : Fact D.p.Prime := ⟨D.prime⟩
  let : CharP D.k₀ D.p := charP_of_card_eq_prime_pow
    ((Nat.card_eq_fintype_card.symm.trans D.card_base).trans D.cardinality_eq)
  have hu : IsUnit (l : D.k₀) := (CharP.isUnit_natCast_iff D.prime).2 (by
    intro hd
    exact _hl ((Nat.prime_dvd_prime_iff_eq D.prime (Fact.out : l.Prime)).1 hd).symm)
  have hk : IsUnit (l : D.k) := by
    simpa only [map_natCast] using hu.map (algebraMap D.k₀ D.k)
  have hres (x : point D) : IsUnit (l : (point D).residueField x) := by
    simpa only [map_natCast] using
      hk.map (((Scheme.ΓSpecIso (.of D.k)).inv ≫ (point D).Γevaluation x).hom)
  let : ∀ x : point D, Invertible (l : (point D).residueField x) := fun x ↦
    (hres x).invertible
  obtain ⟨F, hE, σ, hσ⟩ := normalizedScalarModel D l E L ι
  obtain ⟨free⟩ := (finiteFreeCompletedScalarComparison l E L ι (point D)).1
  have hfree : ∃ d : ℕ, Nonempty
      ((SheafOfModules.restrictScalars
        ((sheafCompose (Scheme.ProEt.topology (point D))
          (forget₂ CommRingCat RingCat)).map (completedCoefficientMap l E L ι (point D)))).obj
        (SheafOfModules.unit (completedIntegralCoefficientSheafUnrestricted l L (point D))) ≅
        ∐ (fun _ : Fin d ↦
          SheafOfModules.unit (completedIntegralCoefficientSheafUnrestricted l E (point D)))) := by
    let f : Fin (completedScalarRelativeDegree l E L ι) → integralTowerModules l E (point D) :=
      fun _ ↦ SheafOfModules.unit (completedIntegralCoefficientSheafUnrestricted l E (point D))
    let : HasBiproduct f :=
      (Abelian.hasFiniteBiproducts (C := integralTowerModules l E (point D))).out _
        |>.has_biproduct f
    exact ⟨completedScalarRelativeDegree l E L ι, ⟨free ≪≫ biproductIso f⟩⟩
  obtain ⟨uS, e, he, huS, hr⟩ := scalar_ramification l E L ι (point D)
  let : HasExactLimitsOfShape (Discrete ℕ) (integralTowerModules l E (point D)) :=
    Scheme.ProEt.products_exact.{t, u, 0} (point D)
      (completedIntegralCoefficientSheafUnrestricted l E (point D)) ℕ
  let : HasExactLimitsOfShape (Discrete ℕ) (integralTowerModules l L (point D)) :=
    Scheme.ProEt.products_exact.{t, u, 0} (point D)
      (completedIntegralCoefficientSheafUnrestricted l L (point D)) ℕ
  obtain ⟨CR⟩ := nonempty_model (completedIntegralCommRingSheafUnrestricted l E (point D))
    (PrincipalKoszulStrictReplacement.uniformizer l E (point D))
  obtain ⟨CS⟩ := nonempty_model (completedIntegralCommRingSheafUnrestricted l L (point D))
    (PrincipalKoszulStrictReplacement.uniformizer l L (point D))
  obtain ⟨Q⟩ := finiteFreeQuotientRoosComparison F hfree
    (PrincipalKoszulStrictReplacement.uniformizer l E (point D))
    (PrincipalKoszulStrictReplacement.uniformizer l L (point D)) uS huS e he hr
  obtain ⟨ε, hε, hrep⟩ := exchangeFromCochains F
    (PrincipalKoszulStrictReplacement.uniformizer l E (point D))
    (PrincipalKoszulStrictReplacement.uniformizer l L (point D)) e Q CR CS
  obtain ⟨A, ME, NE, α, hα⟩ := quotientAdjunctionRealization l E (point D) CR
  obtain ⟨B, ML, NL, γ, hγ⟩ := quotientAdjunctionRealization l L (point D) CS
  have hmul := scalarMultiplicationRealization l E L ι (point D) F hE σ hσ CS
  cases hmul with
  | intro c hcχ =>
    rcases hcχ with ⟨hc, hχ⟩
    have hdesc := sameIndexUnitDescent l E L ι (point D) F hE CR CS
    cases hdesc with
    | intro b hbbu =>
      rcases hbbu with ⟨hb, hbu⟩
      refine ⟨(fun n ↦ ⟨(PrincipalKoszulStrictReplacement.completed_exact l E (point D) n).2,
          (PrincipalKoszulStrictReplacement.completed_exact l L (point D) n).2⟩),
        quotientTransitions D l E, quotientTransitions D l L,
        A, B, ME, ML, NE, NL, CR, CS, α, γ, F, hE, σ, c, b, ε, e,
        hα, hγ, hσ, hc, hχ, hb, hbu, he, ?_, hε, ?_⟩
      · intro P
        exact hrep P.obj P.property.1
      · intro K hK
        have hHK : IntegralOnSlice.IsComplete l E (point D) none
            ((completion D l E A).obj K) :=
          ((purNormalizedReconstructionOfScheme l E (point D) A).1 _
            (A.reduction_normalized K)).1
        have huK := (purNormalizedReconstructionOfScheme l E (point D) A).2 K hK
        let uK := @asIso _ _ _ _ (A.adjunction.unit.app K) huK
        have hcomp := (finiteFreeCompletedScalarComparison l E L ι (point D)).2.1 K hK
        have hcompH := (finiteFreeCompletedScalarComparison l E L ι (point D)).2.1 _ hHK
        let χK := @asIso _ _ _ _ ((completedScalarComparison l E L ι (point D)).app K) hcomp.1
        let χH := @asIso _ _ _ _
          ((completedScalarComparison l E L ι (point D)).app ((completion D l E A).obj K)) hcompH.1
        have hT := (purNormalizedReconstructionOfScheme l L (point D) B).2 _ hcomp.2
        have huX : IsIso (B.adjunction.unit.app
            ((integralScalarExtensionOfUniverses l E L ι (point D)).obj K)) := by
          have hn := B.adjunction.unit.naturality χK.hom
          change χK.hom ≫ _ = _ at hn
          have hi : IsIso (χK.hom ≫ B.adjunction.unit.app
              ((integralScalarExtensionOfUniverses l E L ι (point D)).obj K)) := by
            rw [hn]
            let := hT
            infer_instance
          exact IsIso.of_isIso_comp_left χK.hom _
        let uX := @asIso _ _ _ _ (B.adjunction.unit.app
          ((integralScalarExtensionOfUniverses l E L ι (point D)).obj K)) huX
        have hX : IntegralOnSlice.IsComplete l L (point D) none
            ((integralScalarExtensionOfUniverses l E L ι (point D)).obj K) := by
          apply (completedIntegralPrincipalUnitCriterion l L (point D) CS _).2
          have hi : IsIso (CS.unit.app
              ((integralScalarExtensionOfUniverses l E L ι (point D)).obj K) ≫
            γ.hom.app ((integralScalarExtensionOfUniverses l E L ι (point D)).obj K)) := by
            rw [hγ.1]
            exact huX
          exact IsIso.of_isIso_comp_right _
            (γ.hom.app ((integralScalarExtensionOfUniverses l E L ι (point D)).obj K))
        have hCR := (completedIntegralPrincipalUnitCriterion l E (point D) CR K).1 hK
        have hbe : b.app K = ε.hom.app K := by
          let := hCR
          apply (cancel_epi (F.T.map (CR.unit.app K))).1
          exact (hbu K).trans (hε K).symm
        let β := ((integralScalarExtensionOfUniverses l E L ι (point D)).mapIso uK).symm ≪≫ uX
        have hβ := conjugated_unit (completion D l E A) (completion D l L B)
          (completedDerivedScalarExtension l E L ι (point D))
          (integralScalarExtensionOfUniverses l E L ι (point D))
          A.adjunction.unit B.adjunction.unit (completedScalarComparison l E L ι (point D))
          (actualSameIndex D l E L ι A B F σ CR CS α γ b) K uK rfl χK rfl χH rfl uX rfl
          (sameIndex_actual_unit D l E L ι A B F σ CR CS α γ b hα.1 hγ.1 hbu K)
        exact ⟨hbe, hHK, hcomp.2, hX, uK, χK, χH, uX, β, rfl, rfl, rfl, rfl, hβ⟩

end WeilConjectures.PodCompletionScalar
