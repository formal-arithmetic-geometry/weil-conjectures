/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarExtension
public import WeilConjectures.SmoothPurity.Derived.DerivedCompleteIntegralDetailed
import WeilConjectures.SmoothPurity.Coefficient.CoefficientExtensionFiniteAssociation
import WeilConjectures.SmoothPurity.Coefficient.CoefficientExtensionStrictRepresentatives
import WeilConjectures.SmoothPurity.Coefficient.CoefficientExtensionRepresentativeRoos
import WeilConjectures.SmoothPurity.Coefficient.CoefficientSequenceRoosModel
import WeilConjectures.SmoothPurity.Normalized.NormalizedDVREffectivity
public import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
public import WeilConjectures.AlgebraicGeometry.Picard.KFlatResolutionIndependentCoefficients
public import WeilConjectures.SixFunctors.Coefficient.CoefficientRingedSequenceSiteSupplement
public import WeilConjectures.SmoothPurity.Coefficient.CoefficientExtensionOrdinaryStrictTensor
public import WeilConjectures.SmoothPurity.Coefficient.CoefficientExtensionReductionData
public import WeilConjectures.SmoothPurity.Coefficient.CoefficientExtensionStrictDerivedComparison
public import WeilConjectures.SmoothPurity.Coefficient.CoefficientExtensionStrictTensorNormalized
public import WeilConjectures.SmoothPurity.Supporting.CoefDerivedSystemEvaluationCalculus

/-! # Effectivity of the scalar quotient tower

Source: Bhatt--Scholze, Proposition 3.5.1; integral scalar constructibility proof.
(blueprint: lem-sf-integral-scalar-tower-effectivity).
-/

@[expose] public section
set_option autoImplicit false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  WeilConjectures.SemilinearSections.hasDerived WeilConjectures.SemilinearSections.moduleAbelian

universe d u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (D : FiniteFieldDatum.{d}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
  (ι : E →ₐ[Padic l] L) (Y : AlgebraicGeometry.Scheme.{u})

private theorem integralScalarLegacy_sequenceNormalized_of_iso
    {X Y : coefficientSequenceDerived ell₀ E₀ W₀} (e : X ≅ Y)
    (hX : IsNormalizedCoefficientSequence ell₀ E₀ W₀ X) :
    IsNormalizedCoefficientSequence ell₀ E₀ W₀ Y := by
  intro m n h P
  let en := (coefficientSequenceDerivedEvaluation ell₀ E₀ W₀ n).mapIso e
  let em := (coefficientSequenceDerivedEvaluation ell₀ E₀ W₀ m).mapIso e
  let G := normalizedDVRRes ell₀ E₀ W₀ h
  have hn := (coefficientSequenceDerivedTransition ell₀ E₀ W₀ h).naturality e.hom
  change em.hom ≫ (coefficientSequenceDerivedTransition ell₀ E₀ W₀ h).app Y =
    (coefficientSequenceDerivedTransition ell₀ E₀ W₀ h).app X ≫ G.map en.hom at hn
  constructor
  · intro x y hxy
    apply (cancel_epi en.hom).1
    apply (hX h P).injective
    change (coefficientSequenceDerivedTransition ell₀ E₀ W₀ h).app X ≫ G.map (en.hom ≫ x) =
      (coefficientSequenceDerivedTransition ell₀ E₀ W₀ h).app X ≫ G.map (en.hom ≫ y)
    change (coefficientSequenceDerivedTransition ell₀ E₀ W₀ h).app Y ≫ G.map x =
      (coefficientSequenceDerivedTransition ell₀ E₀ W₀ h).app Y ≫ G.map y at hxy
    simp only [G.map_comp, ← Category.assoc, ← hn]
    simpa only [Category.assoc] using congrArg (fun k ↦ em.hom ≫ k) hxy
  · intro t
    obtain ⟨s, hs⟩ := (hX h P).surjective (em.hom ≫ t)
    refine ⟨en.inv ≫ s, ?_⟩
    apply (cancel_epi em.hom).1
    change em.hom ≫ (coefficientSequenceDerivedTransition ell₀ E₀ W₀ h).app Y ≫
      G.map (en.inv ≫ s) = em.hom ≫ t
    rw [G.map_comp, ← Category.assoc, hn]
    simp only [Category.assoc, ← G.map_comp, Iso.hom_inv_id_assoc]
    exact hs

private theorem integralScalarLegacy_goodRepresentative
    (K : DerivedCategory (scalarReductionSource ell₀ E₀ W₀)) :
    ∃ P : (integralOperationsGoodComplex ell₀ E₀ W₀).FullSubcategory,
      Nonempty (DerivedCategory.Q.obj P.obj ≅ K) := by
  classical
  obtain ⟨P, q, hP, hf, hq, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients
      (R := completedIntegralCommRingSheafUnrestricted ell₀ E₀ W₀)
      (DerivedCategory.Q.objPreimage K)
  have hgood : (integralOperationsGoodComplex ell₀ E₀ W₀) P := by
    refine ⟨hP, fun i ↦ ?_⟩
    exact (exactFunctor _ _).prop_of_iso
      (SheafOfModules.siteSheafTensorRightIso
        (completedIntegralCommRingSheafUnrestricted ell₀ E₀ W₀) (P.X i)).symm (hf i)
  have : IsIso (DerivedCategory.Q.map q) :=
    Localization.inverts DerivedCategory.Q (HomologicalComplex.quasiIso _ _) q hq
  exact ⟨⟨P, hgood⟩, ⟨asIso (DerivedCategory.Q.map q) ≪≫
    DerivedCategory.Q.objObjPreimageIso K⟩⟩

/-- Simultaneous strict finite quotient representatives of derived coefficient extension.
Source: integral operations, Stacks 06YY, 07A6 and 0941
(blueprint: stage3-pur-extension-strict-representatives).
Proof: use the ringed sequence projection to form the ordinary strict system whose
nth term is tensor with the nth target quotient. Its tensor generators determine
its quotient transitions. Apply it degreewise to flat-term K-flat complexes.
The given balanced associations identify the evaluated complexes with the iterated
finite scalar models. Transpose the ordinary units, using the reduction unit and
scalar evaluation formulas, to obtain a natural comparison from the specified
derived extension. At each level this is the composite of the two universal
K-flat comparisons and the given association. Both scalar extensions preserve
K-flatness, so these comparisons are invertible. The jointly conservative
evaluations make the system comparison invertible. For m at least n, scalar
extension of the mth term to the nth quotient is identified with the nth term by
balanced tensor association. Its adjoint is precisely the specified quotient
transition. Thus the universal Hom criterion gives normalization, first on good
representatives and then on every derived object by a K-flat resolution. -/
theorem integralScalarLegacy_strictRepresentative_exists
    (SE : CoefficientDerivedSystemCalculus ell₀ E₀ W₀)
    (association : ∀ n : ℕ,
      scalarReductionExtension ell₀ E₀ W₀ n ⋙ (A₀.levels n).model.E ≅
        integralScalarReduction ell₀ E₀ F₀ i₀ W₀ n)
    (hassociation : IsCoefficientExtensionAssociation ell₀ E₀ F₀ i₀ W₀ A₀ association) :
    ∃ (direct : (integralOperationsGoodComplex ell₀ E₀ W₀).FullSubcategory ⥤
        CochainComplex (coefficientSequenceModules ell₀ F₀ W₀) ℤ)
      (directEvaluation : ∀ n : ℕ,
        direct ⋙ (coefficientSequenceEvaluation ell₀ F₀ W₀ n).mapHomologicalComplex (.up ℤ) ≅
          (integralOperationsGoodComplex ell₀ E₀ W₀).ι ⋙ integralScalarFiniteComplex ell₀ E₀ F₀ i₀
            W₀ n)
      (model : integralOperationsGoodLocalization ell₀ E₀ W₀ ⋙
        coefficientExtensionSystem ell₀ E₀ F₀ i₀ W₀ SE A₀ ≅ direct ⋙ DerivedCategory.Q),
      IsCoefficientExtensionStrictTransition ell₀ E₀ F₀ i₀ W₀ direct directEvaluation ∧
      IsCoefficientExtensionModelEvaluation ell₀ E₀ F₀ i₀ W₀ SE A₀ association direct
        directEvaluation model ∧
      ∀ K : DerivedCategory (scalarReductionSource ell₀ E₀ W₀),
        IsNormalizedCoefficientSequence ell₀ F₀ W₀
          ((coefficientExtensionSystem ell₀ E₀ F₀ i₀ W₀ SE A₀).obj K) := by
  classical
  obtain ⟨direct, directEvaluation, htransition⟩ :=
    coefficientExtensionOrdinaryStrictTensor_exists ell₀ E₀ F₀ i₀ W₀
  obtain ⟨model, hmodel⟩ := coefficientExtensionStrictDerivedComparison
    ell₀ E₀ F₀ i₀ W₀ A₀ SE association hassociation direct directEvaluation htransition
  refine ⟨direct, directEvaluation, model, htransition, hmodel, ?_⟩
  intro K
  obtain ⟨P, ⟨e⟩⟩ := integralScalarLegacy_goodRepresentative ell₀ E₀ W₀ K
  have hP : IsNormalizedCoefficientSequence ell₀ F₀ W₀
      (DerivedCategory.Q.obj (direct.obj P)) :=
    coefficientExtensionStrictTensor_normalized
      ell₀ E₀ F₀ i₀ W₀ direct directEvaluation htransition P
  have hC : IsNormalizedCoefficientSequence ell₀ F₀ W₀
      ((coefficientExtensionSystem ell₀ E₀ F₀ i₀ W₀ SE A₀).obj
        ((integralOperationsGoodLocalization ell₀ E₀ W₀).obj P)) :=
    integralScalarLegacy_sequenceNormalized_of_iso ell₀ F₀ W₀ (model.app P).symm hP
  intro m n h Z
  exact integralScalarLegacy_sequenceNormalized_of_iso ell₀ F₀ W₀
    ((coefficientExtensionSystem ell₀ E₀ F₀ i₀ W₀ SE A₀).mapIso e) hC h Z

private theorem integralTower_normalized_of_iso
    {X Y : coefficientSequenceDerived l E W} (e : X ≅ Y)
    (hX : IsNormalizedCoefficientSequence l E W X) :
    IsNormalizedCoefficientSequence l E W Y := by
  intro m n h P
  let en := (coefficientSequenceDerivedEvaluation l E W n).mapIso e
  let em := (coefficientSequenceDerivedEvaluation l E W m).mapIso e
  let G := normalizedDVRRes l E W h
  have hn := (coefficientSequenceDerivedTransition l E W h).naturality e.hom
  change em.hom ≫ (coefficientSequenceDerivedTransition l E W h).app Y =
    (coefficientSequenceDerivedTransition l E W h).app X ≫ G.map en.hom at hn
  constructor
  · intro x y hxy
    apply (cancel_epi en.hom).1
    apply (hX h P).injective
    change (coefficientSequenceDerivedTransition l E W h).app X ≫ G.map (en.hom ≫ x) =
      (coefficientSequenceDerivedTransition l E W h).app X ≫ G.map (en.hom ≫ y)
    change (coefficientSequenceDerivedTransition l E W h).app Y ≫ G.map x =
      (coefficientSequenceDerivedTransition l E W h).app Y ≫ G.map y at hxy
    simp only [G.map_comp, ← Category.assoc, ← hn]
    simpa only [Category.assoc] using congrArg (fun k ↦ em.hom ≫ k) hxy
  · intro t
    obtain ⟨s, hs⟩ := (hX h P).surjective (em.hom ≫ t)
    refine ⟨en.inv ≫ s, ?_⟩
    apply (cancel_epi em.hom).1
    change em.hom ≫ (coefficientSequenceDerivedTransition l E W h).app Y ≫
      G.map (en.inv ≫ s) = em.hom ≫ t
    rw [G.map_comp, ← Category.assoc, hn]
    simp only [Category.assoc, ← G.map_comp, Iso.hom_inv_id_assoc]
    exact hs

private theorem integralTower_goodRepresentative
    (K : DerivedCategory (scalarReductionSource l E W)) :
    ∃ P : (integralOperationsGoodComplex l E W).FullSubcategory,
      Nonempty (DerivedCategory.Q.obj P.obj ≅ K) := by
  classical
  obtain ⟨P, q, hP, hf, hq, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients
      (R := completedIntegralCommRingSheafUnrestricted l E W)
      (DerivedCategory.Q.objPreimage K)
  have hgood : (integralOperationsGoodComplex l E W) P := by
    refine ⟨hP, fun i ↦ ?_⟩
    exact (exactFunctor _ _).prop_of_iso
      (SheafOfModules.siteSheafTensorRightIso
        (completedIntegralCommRingSheafUnrestricted l E W) (P.X i)).symm (hf i)
  have : IsIso (DerivedCategory.Q.map q) :=
    Localization.inverts DerivedCategory.Q (HomologicalComplex.quasiIso _ _) q hq
  exact ⟨⟨P, hgood⟩, ⟨asIso (DerivedCategory.Q.map q) ≪≫
    DerivedCategory.Q.objObjPreimageIso K⟩⟩

/-- Simultaneous strict finite quotient representatives of derived coefficient extension.
Source: integral operations, Stacks 06YY, 07A6 and 0941
Preserved legacy auxiliary from CoefficientExtensionStrictRepresentatives; it does not
realize the current native-module statement of that node.
Proof: use the ringed sequence projection to form the ordinary strict system whose
nth term is tensor with the nth target quotient. Its tensor generators determine
its quotient transitions. Apply it degreewise to flat-term K-flat complexes.
The given balanced associations identify the evaluated complexes with the iterated
finite scalar models. Transpose the ordinary units, using the reduction unit and
scalar evaluation formulas, to obtain a natural comparison from the specified
derived extension. At each level this is the composite of the two universal
K-flat comparisons and the given association. Both scalar extensions preserve
K-flatness, so these comparisons are invertible. The jointly conservative
evaluations make the system comparison invertible. For m at least n, scalar
extension of the mth term to the nth quotient is identified with the nth term by
balanced tensor association. Its adjoint is precisely the specified quotient
transition. Thus the universal Hom criterion gives normalization, first on good
representatives and then on every derived object by a K-flat resolution. -/
private theorem integralTower_strictRepresentative_legacy
    (A : CoefficientExtensionSystems l E L ι W)
    (SE : CoefficientDerivedSystemCalculus l E W)
    (association : ∀ n : ℕ,
      scalarReductionExtension l E W n ⋙ (A.levels n).model.E ≅
        integralScalarReduction l E L ι W n)
    (hassociation : IsCoefficientExtensionAssociation l E L ι W A association) :
    ∃ (direct : (integralOperationsGoodComplex l E W).FullSubcategory ⥤
        CochainComplex (coefficientSequenceModules l L W) ℤ)
      (directEvaluation : ∀ n : ℕ,
        direct ⋙ (coefficientSequenceEvaluation l L W n).mapHomologicalComplex (.up ℤ) ≅
          (integralOperationsGoodComplex l E W).ι ⋙ integralScalarFiniteComplex l E L ι W n)
      (model : integralOperationsGoodLocalization l E W ⋙
        coefficientExtensionSystem l E L ι W SE A ≅ direct ⋙ DerivedCategory.Q),
      IsCoefficientExtensionStrictTransition l E L ι W direct directEvaluation ∧
      IsCoefficientExtensionModelEvaluation l E L ι W SE A association direct
        directEvaluation model ∧
      ∀ K : DerivedCategory (scalarReductionSource l E W),
        IsNormalizedCoefficientSequence l L W
          ((coefficientExtensionSystem l E L ι W SE A).obj K) := by
  classical
  obtain ⟨direct, directEvaluation, htransition⟩ :=
    coefficientExtensionOrdinaryStrictTensor_exists l E L ι W
  obtain ⟨model, hmodel⟩ := coefficientExtensionStrictDerivedComparison
    l E L ι W A SE association hassociation direct directEvaluation htransition
  refine ⟨direct, directEvaluation, model, htransition, hmodel, ?_⟩
  intro K
  obtain ⟨P, ⟨e⟩⟩ := integralTower_goodRepresentative l E W K
  have hP : IsNormalizedCoefficientSequence l L W
      (DerivedCategory.Q.obj (direct.obj P)) :=
    coefficientExtensionStrictTensor_normalized
      l E L ι W direct directEvaluation htransition P
  have hC : IsNormalizedCoefficientSequence l L W
      ((coefficientExtensionSystem l E L ι W SE A).obj
        ((integralOperationsGoodLocalization l E W).obj P)) :=
    integralTower_normalized_of_iso l L W (model.app P).symm hP
  intro m n h Z
  exact integralTower_normalized_of_iso l L W
    ((coefficientExtensionSystem l E L ι W SE A).mapIso e) hC h Z

/-- Effectivity of the specified strict scalar quotient tower on good representatives.
Source: Bhatt--Scholze, Lemmas 3.5.4--3.5.5; normalized DVR effectivity and the strict
Roos comparison, steps 2, 6--7 of lem-weil-integral-scalar-extension-constructible.
(blueprint: lem-sf-integral-scalar-tower-effectivity).
Proof: termwise scalar tensor of the good complex is K-flat over every finite target
quotient. For m >= n, the balanced tensor maps (x tensor b) tensor c to x tensor bc
and x tensor c to (x tensor 1) tensor c identify further derived reduction with the
specified lower level. These maps commute with the quotient transitions and satisfy
the cocycle because both iterated maps multiply the same three scalars. They give the
normalized DVR tower for O_L with its actual restricted scalar transitions. Exact
countable products compare its strict Roos complex with the derived inverse limit,
compatibly with all quotient evaluations. The representative comparison in the
definition of integralScalarExtension identifies its value on Q(P) with precisely this
Roos complex. Apply normalizedDVRTower_effectivity: its counit comparisons identify
all reductions with the finite tensor levels, and its last clause gives derived
completeness. No constructibility, boundedness, completeness of P, or flatness between
finite coefficient quotients is used. Identity extension and the zero complex are
included; normalization concerns actual quotient maps, not arbitrary triangle fillers. -/
theorem integralScalarTower_effectivity
    (P : (integralOperationsGoodComplex l E Y).FullSubcategory) :
    IsDerivedComplete l L Y D hl
      ((integralScalarExtension l E L ι Y).obj (DerivedCategory.Q.obj P.obj)) ∧
    ∀ n : ℕ, Nonempty
      (((integralDerivedReduction l L Y D hl n).obj
          ((integralScalarExtension l E L ι Y).obj (DerivedCategory.Q.obj P.obj))) ≅
        DerivedCategory.Q.obj ((integralScalarFiniteComplex l E L ι Y n).obj P.obj)) := by
  classical
  let : EssentiallySmall.{u + 1} Y.ProEt := essentiallySmallSelf.{0} _
  let : HasSheafify (AlgebraicGeometry.Scheme.ProEt.topology Y)
      AddCommGrpCat.{u + 1} := integralCoefficientAbSheafify.{u, u} Y
  let : (AlgebraicGeometry.Scheme.ProEt.topology Y).WEqualsLocallyBijective
      AddCommGrpCat.{u + 1} := integralCoefficientAbLocallyBijective.{u, u} Y
  obtain ⟨SE, _⟩ := coefficientDerivedSystemEvaluationCalculus l E Y
  let : EssentiallySmall.{u + 1} (ℕ × Y.ProEt) := essentiallySmallSelf.{0} _
  let S : SemilinearSections.SemilinearDerivedSectionsData.{u + 1, u, u}
      (AlgebraicGeometry.Scheme.ProEt.topology Y)
      (integralCoefficientCommRingSheaf l E Y)
      (coefficientSequenceCommRingTransition l E Y) :=
    (SemilinearSections.semilinearDerivedSections.{u + 1, u, u}
      (AlgebraicGeometry.Scheme.ProEt.topology Y)
      (integralCoefficientCommRingSheaf l E Y)
      (coefficientSequenceCommRingTransition l E Y)).some
  let A : CoefficientExtensionSystems l E L ι Y :=
    S.coefficientExtension (integralCoefficientCommRingSheaf l L Y)
      (coefficientSequenceCommRingTransition l L Y)
      (integralScalarQuotientSheafMap l E L ι Y)
      (coefficientExtensionQuotient_naturality l E L ι Y)
  obtain ⟨s⟩ := coefficientExtensionFiniteAssociation_exists l E L ι Y A
  obtain ⟨direct, evaluation, model, ht, _, hn⟩ :=
    integralTower_strictRepresentative_legacy l E L ι Y A SE
      s.association s.association_section
  obtain ⟨e, _⟩ := coefficientExtensionRepresentativeRoos_exists l E L ι Y A SE
    direct evaluation ht model
  let N := (coefficientExtensionSystem l E L ι Y SE A).obj (DerivedCategory.Q.obj P.obj)
  let M := (integralScalarExtension l E L ι Y).obj (DerivedCategory.Q.obj P.obj)
  let a : M ≅ (coefficientSequenceLimit l L Y).obj N :=
    (integralScalarExtensionComparison l E L ι Y).app P ≪≫ (e.app P).symm
  obtain ⟨T, b, hp, δ, hδ⟩ := coefficientSequence_roosModel l L Y D hl N (hn _)
  let := hp
  let p₀ := Pi.lift (fun n : ℕ ↦ (coefficientSequenceProjection l L Y n).app N ≫
    (normalizedDVRResCompleted l L Y D hl n).map (b n).inv ≫
      (T.evaluationIso n).inv)
  let p := a.hom ≫ p₀
  let δ' := δ ≫ (shiftFunctor _ (1 : ℤ)).map a.inv
  have hc : IsDerivedLimitTriangle
      (fun n : ℕ ↦ (normalizedDVRTowerTransition l L Y D hl n.le_succ).app T.tower)
      M p δ' := by
    exact (Pretriangulated.distinguished_iff_of_iso
      (Pretriangulated.Triangle.isoMk
        (Pretriangulated.Triangle.mk p (towerTransitionEndomorphism
          (fun n : ℕ ↦ (normalizedDVRTowerTransition l L Y D hl n.le_succ).app T.tower)) δ')
        (Pretriangulated.Triangle.mk p₀ (towerTransitionEndomorphism
          (fun n : ℕ ↦ (normalizedDVRTowerTransition l L Y D hl n.le_succ).app T.tower)) δ)
        a (Iso.refl _) (Iso.refl _) (by simp [p]) (by simp)
        (by simp [δ']))).mpr hδ
  obtain ⟨hi, _, hcomplete⟩ := normalizedDVRTower_effectivity l L Y D hl T M p δ' hc
  refine ⟨hcomplete, fun n ↦ ?_⟩
  have := hi n
  exact ⟨asIso (normalizedDVRCounitComparison l L Y D hl T M p n) ≪≫ b n ≪≫
    (coefficientSequenceDerivedEvaluation.{u, u} l L Y n).mapIso (model.app P) ≪≫
    (coefficientSequenceEvaluation.{u, u} l L Y n).mapDerivedCategoryFactors.app (direct.obj P) ≪≫
    DerivedCategory.Q.mapIso ((evaluation n).app P)⟩

end WeilConjectures
