/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.Pod.Reindexing.Derived.PodReindexingDerivedCanonical
import all WeilConjectures.PoincareDuality.Pod.Reindexing.Derived.PodReindexingDerivedCanonical
import WeilConjectures.PoincareDuality.Pod.Reindexing.Derived.PodReindexingDerivedLimitProjection
import all WeilConjectures.SmoothPurity.Supporting.IsomorphismReductionTower
import all WeilConjectures.TraceFormula.CompletionUnit.CompletionUnitFiniteMateComparison
import all WeilConjectures.SmoothPurity.Integral.IntegralOperationsWellDefinedSupplement

/-! # Reduction evaluation law for raw derived comparison data

We show that the completion reindexing datum assembled from raw derived comparison data
satisfies the reduction-evaluation law, provided its restriction and evaluation comparisons are
the canonical ones and its finite, limit and reduction comparisons satisfy the finite-model,
limit-model and unit laws.

## Implementation details

First, the finite scalar comparison is the mate of the canonical restriction comparison with
respect to the finite scalar adjunctions; this is checked on good representatives, where both
adjunction units are localized ordinary units. The law then follows formally from the
limit-projection law, the unit law, and the compatibility of the reduction units of the two
coefficient calculi with the limit projections, by comparing adjoint transposes. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology
attribute [-instance] WeilConjectures.SemilinearSections.moduleAbelian
attribute [-instance] WeilConjectures.SemilinearSections.hasDerived
attribute [-instance] WeilConjectures.integralOperationsCommHasDerivedCategory
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective
attribute [local instance 5000] WeilConjectures.integralTowerHasDerivedCategory
attribute [local instance 5000] WeilConjectures.coefficientSequenceHasDerived
attribute [local instance 5000] WeilConjectures.coefficientFiniteHasDerived
attribute [local irreducible] HasDerivedCategory.standard

universe t u a b
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {X Y : Scheme.{t}} (g : X ⟶ Y) [IsIso g]
  (SY : PodSignedRoosShift (scalarReductionSource l E Y))
  (SX : PodSignedRoosShift (scalarReductionSource l E X))

namespace PodReindexingReductionEvaluation

/-- Quotient comparisons normalized on generators are the strict tensor squares. -/
private theorem quotient_hom_eq
    (β : ∀ (P : CochainComplex (scalarReductionSource l E Y) ℤ),
      integralOperationsGoodComplex l E Y P → ∀ n : ℕ,
      (isoReductionFiniteComplex l E g n).obj (unrestrictedTowerFiniteComplex l E Y n P) ≅
        unrestrictedTowerFiniteComplex l E X n
          ((isoReductionIntegralComplex l E g).obj P))
    (hβ : podReindexingCoreQuotientGenerators l E g β)
    (P : CochainComplex (scalarReductionSource l E Y) ℤ)
    (hP : integralOperationsGoodComplex l E Y P) (n : ℕ) :
    (β P hP n).hom = ((isoReduction_complexSquare l E g n
      (isoReduction_tensorSquare l E g n).choose).app P).hom := by
  let e := fun n ↦ (isoReduction_tensorSquare l E g n).choose
  apply HomologicalComplex.Hom.ext
  funext i
  rw [Iso.app_hom, isoReduction_complexSquare_component]
  let a := (e n).app (P.X i)
  apply (cancel_epi a.inv).1
  change a.inv ≫ (β P hP n).hom.f i = a.inv ≫ a.hom
  rw [a.inv_hom_id]
  let R := scalarReductionRestriction l E X n
  have : R.Faithful := scalarReductionRestriction_faithful l E X n
  apply R.map_injective
  apply SheafOfModules.UnrestrictedTowerProof.identified_hom_ext
    (completedIntegralCommRingProjectionUnrestricted l E X n)
    ((isoReductionIntegralInverse l E g).obj (P.X i))
    (scalarReductionExtension l E X n) (isoReduction_extension_obj l E X n) _
  intro V b x
  have hs := isoReduction_tensorSection_eq l E X n
    ((isoReductionIntegralInverse l E g).obj (P.X i)) V b x
  apply (congrArg ((R.map (a.inv ≫ (β P hP n).hom.f i)).val.app V) hs).trans
  apply Eq.trans _ (congrArg ((R.map (𝟙 _)).val.app V) hs).symm
  let d := isoSectionwiseConstantMap g (CommRingCat.of
    (ULift.{t + 1} (Padic.coefficientExtensionRing l E (n + 1))))
  let b' := (inv d).hom.app V b
  have hb' : d.hom.app V b' = b :=
    congrArg (fun f ↦ f.hom.app V b) (IsIso.inv_hom_id d)
  have ht := isoReduction_tensorFormula l E g n (e n)
    (isoReduction_tensorUnit l E g n (e n) (isoReduction_tensorSquare l E g n).choose_spec)
    (P.X i) V b' x
  have hbt := hβ P hP n i V.unop b' x
  rw [hb'] at ht hbt
  change (a.hom.val.app V) _ = _ at ht
  change ((β P hP n).hom.f i).val.app V _ = _ at hbt
  change ((β P hP n).hom.f i).val.app V (a.inv.val.app V _) = _
  rw [← ht]
  have ha : a.inv.val.app V (a.hom.val.app V
      (unrestrictedTowerTensorSection l E Y n (P.X i)
        ((proEtaleIsoPostcompose g).op.obj V) b' x)) =
    unrestrictedTowerTensorSection l E Y n (P.X i)
      ((proEtaleIsoPostcompose g).op.obj V) b' x := by
    exact ConcreteCategory.congr_hom
      (congrArg (fun f ↦ f.val.app V) a.hom_inv_id) _
  rw [ha]
  exact hbt.trans ht.symm

/-- Natural transformations out of the derived category agree if they agree on good
representatives. -/
private theorem natTrans_ext_good {D : Type*} [Category* D]
    {F₁ F₂ : DerivedCategory (scalarReductionSource l E Y) ⥤ D} {τ τ' : F₁ ⟶ F₂}
    (h : ∀ P : CochainComplex (scalarReductionSource l E Y) ℤ,
      integralOperationsGoodComplex l E Y P →
        τ.app (DerivedCategory.Q.obj P) = τ'.app (DerivedCategory.Q.obj P)) : τ = τ' := by
  have := integralOperationsGoodLocalization_isLocalization l E Y
  exact Localization.natTrans_ext (integralOperationsGoodLocalization l E Y)
    ((HomologicalComplex.quasiIso (integralTowerModules l E Y) (.up ℤ)).inverseImage
      (integralOperationsGoodComplex l E Y).ι) (fun P ↦ h P.obj P.property)

/-- Transport of an adjunction unit along a morphism. -/
private theorem unit_naturality_comp {C D : Type*} [Category* C] [Category* D] {F : C ⥤ D}
    {G : D ⥤ C} (adj : F ⊣ G) {A B Z : C} (f : A ⟶ B) (R : G.obj (F.obj B) ⟶ Z) (u : B ⟶ Z)
    (hu : adj.unit.app B ≫ R = u) : adj.unit.app A ≫ G.map (F.map f) ≫ R = f ≫ u := by
  rw [← hu]
  exact adj.unit_naturality_assoc f R

/-- The finite scalar unit at a reindexed good representative, in localization coordinates. -/
private theorem unit_reindex
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (P : CochainComplex (scalarReductionSource l E Y) ℤ)
    (hFP : integralOperationsGoodComplex l E X ((isoReductionIntegralComplex l E g).obj P))
    (n : ℕ) :
    (coefficientFiniteAdjunction l E X n).unit.app
        ((podOrdinaryReindex l E g).obj (DerivedCategory.Q.obj P)) ≫
      (coefficientFiniteDerivedRestriction l E X n).map
          ((coefficientFiniteDerivedExtension l E X n).map
            ((isoReductionIntegralInverse l E g).mapDerivedCategoryFactors.hom.app P)) ≫
        (coefficientFiniteDerivedRestriction l E X n).map
            (coefficientFiniteReductionModel l E X _ hFP.1 n).hom ≫
          (scalarReductionRestriction l E X n).mapDerivedCategoryFactors.hom.app
            (((scalarReductionExtension l E X n).mapHomologicalComplex (.up ℤ)).obj
              (((isoReductionIntegralInverse l E g).mapHomologicalComplex (.up ℤ)).obj P)) =
      (isoReductionIntegralInverse l E g).mapDerivedCategoryFactors.hom.app P ≫
        DerivedCategory.Q.map
          (((scalarReductionExtension_adjunction l E X n).choose.mapHomologicalComplex
            (.up ℤ)).unit.app (((isoReductionIntegralInverse l E g).mapHomologicalComplex
              (.up ℤ)).obj P)) := by
  have hu := CompletionUnit.finiteModel_unit l E X _ hFP.1 n
  exact unit_naturality_comp (coefficientFiniteAdjunction l E X n)
    ((isoReductionIntegralInverse l E g).mapDerivedCategoryFactors.hom.app P) _ _ hu

/-- The strict tensor square is the mate of the strict restriction comparison. -/
private theorem tensorSquare_spec (n : ℕ) (M : scalarReductionSource l E Y) :
    (isoReductionIntegralInverse l E g).map
          ((scalarReductionExtension_adjunction l E Y n).choose.unit.app M) ≫
        (podReindexingStrictRestriction l E g n).hom.app
          ((scalarReductionExtension l E Y n).obj M) ≫
        (scalarReductionRestriction l E X n).map
          ((isoReduction_tensorSquare l E g n).choose.hom.app M) =
      (scalarReductionExtension_adjunction l E X n).choose.unit.app
        ((isoReductionIntegralInverse l E g).obj M) := by
  have h := (isoReduction_tensorSquare l E g n).choose_spec M
  with_unfolding_all exact h

/-- The strict unit identity behind the finite mate law. -/
private theorem strict_unit (P : CochainComplex (scalarReductionSource l E Y) ℤ) (n : ℕ)
    (b : (isoReductionFiniteComplex l E g n).obj (unrestrictedTowerFiniteComplex l E Y n P) ⟶
      unrestrictedTowerFiniteComplex l E X n ((isoReductionIntegralComplex l E g).obj P))
    (e : scalarReductionExtension l E Y n ⋙ isoReductionFiniteInverse l E g n ≅
      isoReductionIntegralInverse l E g ⋙ scalarReductionExtension l E X n)
    (he : ∀ M, (isoReductionIntegralInverse l E g).map
          ((scalarReductionExtension_adjunction l E Y n).choose.unit.app M) ≫
        (podReindexingStrictRestriction l E g n).hom.app
          ((scalarReductionExtension l E Y n).obj M) ≫
        (scalarReductionRestriction l E X n).map (e.hom.app M) =
      (scalarReductionExtension_adjunction l E X n).choose.unit.app
        ((isoReductionIntegralInverse l E g).obj M))
    (hb : ∀ i, b.f i = e.hom.app (P.X i)) :
    (isoReductionIntegralComplex l E g).map
        (((scalarReductionExtension_adjunction l E Y n).choose.mapHomologicalComplex
          (.up ℤ)).unit.app P) ≫
      (NatTrans.mapHomologicalComplex (podReindexingStrictRestriction l E g n).hom (.up ℤ)).app
        (((scalarReductionExtension l E Y n).mapHomologicalComplex (.up ℤ)).obj P) ≫
      ((scalarReductionRestriction l E X n).mapHomologicalComplex (.up ℤ)).map b =
    ((scalarReductionExtension_adjunction l E X n).choose.mapHomologicalComplex
      (.up ℤ)).unit.app ((isoReductionIntegralComplex l E g).obj P) := by
  apply HomologicalComplex.hom_ext
  intro i
  simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
    NatTrans.mapHomologicalComplex_app_f, Adjunction.mapHomologicalComplex_unit_app_f]
  exact (congrArg (fun x ↦ _ ≫ _ ≫ (scalarReductionRestriction l E X n).map x) (hb i)).trans
    (he (P.X i))

/-- Quotient comparisons normalized on generators have the strict tensor squares as
components. -/
private theorem quotient_hom_f
    (β : ∀ (P : CochainComplex (scalarReductionSource l E Y) ℤ),
      integralOperationsGoodComplex l E Y P → ∀ n : ℕ,
      (isoReductionFiniteComplex l E g n).obj (unrestrictedTowerFiniteComplex l E Y n P) ≅
        unrestrictedTowerFiniteComplex l E X n
          ((isoReductionIntegralComplex l E g).obj P))
    (hβ : podReindexingCoreQuotientGenerators l E g β)
    (P : CochainComplex (scalarReductionSource l E Y) ℤ)
    (hP : integralOperationsGoodComplex l E Y P) (n : ℕ) (i : ℤ) :
    (β P hP n).hom.f i = (isoReduction_tensorSquare l E g n).choose.hom.app (P.X i) := by
  rw [quotient_hom_eq l E g β hβ P hP n, Iso.app_hom, isoReduction_complexSquare_component]

/-- The formal shape of the finite mate computation. -/
private theorem mate_abstract {C : Type*} [Category* C]
    {a b b₁ b₂ c c₁ c₂ d d₁ d₂ d₃ p q q' : C}
    (Fη : a ⟶ b) (rE : b ⟶ c) (resφ : c ⟶ d) (ηX : a ⟶ d)
    (ω₁ : d ⟶ d₁) (ω₂ : d₁ ⟶ d₂) (ω₃ : d₂ ⟶ d₃) [Mono (ω₁ ≫ ω₂ ≫ ω₃)]
    (FfacP : a ⟶ p) (QunitX : p ⟶ d₃) (resHm : c ⟶ c₁) (resHfac : c₁ ⟶ c₂)
    (resQβ : c₂ ⟶ d₂) (Fresm : b ⟶ b₁) (rI : b₁ ⟶ c₁) (resXfacI : c₂ ⟶ q)
    (Qrestrβ : q ⟶ d₃) (FresYfac : b₁ ⟶ b₂) (FfacI : b₂ ⟶ q') (Qsr : q' ⟶ q)
    (FQunitY : a ⟶ b₂) (QFunitY : p ⟶ q')
    (h₁ : ηX ≫ ω₁ ≫ ω₂ ≫ ω₃ = FfacP ≫ QunitX)
    (h₂ : resHm ≫ resHfac ≫ resQβ = resφ ≫ ω₁ ≫ ω₂)
    (h₃ : Fresm ≫ rI = rE ≫ resHm)
    (h₄ : resQβ ≫ ω₃ = resXfacI ≫ Qrestrβ)
    (h₅ : rI ≫ resHfac ≫ resXfacI = FresYfac ≫ FfacI ≫ Qsr)
    (h₆ : Fη ≫ Fresm ≫ FresYfac = FQunitY)
    (h₇ : FQunitY ≫ FfacI = FfacP ≫ QFunitY)
    (h₈ : QFunitY ≫ Qsr ≫ Qrestrβ = QunitX) :
    Fη ≫ rE ≫ resφ = ηX := by
  rw [← cancel_mono (ω₁ ≫ ω₂ ≫ ω₃), h₁]
  simp only [Category.assoc]
  rw [← reassoc_of% h₂, ← reassoc_of% h₃, h₄, reassoc_of% h₅, reassoc_of% h₆, reassoc_of% h₇,
    h₈]

/-- The finite mate law on a good representative. -/
private theorem finite_mate_good
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (S : PodReindexingStrictData l E g)
    (β : ∀ (P : CochainComplex (scalarReductionSource l E Y) ℤ),
      integralOperationsGoodComplex l E Y P → ∀ n : ℕ,
      (isoReductionFiniteComplex l E g n).obj (unrestrictedTowerFiniteComplex l E Y n P) ≅
        unrestrictedTowerFiniteComplex l E X n
          ((isoReductionIntegralComplex l E g).obj P))
    (hβ : podReindexingCoreQuotientGenerators l E g β)
    (CY : IntegralOnSlice.completion l E Y none ≅
      (podReindexCalculus l E Y).reduction ⋙ coefficientSequenceLimit l E Y)
    (CX : IntegralOnSlice.completion l E X none ≅
      (podReindexCalculus l E X).reduction ⋙ coefficientSequenceLimit l E X)
    (Q : PodReindexingDerivedCoreData l E g)
    (hfinite : PodCompletionReindex.FiniteModel l E g (Q.assemble l E g SY SX S β CY CX))
    (n : ℕ) (P : CochainComplex (scalarReductionSource l E Y) ℤ)
    (hP : integralOperationsGoodComplex l E Y P) :
    (podOrdinaryReindex l E g).map
        ((coefficientFiniteAdjunction l E Y n).unit.app (DerivedCategory.Q.obj P)) ≫
      (podReindexingDerivedRestriction l E g n).hom.app
        ((coefficientFiniteDerivedExtension l E Y n).obj (DerivedCategory.Q.obj P)) ≫
      (coefficientFiniteDerivedRestriction l E X n).map
        ((Q.finite n).hom.app (DerivedCategory.Q.obj P)) =
    (coefficientFiniteAdjunction l E X n).unit.app
      ((podOrdinaryReindex l E g).obj (DerivedCategory.Q.obj P)) := by
  have hFP := S.good l E g P hP
  have := (scalarReductionRestriction_exact l E Y n).1
  have := (scalarReductionRestriction_exact l E Y n).2
  have := (scalarReductionRestriction_exact l E X n).1
  have := (scalarReductionRestriction_exact l E X n).2
  let I := ((scalarReductionExtension l E Y n).mapHomologicalComplex (.up ℤ)).obj P
  have hfin := hfinite P hP n
  dsimp only [PodReindexingDerivedCoreData.assemble] at hfin
  have hfin' := congrArg (coefficientFiniteDerivedRestriction l E X n).map hfin
  simp only [Functor.map_comp] at hfin'
  have uY := congrArg (podOrdinaryReindex l E g).map
    (CompletionUnit.finiteModel_unit l E Y P hP.1 n)
  simp only [Functor.map_comp] at uY
  have hr := PodReindexingDerivedCanonical.squareIso_factors (scalarReductionRestriction l E Y n)
    (isoReductionIntegralInverse l E g) (isoReductionFiniteInverse l E g n)
    (scalarReductionRestriction l E X n) (podReindexingStrictRestriction l E g n) I
  have hr' := (Iso.inv_comp_eq ((podOrdinaryReindex l E g).mapIso
    ((scalarReductionRestriction l E Y n).mapDerivedCategoryFactors.app I))).1 hr
  simp only [Functor.mapIso_hom, Iso.app_hom] at hr'
  have hs := congrArg DerivedCategory.Q.map
    (strict_unit l E g P n (β P hP n).hom _ (tensorSquare_spec l E g n)
      (quotient_hom_f l E g β hβ P hP n))
  simp only [Functor.map_comp] at hs
  exact mate_abstract _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (unit_reindex l E g P hFP n) hfin'
    ((podReindexingDerivedRestriction l E g n).hom.naturality
      (coefficientFiniteReductionModel l E Y P hP.1 n).hom)
    (Functor.mapDerivedCategoryFactors_hom_naturality (scalarReductionRestriction l E X n)
      (β P hP n).hom) hr' uY
    (Functor.mapDerivedCategoryFactors_hom_naturality (isoReductionIntegralInverse l E g)
      (((scalarReductionExtension_adjunction l E Y n).choose.mapHomologicalComplex
        (.up ℤ)).unit.app P)) hs


/-- The finite scalar comparison of a datum satisfying the finite-model law is the mate of the
canonical restriction comparison with respect to the finite scalar adjunctions. -/
private theorem finite_mate
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (S : PodReindexingStrictData l E g)
    (β : ∀ (P : CochainComplex (scalarReductionSource l E Y) ℤ),
      integralOperationsGoodComplex l E Y P → ∀ n : ℕ,
      (isoReductionFiniteComplex l E g n).obj (unrestrictedTowerFiniteComplex l E Y n P) ≅
        unrestrictedTowerFiniteComplex l E X n
          ((isoReductionIntegralComplex l E g).obj P))
    (hβ : podReindexingCoreQuotientGenerators l E g β)
    (CY : IntegralOnSlice.completion l E Y none ≅
      (podReindexCalculus l E Y).reduction ⋙ coefficientSequenceLimit l E Y)
    (CX : IntegralOnSlice.completion l E X none ≅
      (podReindexCalculus l E X).reduction ⋙ coefficientSequenceLimit l E X)
    (Q : PodReindexingDerivedCoreData l E g)
    (hfinite : PodCompletionReindex.FiniteModel l E g (Q.assemble l E g SY SX S β CY CX))
    (n : ℕ) (K : DerivedCategory (scalarReductionSource l E Y)) :
    (podOrdinaryReindex l E g).map ((coefficientFiniteAdjunction l E Y n).unit.app K) ≫
        (podReindexingDerivedRestriction l E g n).hom.app
          ((coefficientFiniteDerivedExtension l E Y n).obj K) ≫
        (coefficientFiniteDerivedRestriction l E X n).map ((Q.finite n).hom.app K) =
      (coefficientFiniteAdjunction l E X n).unit.app ((podOrdinaryReindex l E g).obj K) := by
  let τ₁ : podOrdinaryReindex l E g ⟶ podOrdinaryReindex l E g ⋙
      coefficientFiniteDerivedExtension l E X n ⋙ coefficientFiniteDerivedRestriction l E X n :=
    Functor.whiskerRight (coefficientFiniteAdjunction l E Y n).unit (podOrdinaryReindex l E g) ≫
      Functor.whiskerLeft (coefficientFiniteDerivedExtension l E Y n)
        (podReindexingDerivedRestriction l E g n).hom ≫
      Functor.whiskerRight (Q.finite n).hom (coefficientFiniteDerivedRestriction l E X n)
  let τ₂ : podOrdinaryReindex l E g ⟶ podOrdinaryReindex l E g ⋙
      coefficientFiniteDerivedExtension l E X n ⋙ coefficientFiniteDerivedRestriction l E X n :=
    Functor.whiskerLeft (podOrdinaryReindex l E g) (coefficientFiniteAdjunction l E X n).unit
  suffices h : τ₁ = τ₂ from congr_app h K
  exact natTrans_ext_good l E (fun P hP ↦
    finite_mate_good l E g SY SX S β hβ CY CX Q hfinite n P hP)

/-- The formal shape of the reduction-evaluation computation. -/
private theorem reductionEvaluation_abstract {C : Type*} [Category* C]
    {a b₁ b₂ b₃ c₁ c₂ c₃ c₄ z m₁ m₂ : C}
    (ηfX : a ⟶ z) (RρXinv : z ⟶ c₁) (RevXαinv : c₁ ⟶ c₂) (Rev : c₂ ⟶ c₃) (RHρ : c₃ ⟶ c₄)
    (Rφ : c₄ ⟶ z) (ηX : a ⟶ m₁) (πXred : m₁ ⟶ c₁) (limαinv : m₁ ⟶ m₂) (πXG : m₂ ⟶ c₂)
    (FηY : a ⟶ b₁) (LredY : b₁ ⟶ m₂) (limα : m₂ ⟶ m₁) (FπY : b₁ ⟶ b₂) (rEv : b₂ ⟶ c₃)
    (FresYρ : b₂ ⟶ b₃) (rExt : b₃ ⟶ c₄) (FηfY : a ⟶ b₃)
    (e₁ : ηfX ≫ RρXinv = ηX ≫ πXred)
    (e₂ : πXred ≫ RevXαinv = limαinv ≫ πXG)
    (e₃ : FηY ≫ LredY ≫ limα = ηX)
    (e₄ : limα ≫ limαinv = 𝟙 m₂)
    (e₅ : FπY ≫ rEv = LredY ≫ πXG ≫ Rev)
    (e₆ : rEv ≫ RHρ = FresYρ ≫ rExt)
    (e₇ : FηY ≫ FπY ≫ FresYρ = FηfY)
    (e₈ : FηfY ≫ rExt ≫ Rφ = ηfX) :
    ηfX ≫ RρXinv ≫ RevXαinv ≫ Rev ≫ RHρ ≫ Rφ = ηfX := by
  rw [reassoc_of% e₁, reassoc_of% e₂, ← e₃]
  simp only [Category.assoc]
  rw [reassoc_of% e₄, ← reassoc_of% e₅, reassoc_of% e₆, reassoc_of% e₇, e₈]


end PodReindexingReductionEvaluation

open PodReindexingReductionEvaluation

/-- The assembled datum of raw derived comparison data `Q` with the canonical restriction and
evaluation comparisons, and with finite, limit and reduction comparisons satisfying the
finite-model, limit-model and unit laws, satisfies the reduction-evaluation law. -/
theorem podReindexingDerivedCoreData_reductionEvaluation
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (S : PodReindexingStrictData l E g) (hS : S.Laws l E g SY SX)
    (β : ∀ (P : CochainComplex (scalarReductionSource l E Y) ℤ),
      integralOperationsGoodComplex l E Y P → ∀ n : ℕ,
      (isoReductionFiniteComplex l E g n).obj (unrestrictedTowerFiniteComplex l E Y n P) ≅
        unrestrictedTowerFiniteComplex l E X n
          ((isoReductionIntegralComplex l E g).obj P))
    (hβ : podReindexingCoreQuotientGenerators l E g β)
    (htransition : podReindexingCoreQuotientTransition l E g β)
    (CY : IntegralOnSlice.completion l E Y none ≅
      (podReindexCalculus l E Y).reduction ⋙ coefficientSequenceLimit l E Y)
    (CX : IntegralOnSlice.completion l E X none ≅
      (podReindexCalculus l E X).reduction ⋙ coefficientSequenceLimit l E X)
    (Q : PodReindexingDerivedCoreData l E g)
    (hrestriction : ∀ n, Q.restriction n = podReindexingDerivedRestriction l E g n)
    (hevaluation : ∀ n, Q.evaluation n = podReindexingDerivedEvaluation l E g n)
    (hfinite : PodCompletionReindex.FiniteModel l E g (Q.assemble l E g SY SX S β CY CX))
    (hlimit : PodCompletionReindex.LimitModel l E g (Q.assemble l E g SY SX S β CY CX))
    (hunit : PodCompletionReindex.Unit l E g (Q.assemble l E g SY SX S β CY CX)) :
    PodCompletionReindex.ReductionEvaluation l E g
      (Q.assemble l E g SY SX S β CY CX) := by
  intro K n
  dsimp only [PodReindexingDerivedCoreData.assemble]
  have hproj := podReindexingDerivedCoreData_limitProjection l E g SY SX S hS β hβ htransition
    CY CX Q hrestriction hevaluation hlimit ((podReindexCalculus l E Y).reduction.obj K) n
  dsimp only [PodReindexingDerivedCoreData.assemble] at hproj
  have hmate := finite_mate l E g SY SX S β hβ CY CX Q hfinite n K
  rw [← hrestriction n] at hmate
  have hU := hunit K
  dsimp only [PodReindexingDerivedCoreData.assemble] at hU
  have upX := (podReindexCalculus l E X).unit_projection ((podOrdinaryReindex l E g).obj K) n
  have upY := (podReindexCalculus l E Y).unit_projection K n
  have e₇ : (podOrdinaryReindex l E g).map ((podReindexCalculus l E Y).adjunction.unit.app K) ≫
      (podOrdinaryReindex l E g).map ((coefficientSequenceProjection l E Y n).app
        ((podReindexCalculus l E Y).reduction.obj K)) ≫
      (podOrdinaryReindex l E g).map ((coefficientFiniteDerivedRestriction l E Y n).map
        (((podReindexCalculus l E Y).reductionEvaluation n).hom.app K)) =
      (podOrdinaryReindex l E g).map ((coefficientFiniteAdjunction l E Y n).unit.app K) := by
    rw [← Functor.map_comp, ← Functor.map_comp, ← Category.assoc, upY, Category.assoc,
      ← Functor.map_comp, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id]
    erw [Category.comp_id]
  let u := ((podReindexCalculus l E X).reductionEvaluation n).inv.app
      ((podOrdinaryReindex l E g).obj K) ≫
    (coefficientSequenceDerivedEvaluation l E X n).map (Q.reduction.inv.app K)
  have hu₁ : u ≫ (coefficientSequenceDerivedEvaluation l E X n).map (Q.reduction.hom.app K) ≫
      ((podReindexCalculus l E X).reductionEvaluation n).hom.app
        ((podOrdinaryReindex l E g).obj K) = 𝟙 _ := by
    simp only [u, Category.assoc]
    rw [← Functor.map_comp_assoc, Iso.inv_hom_id_app]
    erw [CategoryTheory.Functor.map_id, Category.id_comp]
    exact Iso.inv_hom_id_app _ _
  have hu₂ : u ≫ (Q.evaluation n).hom.app ((podReindexCalculus l E Y).reduction.obj K) ≫
      (isoReductionFiniteDerived l E g n).map
        (((podReindexCalculus l E Y).reductionEvaluation n).hom.app K) ≫
      (Q.finite n).hom.app K = 𝟙 _ := by
    apply ((coefficientFiniteAdjunction l E X n).homEquiv _ _).injective
    simp only [Adjunction.homEquiv_unit, Functor.map_comp, CategoryTheory.Functor.map_id, u,
      Category.assoc]
    refine (reductionEvaluation_abstract _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ upX.symm
      ((coefficientSequenceProjection l E X n).naturality (Q.reduction.inv.app K)).symm hU
      ((coefficientSequenceLimit l E X).mapIso (Q.reduction.app K)).hom_inv_id hproj
      ((Q.restriction n).hom.naturality
        (((podReindexCalculus l E Y).reductionEvaluation n).hom.app K)).symm e₇ hmate).trans
      (Category.comp_id _).symm
  have : IsIso u := by dsimp only [u]; infer_instance
  exact (cancel_epi u).1 (hu₁.trans hu₂.symm)

end WeilConjectures
