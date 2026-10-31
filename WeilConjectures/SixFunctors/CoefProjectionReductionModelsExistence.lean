/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.CoefHomTowerScalarData
public import WeilConjectures.AlgebraicGeometry.CoefficientSystemScalarCalculus
import Mathlib.CategoryTheory.Adjunction.Unique
import WeilConjectures.AlgebraicGeometry.PurSequenceOrdinaryFactorization
import all WeilConjectures.AlgebraicGeometry.SequenceSiteCompletionProjectionSupplement
import all WeilConjectures.AlgebraicGeometry.RingedTopoiDerivedPullbackIndependentSupplement
import all WeilConjectures.AlgebraicGeometry.RingIsoQuotientSystemTransport
import all WeilConjectures.AlgebraicGeometry.PurSequenceConstantRingFactorization

/-! # Strict reduction for the scalar extension of constant systems

Source: Stacks Project, Cohomology on Sites, Tags 07A4, 07A6, 08J9, 0D6D and 0B56.
(blueprint: lem-sf-coef-projection-reduction-models-existence).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.hasSheafCompose_of_preservesMulticospan
attribute [local instance 11000] CategoryTheory.hasSheafCompose_of_preservesLimitsOfSize
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology
attribute [local instance 30000] CategoryTheory.essentiallySmall_of_small_of_locallySmall
attribute [local instance 11000] SheafOfModules.hasSheafify_coefficientUniverse
  SheafOfModules.wEqualsLocallyBijective_coefficientUniverse
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible] CategoryTheory.Functor.leftAdjoint
  CategoryTheory.Functor.mapDerivedCategory CategoryTheory.Functor.rightDerivedFunctor
  HasDerivedCategory.standard
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme SheafOfModules
namespace WeilConjectures.CoefProjectionEvaluation
attribute [local instance 2000] Limits.instHasColimitOfHasColimitsOfShape
  Limits.instHasLimitOfHasLimitsOfShape
attribute [-instance] SemilinearSections.hasDerived SemilinearSections.moduleAbelian
  SemilinearSections.abelianSheafify SemilinearSections.locallyBijective
  SemilinearSections.sequenceSmall SemilinearSections.sliceSmall
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

private theorem restriction_towers (W : Scheme.{u}) :
    coefHomOrdinaryRestriction l E W ⋙ (coefHomEquivalence l E W).functor =
      coefficientSequenceRestriction l E W := by
  exact firstFactor_restriction l E W

private def constant_adjunction (W : Scheme.{u}) :
    coefHomConstant l E W ⊣
      (coefHomEquivalence l E W).functor ⋙
        (lim : (ℕᵒᵖ ⥤ scalarReductionSource l E W) ⥤ _) := by
  let e := coefHomEquivalence l E W
  exact constLimAdj.comp e.symm.toAdjunction

private def ordinary_adjunction (W : Scheme.{u})
    (S : ScalarHomModels.{u + 1, u, u, u + 2}
      (coefficientSequenceTopology (ProEt.topology W))) :
    (coefHomConstant l E W ⋙ (S.scalar (coefHomScalarMap l E W)).extension) ⊣
      (coefficientSequenceRestriction l E W ⋙ lim) := by
  let a := (constant_adjunction l E W).comp
    (S.scalar (coefHomScalarMap l E W)).ordinaryAdjunction
  exact a.ofNatIsoRight ((Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (eqToIso (restriction_towers l E W)) lim)

private theorem constant_kflat (W : Scheme.{u})
    (P : CochainComplex (scalarReductionSource l E W) ℤ)
    (hp : CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1} P
      (J := ProEt.topology W)
      (R := completedIntegralCommRingSheafUnrestricted l E W))
    (hf : SemilinearSections.flatTerms.{u + 1, u, u}
      (ProEt.topology W) (completedIntegralCommRingSheafUnrestricted l E W) P) :
    CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
      (J := coefficientSequenceTopology (ProEt.topology W))
      (R := coefHomConstantRing l E W)
      (((coefHomConstant l E W).mapHomologicalComplex (.up ℤ)).obj P) := by
  let J := ProEt.topology W
  let A := completedIntegralCommRingSheafUnrestricted l E W
  let L := SemilinearSections.seqConstant.{u + 1, u, u + 1} J
  let V := SemilinearSections.seqSetsTower.{u + 1, u, u + 1} J ⋙ lim
  let I : AlgebraicInverseImage L A (coefHomConstantRing l E W) :=
    { ringUnderlying := ObjectProperty.isoMk _
        (NatIso.ofComponents (fun _ ↦ Iso.refl _) (by intros; rfl))
      ringAdd := by intro T a b t h U x; exact h (op U.unop.2) x
      ringMul := by intro T a b t h U x; exact h (op U.unop.2) x
      ringZero := by intro T a h U x; exact h (op U.unop.2) x
      ringOne := by intro T a h U x; exact h (op U.unop.2) x
      modules := coefHomConstant l E W
      moduleUnderlying := NatIso.ofComponents
        (fun _ ↦ ObjectProperty.isoMk _
          (NatIso.ofComponents (fun _ ↦ Iso.refl _) (by
            intros; ext x; rfl)))
        (by intros; ext U x; rfl)
      moduleAdd := by intro M T a b t h U x; exact h (op U.unop.2) x
      moduleZero := by intro M T a h U x; exact h (op U.unop.2) x
      moduleSMul := by intro M T a b t h U x; exact h (op U.unop.2) x }
  exact SheafOfModules.kFlat_inverseImage_independent L V
    (SemilinearSections.seqAdjunction.{u + 1, u, u + 1} J) I P hp hf

/-- Constant completed-coefficient systems followed by the prescribed derived scalar
extension have the strict simultaneous reduction model. The scalar model is fixed;
no Hom-tower comparison or compact-support operation is asserted here.

Source: Stacks 06YY, 07A6 and 0941; ordinary quotient pullback and comparison
of left-derived functors on flat-term K-flat resolutions.
(blueprint: lem-sf-coef-projection-reduction-models-existence).

Proof: represent K by a flat-term K-flat P. The exact constant-system inverse
image preserves K-flatness. Apply the normalized scalar pair to const P; its
left-derived counit computes scalar extension by the actual quotient ring sheaf.
The resulting complex C has level P tensor A_(n+1) and horizontal map id tensor
the quotient. Evaluation on each vertical slice gives its ordinary scalar-extension
complex, with the same tensor-unit normalization. The universal left-derived
comparison identifies this evaluation with coefficientFiniteDerivedExtension;
these identifications extend naturally from K-flat representatives to every K.
The scalar-pair counit equation is CoefficientComparisonEquation, and ordinary
quotient naturality is CoefficientTransitionEquation. Thus one C and one family
of comparisons simultaneously satisfy every clause of CoefficientReductionModels.
No flatness of a quotient map is needed; for equal levels its quotient transition
is the identity, and zero complexes give the zero reduction. -/
theorem coefficientProjectionReductionModels_exists (W : Scheme.{u})
    (S : ScalarHomModels.{u + 1, u, u, u + 2}
      (coefficientSequenceTopology (ProEt.topology W))) :
    ∃ ρ : ∀ n : ℕ,
      (coefHomDerivedConstant l E W ⋙ (S.scalar (coefHomScalarMap l E W)).derived) ⋙
        coefficientSequenceDerivedEvaluation l E W n ≅ coefficientFiniteDerivedExtension l E W n,
      CoefficientReductionModels l E W
        (coefHomDerivedConstant l E W ⋙ (S.scalar (coefHomScalarMap l E W)).derived) ρ := by
  classical
  let s := S.scalar (coefHomScalarMap l E W)
  let := s.extension_additive
  let F := (coefHomConstant l E W).mapHomologicalComplex (.up ℤ)
  let R := coefHomDerivedConstant l E W ⋙ s.derived
  obtain ⟨O, _⟩ := purSequenceOrdinaryFactorization l E W
  let a : coefHomConstant l E W ⋙ s.extension ≅ O.pullback :=
    (ordinary_adjunction l E W S).leftAdjointUniq
      (O.adjunction.ofNatIsoRight O.limit)
  let εs : DerivedCategory.Q ⋙ s.derived ⟶
      s.extension.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
    { app := fun P ↦ s.counit.app ((HomotopyCategory.quotient _ (.up ℤ)).obj P)
      naturality := fun _ _ f ↦
        s.counit.naturality ((HomotopyCategory.quotient _ (.up ℤ)).map f) }
  have hεs (P : CochainComplex (scalarModules
      (coefficientSequenceTopology (ProEt.topology W)) (coefHomConstantRing l E W)) ℤ)
      (hP : CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1} P) :
      IsIso (εs.app P) := by
    have h := s.computes P hP
    let f := s.derived.map ((DerivedCategory.quotientCompQhIso _).inv.app P)
    let g := s.counit.app ((HomotopyCategory.quotient _ (.up ℤ)).obj P)
    let k := (DerivedCategory.quotientCompQhIso _).hom.app
      ((s.extension.mapHomologicalComplex (.up ℤ)).obj P)
    have hk : IsIso k := by dsimp [k]; infer_instance
    have hfi : IsIso f := by dsimp [f]; infer_instance
    have hfgk : IsIso (f ≫ g ≫ k) := by
      simpa only [scalarPairComplexComparison, scalarComplex, f, g, k,
        HomotopyCategory.quotient_obj_as] using h
    have hgk : IsIso (g ≫ k) := @IsIso.of_isIso_comp_left _ _ _ _ _ f (g ≫ k) hfi hfgk
    have hg : IsIso g := @IsIso.of_isIso_comp_right _ _ _ _ _ g k hk hgk
    exact (show IsIso g from inferInstance)
  let ε : DerivedCategory.Q ⋙ R ⟶
      O.pullback.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
    Functor.whiskerRight (coefHomConstant l E W).mapDerivedCategoryFactors.hom s.derived ≫
      Functor.whiskerLeft F εs ≫
      Functor.whiskerRight (NatIso.mapHomologicalComplex a (.up ℤ)).hom DerivedCategory.Q
  have hε (P : CochainComplex (scalarReductionSource l E W) ℤ)
      (hP : CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1} P)
      (hf : SemilinearSections.flatTerms.{u + 1, u, u}
      (ProEt.topology W) (completedIntegralCommRingSheafUnrestricted l E W) P) :
      IsIso (ε.app P) := by
    have := hεs (F.obj P) (constant_kflat l E W P hP hf)
    change IsIso (s.derived.map
      ((coefHomConstant l E W).mapDerivedCategoryFactors.hom.app P) ≫
        εs.app (F.obj P) ≫
          DerivedCategory.Q.map ((NatIso.mapHomologicalComplex a (.up ℤ)).hom.app P))
    exact (s.derived.mapIso ((coefHomConstant l E W).mapDerivedCategoryFactors.app P) ≪≫
      asIso (εs.app (F.obj P)) ≪≫
        DerivedCategory.Q.mapIso ((NatIso.mapHomologicalComplex a (.up ℤ)).app P)).isIso_hom
  let η (n : ℕ) : DerivedCategory.Q ⋙
      (R ⋙ coefficientSequenceDerivedEvaluation l E W n) ⟶
      (scalarReductionExtension l E W n).mapHomologicalComplex (.up ℤ) ⋙
        DerivedCategory.Q :=
    Functor.whiskerRight ε (coefficientSequenceDerivedEvaluation l E W n) ≫
      Functor.whiskerLeft (O.pullback.mapHomologicalComplex (.up ℤ))
        (coefficientSequenceEvaluation l E W n).mapDerivedCategoryFactors.hom ≫
      Functor.whiskerRight
        (NatIso.mapHomologicalComplex (O.tensor n) (.up ℤ)).hom DerivedCategory.Q
  let θ (n : ℕ) : DerivedCategory.Q ⋙ coefficientFiniteDerivedExtension l E W n ⟶
      (scalarReductionExtension l E W n).mapHomologicalComplex (.up ℤ) ⋙
        DerivedCategory.Q :=
    { app := fun P ↦ (scalarReductionCounit l E W n).app
        ((HomotopyCategory.quotient _ (.up ℤ)).obj P)
      naturality := fun _ _ f ↦ (scalarReductionCounit l E W n).naturality
        ((HomotopyCategory.quotient _ (.up ℤ)).map f) }
  let p : CochainComplex (scalarReductionSource l E W) ℤ → Prop := fun P ↦
    CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1} P ∧
      SemilinearSections.flatTerms.{u + 1, u, u}
        (ProEt.topology W) (completedIntegralCommRingSheafUnrestricted l E W) P
  have hρ (n : ℕ) : ∃ b : R ⋙ coefficientSequenceDerivedEvaluation l E W n ≅
      coefficientFiniteDerivedExtension l E W n,
      ∀ P, b.hom.app (DerivedCategory.Q.obj P) ≫ (θ n).app P = (η n).app P := by
    apply SheafOfModules.QuotientIsoTransport.comparisonFromResolutions p
      (by
        intro K
        simpa only [p, SemilinearSections.flatTerms] using
          SheafOfModules.QuotientIsoTransport.reductionResolution
            (completedIntegralCommRingSheafUnrestricted l E W) K)
      _ _ _ (η n) (θ n)
    · intro P hP
      have := hε P hP.1 hP.2
      change IsIso ((coefficientSequenceDerivedEvaluation l E W n).map (ε.app P) ≫
        (coefficientSequenceEvaluation l E W n).mapDerivedCategoryFactors.hom.app
          ((O.pullback.mapHomologicalComplex (.up ℤ)).obj P) ≫
            DerivedCategory.Q.map
              ((NatIso.mapHomologicalComplex (O.tensor n) (.up ℤ)).hom.app P))
      exact ((coefficientSequenceDerivedEvaluation l E W n).mapIso (asIso (ε.app P)) ≪≫
        (coefficientSequenceEvaluation l E W n).mapDerivedCategoryFactors.app
          ((O.pullback.mapHomologicalComplex (.up ℤ)).obj P) ≪≫
            DerivedCategory.Q.mapIso
              ((NatIso.mapHomologicalComplex (O.tensor n) (.up ℤ)).app P)).isIso_hom
    · intro P hP
      exact coefficientFiniteReductionCounit_isIso l E W P hP.1 n
  choose ρ hρ using hρ
  refine ⟨ρ, ?_⟩
  intro P hP hf
  have hf' : SemilinearSections.flatTerms.{u + 1, u, u}
      (ProEt.topology W) (completedIntegralCommRingSheafUnrestricted l E W) P := by
    dsimp only [SemilinearSections.flatTerms]
    exact hf
  have := hε P hP hf'
  refine ⟨(O.pullback.mapHomologicalComplex (.up ℤ)).obj P, asIso (ε.app P),
    fun n ↦ (NatIso.mapHomologicalComplex (O.tensor n) (.up ℤ)).app P, ?_, ?_⟩
  · intro n
    have hh := (hρ n P).symm
    change (coefficientSequenceDerivedEvaluation l E W n).map (ε.app P) ≫
        (coefficientSequenceEvaluation l E W n).mapDerivedCategoryFactors.hom.app
          ((O.pullback.mapHomologicalComplex (.up ℤ)).obj P) ≫
            DerivedCategory.Q.map
              ((NatIso.mapHomologicalComplex (O.tensor n) (.up ℤ)).hom.app P) =
      (ρ n).hom.app (DerivedCategory.Q.obj P) ≫ (θ n).app P at hh
    have hm : (coefficientFiniteReductionModel l E W P hP n).hom = (θ n).app P := by
      change (coefficientFiniteDerivedExtension l E W n).map (𝟙 _) ≫
        (θ n).app P ≫ 𝟙 _ = _
      erw [(coefficientFiniteDerivedExtension l E W n).map_id]
      simp only [Category.id_comp, Category.comp_id]
    change (coefficientSequenceDerivedEvaluation l E W n).map (ε.app P) ≫
        (coefficientSequenceEvaluation l E W n).mapDerivedCategoryFactors.hom.app
          ((O.pullback.mapHomologicalComplex (.up ℤ)).obj P) ≫
            DerivedCategory.Q.map
              ((NatIso.mapHomologicalComplex (O.tensor n) (.up ℤ)).hom.app P) =
      (ρ n).hom.app (DerivedCategory.Q.obj P) ≫
        (coefficientFiniteReductionModel l E W P hP n).hom
    rw [hm]
    exact hh
  · intro m n h
    dsimp only [CoefficientTransitionEquation]
    apply HomologicalComplex.hom_ext
    intro i
    exact O.tensor_transition (P.X i) m n h

end WeilConjectures.CoefProjectionEvaluation
