/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.TraceFormula.CompletionUnit.CompletionUnitModels
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
public import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientGerm
public import WeilConjectures.Algebra.Homology.SixFunctors.OrdinaryDerivedChangeOfRings
import WeilConjectures.CategoryTheory.Derived.DerivedTowerCounitProjections
import WeilConjectures.TraceFormula.CompletionUnit.CompletionUnitStrictQuotientModel
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback

/-! # Simultaneous Roos, counit and strict quotient-unit normalization

Source: Stacks Project, Cohomology on Sites, Tag 0941, lemma-derived-limit-is-ok;
whole-system adjunction and quotient-unit refinements extracted from the integral
trace-transport construction (blueprint: lem-trf-roos-adjunction-quotient-normalization).

The coefficient field F is arbitrary: apply this statement to each of E, L and M.
No distinctness or compatibility between different coefficient fields is required.
Index n denotes the positive quotient exponent n+1. The site and coefficient
universes remain independent. All categories are ordinary unbounded derived categories.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe t u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace WeilConjectures

private theorem constant_limit_comparison_naturality
    {A : Type*} [Category* A] [Abelian A] [HasLimitsOfShape ℕᵒᵖ A]
    [HasDerivedCategory A] [HasDerivedCategory (ℕᵒᵖ ⥤ A)]
    (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ)
    (e : (lim : (ℕᵒᵖ ⥤ A) ⥤ A).mapHomologicalComplex (.up ℤ) ≅
      roosLimitFunctor) :
    (Functor.const ℕᵒᵖ : A ⥤ ℕᵒᵖ ⥤ A).mapDerivedCategory.map
        (DerivedCategory.Q.map (e.inv.app I)) ≫
      (Functor.const ℕᵒᵖ : A ⥤ ℕᵒᵖ ⥤ A).mapDerivedCategoryFactors.hom.app
        (((lim : (ℕᵒᵖ ⥤ A) ⥤ A).mapHomologicalComplex (.up ℤ)).obj I) ≫
      DerivedCategory.Q.map
        (((constLimAdj : (Functor.const ℕᵒᵖ : A ⥤ ℕᵒᵖ ⥤ A) ⊣ lim).mapHomologicalComplex
          (.up ℤ)).counit.app I) =
    (Functor.const ℕᵒᵖ : A ⥤ ℕᵒᵖ ⥤ A).mapDerivedCategoryFactors.hom.app
        (limit I.asFunctor) ≫
      DerivedCategory.Q.map
        (((Functor.const ℕᵒᵖ : A ⥤ ℕᵒᵖ ⥤ A).mapHomologicalComplex (.up ℤ)).map (e.inv.app I) ≫
          ((constLimAdj : (Functor.const ℕᵒᵖ : A ⥤ ℕᵒᵖ ⥤ A) ⊣ lim).mapHomologicalComplex
            (.up ℤ)).counit.app I) := by
  rw [DerivedCategory.Q.map_comp]
  exact (Functor.const ℕᵒᵖ : A ⥤ ℕᵒᵖ ⥤ A).mapDerivedCategoryFactors_hom_naturality_assoc
    (e.inv.app I) _

private theorem generic_limit_adjunction
    (A : Type*) [Category* A] [Abelian A] [HasLimitsOfShape ℕᵒᵖ A]
    [HasDerivedCategory A] [HasDerivedCategory (ℕᵒᵖ ⥤ A)]
    [Abelian.HasKInjectiveResolutions (ℕᵒᵖ ⥤ A)]
    (e : (lim : (ℕᵒᵖ ⥤ A) ⥤ A).mapHomologicalComplex (.up ℤ) ≅ roosLimitFunctor)
    (α : roosLimitFunctor ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙
      (lim : (ℕᵒᵖ ⥤ A) ⥤ A).rightDerivedFunctor)
    (hα : ∀ (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) [I.IsKInjective],
      α.app I ≫ (lim.rightDerivedFunctorObjQIso I).hom =
        DerivedCategory.Q.map (e.inv.app I)) :
    ∃ adj : (Functor.const ℕᵒᵖ : A ⥤
        ℕᵒᵖ ⥤ A).mapDerivedCategory ⊣
          (lim : (ℕᵒᵖ ⥤ A) ⥤ A).rightDerivedFunctor,
      ∀ (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) [I.IsKInjective],
        (Functor.const ℕᵒᵖ : A ⥤
            ℕᵒᵖ ⥤ A).mapDerivedCategory.map
            (α.app I) ≫ adj.counit.app (DerivedCategory.Q.obj I) =
          (Functor.const ℕᵒᵖ : A ⥤
            ℕᵒᵖ ⥤ A).mapDerivedCategoryFactors.hom.app
              (limit I.asFunctor) ≫
            DerivedCategory.Q.map
              (((Functor.const ℕᵒᵖ : A ⥤
                ℕᵒᵖ ⥤ A).mapHomologicalComplex (.up ℤ)).map
                  (e.inv.app I) ≫
                ((constLimAdj :
                  (Functor.const ℕᵒᵖ : A ⥤
                    ℕᵒᵖ ⥤ A) ⊣ lim).mapHomologicalComplex
                      (.up ℤ)).counit.app I) := by
  let T : (ℕᵒᵖ ⥤ A) ⥤ A := lim
  let η : T.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ (lim : (ℕᵒᵖ ⥤ A) ⥤ A).rightDerivedFunctor :=
    { app := T.rightDerivedFunctorUnitQ
      naturality := fun _ _ f ↦ T.rightDerivedFunctorUnitQ_naturality f }
  have hd : (CochainComplex.KInjectives.localizerMorphism (ℕᵒᵖ ⥤ A)).Derives
      (T.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q) := by
    intro X Y f hf
    have : X.obj.IsKInjective := X.property
    have : Y.obj.IsKInjective := Y.property
    have : QuasiIso f.hom := hf
    obtain ⟨e, he⟩ := (CochainComplex.IsKInjective.quasiIso_iff f.hom).mp hf
    have : QuasiIso ((T.mapHomologicalComplex (.up ℤ)).map f.hom) := by
      rw [← he]
      exact (T.mapHomotopyEquiv e).quasiIso_hom
    change IsIso (DerivedCategory.Q.map ((T.mapHomologicalComplex (.up ℤ)).map f.hom))
    infer_instance
  have hη (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (hI : I.IsKInjective) :
      IsIso (η.app I) := by
    change IsIso (T.rightDerivedFunctorUnitQ I)
    rw [T.rightDerivedFunctorUnitQ_eq]
    infer_instance
  let : ((lim : (ℕᵒᵖ ⥤ A) ⥤ A).rightDerivedFunctor).IsRightDerivedFunctor η
      (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ A) (.up ℤ)) := by
    apply hd.isRightDerivedFunctor_of_isIso
    intro I
    exact hη I.obj I.property
  have hηuniv (G : DerivedCategory (ℕᵒᵖ ⥤ A) ⥤ DerivedCategory A) :
      Function.Bijective (fun β : (lim : (ℕᵒᵖ ⥤ A) ⥤ A).rightDerivedFunctor ⟶ G ↦
        η ≫ Functor.whiskerLeft DerivedCategory.Q β) := by
    constructor
    · intro f g hfg
      exact Functor.rightDerived_ext _ η
        (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ A) (.up ℤ)) G f g hfg
    · intro β
      exact ⟨Functor.rightDerivedDesc _ η
        (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ A) (.up ℤ)) G β,
        Functor.rightDerived_fac _ η _ G β⟩
  obtain ⟨adj, c, π, _, hc, _⟩ :=
    derived_tower_counit_projections.{_, _, _, _, 0, 0} A
    (fun X ↦ by
      obtain ⟨I, hI, q, _, hq⟩ := Abelian.HasKInjectiveResolutions.exists_isKInjective X
      exact ⟨I, q, hI, hq⟩)
    ((lim : (ℕᵒᵖ ⥤ A) ⥤ A).rightDerivedFunctor) η hηuniv hη
  refine ⟨adj, ?_⟩
  intro I _
  have hn : α.app I =
      DerivedCategory.Q.map (e.inv.app I) ≫ η.app I := by
    apply (cancel_mono (T.rightDerivedFunctorObjQIso I).hom).1
    rw [hα]
    dsimp only [η]
    rw [Category.assoc, T.rightDerivedFunctorUnitQ_eq,
      Iso.inv_hom_id, Category.comp_id]
  rw [hn, Functor.map_comp, Category.assoc, hc I inferInstance]
  exact constant_limit_comparison_naturality (A := A) I e

section Normalization

variable (l : ℕ) [Fact l.Prime] (F : Type u) [Field F]
  [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F] (W : Scheme.{t})
  {S : CoefficientDerivedSystemCalculus l F W}
  {M : CompletionUnit.OrdinaryModel l F W}
  (D : CompletionUnit.DerivedModel l F W S M)

private theorem limitUnit_isIso
    (I : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l F W) ℤ) [I.IsKInjective] :
    IsIso (D.limitUnit.app I) := by
  have : IsIso (D.limitUnit.app I ≫
      ((lim : (ℕᵒᵖ ⥤ scalarReductionSource l F W) ⥤
        scalarReductionSource l F W).rightDerivedFunctorObjQIso I).hom) := by
    rw [D.limitUnit_normalization]
    infer_instance
  exact IsIso.of_isIso_comp_right _
    ((lim : (ℕᵒᵖ ⥤ scalarReductionSource l F W) ⥤
      scalarReductionSource l F W).rightDerivedFunctorObjQIso I).hom

include D in
private theorem inclusion_quasiIso
    (I : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l F W) ℤ) [I.IsKInjective] :
    QuasiIso (roosι I) := by
  have := limitUnit_isIso l F W D I
  have : IsIso (DerivedCategory.Q.map (roosι I) ≫ D.roos.hom.app I) := by
    rw [D.roos_normalization]
    infer_instance
  have : IsIso (DerivedCategory.Q.map (roosι I)) :=
    IsIso.of_isIso_comp_right _ (D.roos.hom.app I)
  exact (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).mp this

private theorem limitUnit_projection
    (I : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l F W) ℤ) [I.IsKInjective]
    (n : ℕ) :
    D.limitUnit.app I ≫ (coefficientConstantTowerProjection l F W n).app
        (DerivedCategory.Q.obj I) ≫
      (coefficientConstantTowerEvaluationFactors l F W n).hom.app I =
      DerivedCategory.Q.map (limit.π I.asFunctor (op n)) := by
  have hp := (coefficientConstantTowerProjection_exists l F W n).choose_spec.1 I
  change (coefficientConstantTowerProjection l F W n).app _ ≫ _ = _ at hp
  rw [hp, ← Category.assoc, D.limitUnit_normalization,
    ← DerivedCategory.Q.map_comp]
  congr 1
  apply (cancel_epi (D.towerLimitComparison.hom.app I)).1
  rw [Iso.hom_inv_id_app_assoc]
  apply HomologicalComplex.hom_ext
  intro p
  exact (D.towerLimitComparison_projection I n p).symm

private theorem roos_projection
    (X : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l F W) ℤ) (n : ℕ) :
    D.roos.hom.app X ≫ (coefficientConstantTowerProjection l F W n).app
        (DerivedCategory.Q.obj X) ≫
      (coefficientConstantTowerEvaluationFactors l F W n).hom.app X =
      DerivedCategory.Q.map (roosEval X n) := by
  have hi (I : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l F W) ℤ)
      [I.IsKInjective] :
      D.roos.hom.app I ≫ (coefficientConstantTowerProjection l F W n).app
          (DerivedCategory.Q.obj I) ≫
        (coefficientConstantTowerEvaluationFactors l F W n).hom.app I =
        DerivedCategory.Q.map (roosEval I n) := by
    have := inclusion_quasiIso l F W D I
    apply (cancel_epi (DerivedCategory.Q.map (roosι I))).1
    rw [← Category.assoc, ← Category.assoc, D.roos_normalization, Category.assoc,
      limitUnit_projection, ← DerivedCategory.Q.map_comp, roosι_eval]
  obtain ⟨I, hI, q, _, hq⟩ := Abelian.HasKInjectiveResolutions.exists_isKInjective X
  have : QuasiIso q := hq
  let V := (evaluation ℕᵒᵖ (scalarReductionSource l F W)).obj (op n)
  apply (cancel_mono (DerivedCategory.Q.map
    ((V.mapHomologicalComplex (.up ℤ)).map q))).1
  have hv := V.mapDerivedCategoryFactors.hom.naturality q
  have hp := (coefficientConstantTowerProjection l F W n).naturality
    (DerivedCategory.Q.map q)
  have hr := D.roos.hom.naturality q
  dsimp only [Functor.comp_map] at hv hr
  simp only [Category.assoc]
  rw [← hv]
  erw [← reassoc_of% hp, ← reassoc_of% hr, hi I]
  rw [← DerivedCategory.Q.map_comp, roosEval_natural, DerivedCategory.Q.map_comp]
  rfl

private theorem limit_adjunction :
    ∃ adj : (Functor.const ℕᵒᵖ : scalarReductionSource l F W ⥤
        ℕᵒᵖ ⥤ scalarReductionSource l F W).mapDerivedCategory ⊣
          coefficientConstantTowerLimit l F W,
      ∀ (I : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l F W) ℤ) [I.IsKInjective],
        (Functor.const ℕᵒᵖ : scalarReductionSource l F W ⥤
            ℕᵒᵖ ⥤ scalarReductionSource l F W).mapDerivedCategory.map
            (D.limitUnit.app I) ≫ adj.counit.app (DerivedCategory.Q.obj I) =
          (Functor.const ℕᵒᵖ : scalarReductionSource l F W ⥤
            ℕᵒᵖ ⥤ scalarReductionSource l F W).mapDerivedCategoryFactors.hom.app
              (limit I.asFunctor) ≫
            DerivedCategory.Q.map
              (((Functor.const ℕᵒᵖ : scalarReductionSource l F W ⥤
                ℕᵒᵖ ⥤ scalarReductionSource l F W).mapHomologicalComplex (.up ℤ)).map
                  (D.towerLimitComparison.inv.app I) ≫
                ((constLimAdj :
                  (Functor.const ℕᵒᵖ : scalarReductionSource l F W ⥤
                    ℕᵒᵖ ⥤ scalarReductionSource l F W) ⊣ lim).mapHomologicalComplex
                      (.up ℤ)).counit.app I) := by
  exact generic_limit_adjunction (scalarReductionSource l F W) D.towerLimitComparison
    D.limitUnit D.limitUnit_normalization

end Normalization

/-- One normalized Roos comparison for all strict completed-coefficient towers,
with the actual whole-system counit and the strict quotient augmentation unit.
Source: Stacks 0941, lemma-derived-limit-is-ok, and the stated whole-system
adjunction/quotient-unit refinements
(blueprint: lem-trf-roos-adjunction-quotient-normalization).

Proof:
1. Take S, its coherence, M and D from completionUnitStrictQuotientModel.
   Retain its section, zero-coordinate and whole-unit formulas. Set H to the
   specified constant tower limit, κ to D.roos and ρ to the identity.
2. The normalization of D.limitUnit on K-injective towers makes it invertible.
   The equation Q(roosι) D.roos = D.limitUnit therefore makes roosι a
   quasi-isomorphism. Its coordinates are the existing equation roosι_χ.
3. The uniquely specified derived projections and towerLimitComparison_projection
   identify D.limitUnit followed by each evaluation with the ordinary projection.
   Cancel Q(roosι) to obtain the Roos evaluation equation on K-injectives.
   Naturality along a K-injective resolution gives that equation for every X.
4. Construct the ordinary limit's canonical right-derived comparison on complexes.
   Quasi-isomorphisms between K-injectives are homotopy equivalences, so this
   comparison has the required derived universal property. Apply
   derived_tower_counit_projections. The normalization of D.limitUnit and
   naturality of the exact constant functor's factorization give its whole-tower
   counit equation on every K-injective I.
5. For each q:X→I take j=asIso Q(roosι I), and take d to be asIso(D.limitUnit I)
   followed by the inverse of the derived limit of Q(q). The Roos naturality
   square and normalization give the comparison formula. Naturality of the
   projections and evaluated localization comparison gives the resolution
   projection formula. Counit naturality transports the entire counit equation
   along Q(q), without any detection of tower maps by evaluation.
6. S.counit_projection is the required finite scalar adjunct equation. Retain
   the first three conjuncts of the quotient-model theorem for every P. -/
theorem roosAdjunctionQuotientNormalization
    (l : ℕ) [Fact l.Prime] (F : Type u) [Field F]
    [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F] (W : Scheme.{t})
    [∀ x : W, Invertible (l : W.residueField x)] :
    ∃ (S : CoefficientDerivedSystemCalculus l F W)
      (_coherence : CoefficientDerivedSystemCoherence l F W S)
      (M : CompletionUnit.OrdinaryModel l F W)
      (D : CompletionUnit.DerivedModel l F W S M)
      (H : coefficientSequenceRestrictedDerived l F W ⥤
        DerivedCategory (scalarReductionSource l F W))
      (κ : roosF ⋙ DerivedCategory.Q ≅ DerivedCategory.Q ⋙ H)
      (ρ : H ≅ coefficientConstantTowerLimit l F W)
      (adj : (Functor.const ℕᵒᵖ : scalarReductionSource l F W ⥤
        ℕᵒᵖ ⥤ scalarReductionSource l F W).mapDerivedCategory ⊣
          coefficientConstantTowerLimit l F W),
      (κ.hom ≫ Functor.whiskerLeft DerivedCategory.Q ρ.hom = D.roos.hom) ∧
      (∀ (X I : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l F W) ℤ)
        (q : X ⟶ I) [QuasiIso q] [I.IsKInjective]
        (_hI : ∀ p : ℤ, Injective (I.X p)),
        QuasiIso (roosι I) ∧
        (∀ p : ℤ, (roosι I).f (p + 1) ≫ (roosχ I p).hom =
          biprod.lift 0
            ((Pi.lift (fun n : ℕ ↦ limit.π I.asFunctor (op n))).f (p + 1))) ∧
        ∃ (j : DerivedCategory.Q.obj (limit I.asFunctor) ≅
            DerivedCategory.Q.obj (roosF.obj I))
          (d : DerivedCategory.Q.obj (limit I.asFunctor) ≅
            (coefficientConstantTowerLimit l F W).obj (DerivedCategory.Q.obj X)),
          j.hom = DerivedCategory.Q.map (roosι I) ∧
          d.hom ≫ (coefficientConstantTowerLimit l F W).map
              (DerivedCategory.Q.map q) = D.limitUnit.app I ∧
          D.roos.hom.app X = DerivedCategory.Q.map (roosF.map q) ≫ j.inv ≫ d.hom ∧
          (∀ n : ℕ,
            d.hom ≫ (coefficientConstantTowerProjection l F W n).app
                (DerivedCategory.Q.obj X) ≫
              (coefficientConstantTowerEvaluationFactors l F W n).hom.app X ≫
              DerivedCategory.Q.map
                ((HomologicalComplex.complexOfFunctorsToFunctorToComplex.map q).app (op n)) =
              DerivedCategory.Q.map (limit.π I.asFunctor (op n))) ∧
          (Functor.const ℕᵒᵖ : scalarReductionSource l F W ⥤
              ℕᵒᵖ ⥤ scalarReductionSource l F W).mapDerivedCategory.map d.hom ≫
            adj.counit.app (DerivedCategory.Q.obj X) =
            (Functor.const ℕᵒᵖ : scalarReductionSource l F W ⥤
                ℕᵒᵖ ⥤ scalarReductionSource l F W).mapDerivedCategoryFactors.hom.app
                  (limit I.asFunctor) ≫
              DerivedCategory.Q.map
                (((Functor.const ℕᵒᵖ : scalarReductionSource l F W ⥤
                    ℕᵒᵖ ⥤ scalarReductionSource l F W).mapHomologicalComplex (.up ℤ)).map
                      (D.towerLimitComparison.inv.app I) ≫
                  ((constLimAdj :
                    (Functor.const ℕᵒᵖ : scalarReductionSource l F W ⥤
                      ℕᵒᵖ ⥤ scalarReductionSource l F W) ⊣ lim).mapHomologicalComplex
                        (.up ℤ)).counit.app I) ≫ inv (DerivedCategory.Q.map q)) ∧
      (∀ (X : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l F W) ℤ) (n : ℕ),
        D.roos.hom.app X ≫ (coefficientConstantTowerProjection l F W n).app
            (DerivedCategory.Q.obj X) ≫
          (coefficientConstantTowerEvaluationFactors l F W n).hom.app X =
          DerivedCategory.Q.map (roosEval X n)) ∧
      (∀ (C : coefficientSequenceDerived l F W) (n : ℕ),
        (coefficientFiniteAdjunction l F W n).homEquiv _ _
          ((S.reductionEvaluation n).inv.app ((coefficientSequenceLimit l F W).obj C) ≫
            (coefficientSequenceDerivedEvaluation l F W n).map (S.adjunction.counit.app C)) =
          (coefficientSequenceProjection l F W n).app C) ∧
      (∀ (P : CochainComplex (scalarReductionSource l F W) ℤ)
        (hP : P.IsKFlatIndependentCoefficients)
        (hflat : ∀ p : ℤ, (P.X p).IsFlatOnSite),
        (∀ (p : ℤ) (n : ℕ) (V : W.ProEtᵒᵖ) (z : (P.X p).val.obj V),
          (((M.augmentation l F W P ≫
              limit.π ((CompletionUnit.tower l F W).obj ((M.quotient l F W).obj P)).asFunctor
                (op n)).f p ≫
              (eqToIso (coefficientSequenceRestriction_evaluation l F W n)).hom.app
                (((M.quotient l F W).obj P).X p) ≫
              (scalarReductionRestriction l F W n).map
                ((M.evaluation n).hom.app (P.X p))).val.app V) z =
            unrestrictedIntegralTensorSection l F W n (P.X p) V 1 z) ∧
        (∀ p : ℤ,
          (M.coneAugmentation l F W P).f (p + 1) ≫
              (roosχ ((CompletionUnit.tower l F W).obj ((M.quotient l F W).obj P)) p).hom =
            biprod.lift 0
              ((Pi.lift (fun n : ℕ ↦ M.augmentation l F W P ≫
                limit.π ((CompletionUnit.tower l F W).obj
                  ((M.quotient l F W).obj P)).asFunctor (op n))).f (p + 1))) ∧
        (∀ (K : DerivedCategory (scalarReductionSource l F W))
          (p : DerivedCategory.Q.obj P ≅ K),
          S.adjunction.unit.app K = p.inv ≫
            DerivedCategory.Q.map (M.coneAugmentation l F W P) ≫
            (D.completionComparison l F W P hP hflat).hom ≫
            (coefficientSequenceLimit l F W).map (S.reduction.map p.hom))) := by
  obtain ⟨S, coherence, M, D, hunit, _⟩ :=
    CompletionUnit.completionUnitStrictQuotientModel l F W
  obtain ⟨adj, hc⟩ := limit_adjunction l F W D
  refine ⟨S, coherence, M, D, coefficientConstantTowerLimit l F W,
    D.roos, Iso.refl _, adj, ?_, ?_, roos_projection l F W D,
    S.counit_projection, ?_⟩
  · simp
  · intro X I q _ _ _
    have := limitUnit_isIso l F W D I
    have hι := inclusion_quasiIso l F W D I
    have := hι
    let j := asIso (DerivedCategory.Q.map (roosι I))
    let d := asIso (D.limitUnit.app I) ≪≫
      (coefficientConstantTowerLimit l F W).mapIso (asIso (DerivedCategory.Q.map q)).symm
    have hd : d.hom ≫ (coefficientConstantTowerLimit l F W).map
        (DerivedCategory.Q.map q) = D.limitUnit.app I := by
      simp [d]
    refine ⟨hι, roosι_χ I, j, d, rfl, hd, ?_, ?_, ?_⟩
    · apply (cancel_mono ((coefficientConstantTowerLimit l F W).map
        (DerivedCategory.Q.map q))).1
      rw [Category.assoc, Category.assoc, hd]
      rw [← D.roos_normalization I]
      simp only [j, asIso_inv, IsIso.inv_hom_id_assoc]
      exact (D.roos.hom.naturality q).symm
    · intro n
      have hp := (coefficientConstantTowerProjection l F W n).naturality
        (DerivedCategory.Q.map q)
      have hv := (coefficientConstantTowerEvaluationFactors l F W n).hom.naturality q
      dsimp only [Functor.comp_map] at hv
      change d.hom ≫ (coefficientConstantTowerProjection l F W n).app
        (DerivedCategory.Q.obj X) ≫
        (coefficientConstantTowerEvaluationFactors l F W n).hom.app X ≫
        DerivedCategory.Q.map
          ((((evaluation ℕᵒᵖ (scalarReductionSource l F W)).obj (op n)).mapHomologicalComplex
            (.up ℤ)).map q) = _
      rw [← hv]
      erw [← reassoc_of% hp, ← Category.assoc, hd]
      exact limitUnit_projection l F W D I n
    · apply (cancel_mono (DerivedCategory.Q.map q)).1
      simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
      have hn := adj.counit.naturality (DerivedCategory.Q.map q)
      dsimp only [Functor.comp_map, Functor.id_map] at hn
      rw [← hn, ← Functor.map_comp_assoc, hd]
      exact hc I
  · intro P hP hflat
    exact ⟨(hunit P hP hflat).1, (hunit P hP hflat).2.1,
      (hunit P hP hflat).2.2.1⟩

end WeilConjectures
