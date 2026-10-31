/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CoefSupportPointSectionsData
import all WeilConjectures.AlgebraicGeometry.PurSequenceConstantRingFactorization
import WeilConjectures.CategoryTheory.CoefficientRestrictionSectionEvaluationAcyclic
import all WeilConjectures.CategoryTheory.TowerRightDerivedEvaluation

/-! # Existence of unit-normalized native point sections

Source: Stacks 0D6E and 0941
(blueprint: lem-coef-support-point-sections-comparison-existence).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local irreducible] CategoryTheory.Functor.leftAdjoint
  CategoryTheory.Functor.mapDerivedCategory CategoryTheory.Functor.rightDerivedFunctor
  HasDerivedCategory.standard
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.SemilinearSections.abelianSheafify
  WeilConjectures.SemilinearSections.locallyBijective
  WeilConjectures.SemilinearSections.moduleAbelian WeilConjectures.SemilinearSections.hasDerived
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.CoefSupportOpenTensor

private instance (priority := 10000) siteSmall (W : Scheme.{u}) :
    EssentiallySmall.{u+1} W.ProEt := essentiallySmallSelf.{0, u, u+1} _

private instance (priority := 10000) siteAbSheafify (W : Scheme.{u}) :
    HasSheafify (ProEt.topology W) AddCommGrpCat.{u+1} :=
  integralCoefficientAbSheafify.{u, u} W

private instance (priority := 10000) siteAbLocallyBijective (W : Scheme.{u}) :
    (ProEt.topology W).WEqualsLocallyBijective AddCommGrpCat.{u+1} :=
  integralCoefficientAbLocallyBijective.{u, u} W

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

set_option maxHeartbeats 2000000 in
-- Transport through the explicit sequence equivalence needs extra definitional equality checks.
/-- Sections of a completed-scalar resolution of a K-injective quotient system
are a quasi-isomorphism of integral-module towers.
Source: Stacks 0D6E on sequence-site slices.
(blueprint: lem-coef-support-point-sections-comparison-existence).
Proof: transport the resolution through the inverse constant-sequence equivalence,
apply scalar-restriction acyclicity at every `(n, id_W)`, cancel the mapped unit
isomorphism, and reflect quasi-isomorphisms through forgetting integral modules. -/
private theorem sectionsRestriction_quasiIso (W : Scheme.{u})
    (I : CochainComplex (coefficientSequenceModules.{u, u} l E W) ℤ)
    [I.IsKInjective]
    (T : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource.{u, u} l E W) ℤ)
    [T.IsKInjective]
    (j : ((coefficientSequenceRestriction.{u, u} l E W).mapHomologicalComplex
      (.up ℤ)).obj I ⟶ T) [QuasiIso j] :
    QuasiIso (((ordinarySections l E W).mapHomologicalComplex (.up ℤ)).map j) := by
  let e := completedTowers.{u, u} l E W
  let r := (firstFactor.{u, u} l E W).modules
  have he : e.functor.Additive :=
    (CategoryTheory.ConstantCompletion.independentConstantSequenceEquivalence_additive.{u+1, u, u}
      (completedIntegralCommRingSheafUnrestricted l E W)).1
  let U := r ⋙ e.functor
  have hU : U = coefficientSequenceRestriction.{u, u} l E W :=
    firstFactor_restriction.{u, u} l E W
  let P (V : coefficientSequenceModules.{u, u} l E W ⥤
      (ℕᵒᵖ ⥤ scalarReductionSource.{u, u} l E W)) (hV : V.Additive) : Prop :=
    have := hV
    ∀ (j : (V.mapHomologicalComplex (.up ℤ)).obj I ⟶ T) [QuasiIso j],
      QuasiIso (((ordinarySections l E W).mapHomologicalComplex (.up ℤ)).map j)
  have hP : ∀ hV : U.Additive, P U hV := by
    intro hV j hj
    have : e.inverse.Additive := e.inverse_additive
    let K := (e.inverse.mapHomologicalComplex (.up ℤ)).obj T
    have : CochainComplex.IsKInjective K := inferInstance
    let ec := NatIso.mapHomologicalComplex e.unitIso (.up ℤ)
    let j' : (r.mapHomologicalComplex (.up ℤ)).obj I ⟶ K :=
      ec.hom.app ((r.mapHomologicalComplex (.up ℤ)).obj I) ≫
        (e.inverse.mapHomologicalComplex (.up ℤ)).map j
    have : QuasiIso j' := by
      dsimp only [j']
      infer_instance
    rw [HomologicalComplex.quasiIso_iff_evaluation]
    intro n
    let F := forget₂ (ModuleCat.{u+1} (coefTraceRing l E)) AddCommGrpCat.{u+1}
    let : PreservesColimitsOfSize.{0, 0} F :=
      ModuleCat.forget₂PreservesColimitsOfSize.{u+1, u+1, 0, 0} (R := coefTraceRing l E)
    let : PreservesFiniteColimits F := PreservesColimitsOfSize.preservesFiniteColimits F
    apply (HomologicalComplex.quasiIso_map_iff_of_preservesHomology _ F).mp
    let A := SheafOfModules.toSheaf (purSequenceConstantRing l E W) ⋙
      sheafToPresheaf (coefficientSequenceTopology (ProEt.topology W)) AddCommGrpCat.{u+1} ⋙
      (CategoryTheory.evaluation _ _).obj (op (n.unop, ProEt.mk (𝟙 W)))
    have hq : QuasiIso ((A.mapHomologicalComplex (.up ℤ)).map j') :=
      SheafOfModules.coefficientRestrictionSectionsEvaluation_quasiIso.{u+1, u, u}
        (purSequenceConstantRing.{u, u} l E W) (purSequenceQuotientRing.{u, u} l E W)
        (fun V x y ↦ completedIntegralCoefficient_mul_commUnrestricted.{u, u}
          l E W (op V.unop.2) x y)
        (fun V x y ↦ mul_comm
          (show (coefficientSequenceCommRingSheaf.{u, u} l E W).obj.obj V from x) y)
        (quotientScalarMap.{u, u} l E W) I K j' (n.unop, ProEt.mk (𝟙 W))
    have hq' : QuasiIso ((A.mapHomologicalComplex (.up ℤ)).map
        ((e.inverse.mapHomologicalComplex (.up ℤ)).map j)) := by
      dsimp only [j'] at hq
      rw [Functor.map_comp] at hq
      exact quasiIso_of_comp_left
        ((A.mapHomologicalComplex (.up ℤ)).map
          (ec.hom.app ((r.mapHomologicalComplex (.up ℤ)).obj I)))
        ((A.mapHomologicalComplex (.up ℤ)).map
          ((e.inverse.mapHomologicalComplex (.up ℤ)).map j))
    let H := ordinarySections l E W ⋙
      (CategoryTheory.evaluation ℕᵒᵖ (ModuleCat.{u+1} (coefTraceRing l E))).obj n ⋙ F
    let δ : e.inverse ⋙ A ≅ H :=
      NatIso.ofComponents (fun _ ↦ Iso.refl _) (by intros; rfl)
    exact (quasiIso_iff_of_arrow_mk_iso _ _
      (Arrow.isoOfNatIso (NatIso.mapHomologicalComplex δ (.up ℤ)) (Arrow.mk j))).mp hq'
  exact (Eq.mp (congrArg (fun V ↦ ∀ hV : V.Additive, P V hV) hU) hP)
    (coefficientSequenceRestriction_additive l E W) j

/-- Exact scalar restriction commutes with the native total derived point sections,
with the prescribed derived-unit equation.
Source: Stacks, sites-cohomology.tex, lemma-derived-pushforward-composition
(Tag 0D6E); support-open-tensor proof step 4.
(blueprint: lem-coef-support-point-sections-comparison-existence).

Proof: the ordinary quotient point functor is exact coefficient restriction
followed by ordinary completed-ring tower sections, including the constant R
module action. Present both as direct image along the ringed point square.
Apply derived direct-image composition to its two factorizations. Exact scalar
restriction is computed on every complex. Its inverse-image left adjoint is
computed on flat-term K-flat complexes, and the derived pullback composition
comparison identifies the two left adjoints. Uniqueness of right adjoints gives
the desired isomorphism of total derived functors; its construction from the
universal derived units gives sectionsComparisonUnit on every complex. The
comparison keeps the constant R action and no inverse limit is taken. This
argument does not require restriction to preserve K-injective complexes. -/
theorem sectionsComparison_exists (W : Scheme.{u}) :
    ∃ comparison : quotientSections l E W ≅
        coefficientSequenceDerivedRestriction.{u, u} l E W ⋙ integralSections l E W,
      sectionsComparisonUnit l E W comparison := by
  -- Use the sectionwise acyclicity consequence of the ringed-topos argument above.
  -- The existing descent construction retains the unit equation on every complex.
  let P : coefficientSequenceModules.{u, u} l E W ⥤
      (ℕᵒᵖ ⥤ scalarReductionSource.{u, u} l E W) :=
    coefficientSequenceRestriction.{u, u} l E W
  let F : coefficientSequenceModules.{u, u} l E W ⥤
      (ℕᵒᵖ ⥤ ModuleCat.{u+1} (coefTraceRing l E)) := ordinaryQuotientSections l E W
  let G : (ℕᵒᵖ ⥤ scalarReductionSource.{u, u} l E W) ⥤
      (ℕᵒᵖ ⥤ ModuleCat.{u+1} (coefTraceRing l E)) := ordinarySections l E W
  let a : F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ F.rightDerivedFunctor :=
    { app := F.rightDerivedFunctorUnitQ
      naturality := fun {_ _} f ↦ F.rightDerivedFunctorUnitQ_naturality f }
  let g : G.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ G.rightDerivedFunctor :=
    { app := G.rightDerivedFunctorUnitQ
      naturality := fun {_ _} f ↦ G.rightDerivedFunctorUnitQ_naturality f }
  let b : F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ P.mapDerivedCategory ⋙ G.rightDerivedFunctor :=
    Functor.whiskerLeft (P.mapHomologicalComplex (.up ℤ)) g ≫
      Functor.whiskerRight P.mapDerivedCategoryFactors.inv G.rightDerivedFunctor
  have computes (I : CochainComplex (coefficientSequenceModules.{u, u} l E W) ℤ)
      (hI : I.IsKInjective) :
      IsIso (G.rightDerivedFunctorUnitQ ((P.mapHomologicalComplex (.up ℤ)).obj I)) := by
    have := hI
    obtain ⟨T, hT, j, _, hj⟩ := Abelian.HasKInjectiveResolutions.exists_isKInjective
      ((P.mapHomologicalComplex (.up ℤ)).obj I)
    have := hT
    have := hj
    have : QuasiIso ((G.mapHomologicalComplex (.up ℤ)).map j) :=
      sectionsRestriction_quasiIso l E W I T j
    have : IsIso (G.rightDerivedFunctorUnitQ T) := by
      rw [G.rightDerivedFunctorUnitQ_eq]
      infer_instance
    have hi : IsIso (G.rightDerivedFunctorUnitQ
        ((P.mapHomologicalComplex (.up ℤ)).obj I) ≫
          G.rightDerivedFunctor.map (DerivedCategory.Q.map j)) := by
      rw [← G.rightDerivedFunctorUnitQ_naturality j]
      infer_instance
    exact IsIso.of_isIso_comp_right _ (G.rightDerivedFunctor.map (DerivedCategory.Q.map j))
  obtain ⟨comparison, hc⟩ := TowerRightDerivedEvaluation.descend_comparison
    (fun K ↦ by
      obtain ⟨I, hI, a, _, ha⟩ := Abelian.HasKInjectiveResolutions.exists_isKInjective K
      exact ⟨I, a, hI, ha⟩)
    F.rightDerivedFunctor (P.mapDerivedCategory ⋙ G.rightDerivedFunctor)
    (F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q) a b
    (fun I hI ↦ by
      have := hI
      change IsIso (F.rightDerivedFunctorUnitQ I)
      rw [F.rightDerivedFunctorUnitQ_eq]
      infer_instance)
    (fun I hI ↦ by
      have := computes I hI
      change IsIso (G.rightDerivedFunctorUnitQ _ ≫
        G.rightDerivedFunctor.map (P.mapDerivedCategoryFactors.inv.app I))
      infer_instance)
  exact ⟨comparison, hc⟩

end WeilConjectures.CoefSupportOpenTensor
