/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Sheaf.SixFunctors.OpenQuotientKoszulModels
import all Sheaf.CategoryTheory.ExactEquivalenceDerivedSquares
import Mathlib.CategoryTheory.Limits.Preserves.Limits
import all Mathlib.CategoryTheory.Limits.HasLimits
import all Mathlib.CategoryTheory.Equivalence
import Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback

/-! # The augmented quotient tower under the canonical DVR coefficient comparison 

Source: Stacks Tags 0941, 099B and 0A0E; canonical coefficient transport.
(blueprint: lem-sf-open-dvr-limit-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Canonical projection-normalized ordinary and derived limit transport.
Source: Stacks Tags 05RR and 0941
(blueprint: lem-sf-open-dvr-limit-comparison). -/
structure OpenDvrLimitComparison
    {d : AdicCoefficientDatum (Padic.coefficientExtensionIntegers l E)} {T : Scheme.{u}}
    (C : OpenDvrCoefficientModel l E d T) where
  /-- The total-limit comparison is the canonical one under the coefficient equivalence. -/
  rlim : C.towers ⋙ reconstructionRlim T d ≅
    coefficientConstantTowerLimit.{u, u} l E T ⋙ C.derived.functor
  /-- The total-limit comparison extends the ordinary projection-normalized comparison. -/
  limit_model : ∀ I : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource.{u, u} l E T) ℤ,
    ∃ σ : ((reconstructionLimit T d).mapHomologicalComplex (.up ℤ)).obj
          (C.towerComplexes.obj I) ≅
        C.complexes.obj
          (((lim : (ℕᵒᵖ ⥤ scalarReductionSource.{u, u} l E T) ⥤ _).mapHomologicalComplex
            (.up ℤ)).obj I),
      (∀ (i : ℤ) (n : ℕ),
        σ.hom.f i ≫ C.modules.functor.map (limit.π (I.X i) (op n)) =
          limit.π ((C.towerComplexes.obj I).X i) (op n)) ∧
      C.derived.functor.map
          (derivedLimitComplexComparison
            (lim : (ℕᵒᵖ ⥤ scalarReductionSource.{u, u} l E T) ⥤ _)
            (coefficientConstantTowerLimit.{u, u} l E T)
            (lim : (ℕᵒᵖ ⥤ scalarReductionSource.{u, u} l E T) ⥤ _).rightDerivedFunctorUnit I) =
        C.modules.functor.mapDerivedCategoryFactors.hom.app
            (((lim : (ℕᵒᵖ ⥤ scalarReductionSource.{u, u} l E T) ⥤ _).mapHomologicalComplex
            (.up ℤ)).obj I) ≫
          DerivedCategory.Q.map σ.inv ≫
          reconstructionRlimComparison T d (C.towerComplexes.obj I) ≫
          (reconstructionRlim T d).map
            (C.ordinaryTowers.mapDerivedCategoryFactors.inv.app I) ≫
          rlim.hom.app (DerivedCategory.Q.obj I)

private theorem dvrRlimComparison_exists
    (d : AdicCoefficientDatum (Padic.coefficientExtensionIntegers l E))
    (T : Scheme.{u}) (C : OpenDvrCoefficientModel l E d T) :
    ∃ e : C.towers ⋙ reconstructionRlim T d ≅
        coefficientConstantTowerLimit.{u, u} l E T ⋙ C.derived.functor,
      ∀ I : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource.{u, u} l E T) ℤ,
        C.derived.functor.map
          (derivedLimitComplexComparison
            (lim : (ℕᵒᵖ ⥤ scalarReductionSource.{u, u} l E T) ⥤ _)
            (coefficientConstantTowerLimit.{u, u} l E T)
            (lim : (ℕᵒᵖ ⥤ scalarReductionSource.{u, u} l E T) ⥤ _).rightDerivedFunctorUnit I) ≫
          e.inv.app (DerivedCategory.Q.obj I) ≫
          (reconstructionRlim T d).map
            (C.ordinaryTowers.mapDerivedCategoryFactors.hom.app I) =
        C.modules.functor.mapDerivedCategoryFactors.hom.app
            (((lim : (ℕᵒᵖ ⥤ scalarReductionSource.{u, u} l E T) ⥤ _).mapHomologicalComplex
              (.up ℤ)).obj I) ≫
          DerivedCategory.Q.map
            ((NatIso.mapHomologicalComplex
              (preservesLimitNatIso C.modules.functor) (.up ℤ)).hom.app I) ≫
          reconstructionRlimComparison T d (C.towerComplexes.obj I) := by
  let E' := C.modules.congrRight (E := ℕᵒᵖ)
  have : E'.functor.Additive := by
    change C.ordinaryTowers.Additive
    infer_instance
  let L : (ℕᵒᵖ ⥤ scalarReductionSource.{u, u} l E T) ⥤ _ := lim
  let L' : CompletedAdicTowers T d ⥤ _ := reconstructionLimit T d
  let η : L.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ L.rightDerivedFunctor :=
    { app := L.rightDerivedFunctorUnitQ
      naturality := fun {_ _} f ↦ L.rightDerivedFunctorUnitQ_naturality f }
  let η' : L'.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ L'.rightDerivedFunctor :=
    { app := L'.rightDerivedFunctorUnitQ
      naturality := fun {_ _} f ↦ L'.rightDerivedFunctorUnitQ_naturality f }
  have hL := CategoryTheory.derives L
  have : L.rightDerivedFunctor.IsRightDerivedFunctor η
      (HomologicalComplex.quasiIso _ (.up ℤ)) := by
    apply hL.isRightDerivedFunctor_of_isIso
    intro I
    have := I.property
    change IsIso (L.rightDerivedFunctorUnitQ I.obj)
    rw [Functor.rightDerivedFunctorUnitQ_eq]
    infer_instance
  have hL' := CategoryTheory.derives L'
  have : L'.rightDerivedFunctor.IsRightDerivedFunctor η'
      (HomologicalComplex.quasiIso _ (.up ℤ)) := by
    apply hL'.isRightDerivedFunctor_of_isIso
    intro I
    have := I.property
    change IsIso (L'.rightDerivedFunctorUnitQ I.obj)
    rw [Functor.rightDerivedFunctorUnitQ_eq]
    infer_instance
  have := Functor.IsRightDerivedFunctor.isLeftKanExtension L.rightDerivedFunctor η
    (HomologicalComplex.quasiIso _ (.up ℤ))
  have := Functor.IsRightDerivedFunctor.isLeftKanExtension L'.rightDerivedFunctor η'
    (HomologicalComplex.quasiIso _ (.up ℤ))
  obtain ⟨φ, hφ⟩ := CategoryTheory.rightDerivedSquare E' C.modules L L'
    L.rightDerivedFunctor L'.rightDerivedFunctor η η'
    (preservesLimitNatIso C.modules.functor)
  refine ⟨φ.symm, ?_⟩
  intro I
  simpa [η, η', E', L, L', coefficientConstantTowerLimit, reconstructionRlim,
    CategoryTheory.Equivalence.congrRight,
    OpenDvrCoefficientModel.towers, OpenDvrCoefficientModel.ordinaryTowers,
    OpenDvrCoefficientModel.towerComplexes, OpenDvrCoefficientModel.derived,
    Functor.rightDerivedFunctorUnitQ,
    derivedLimitComplexComparison, reconstructionRlimComparison,
    Functor.mapHomotopyCategoryFactors, Quotient.lift.isLift_inv,
    Functor.map_id, Category.id_comp, Category.comp_id, Category.assoc]
    using hφ I

private theorem dvrRlimModel_exists
    (d : AdicCoefficientDatum (Padic.coefficientExtensionIntegers l E))
    (T : Scheme.{u}) (C : OpenDvrCoefficientModel l E d T) :
    ∃ rlim : C.towers ⋙ reconstructionRlim T d ≅
        coefficientConstantTowerLimit.{u, u} l E T ⋙ C.derived.functor,
      ∀ I : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource.{u, u} l E T) ℤ,
    ∃ σ : ((reconstructionLimit T d).mapHomologicalComplex (.up ℤ)).obj
          (C.towerComplexes.obj I) ≅
        C.complexes.obj
          (((lim : (ℕᵒᵖ ⥤ scalarReductionSource.{u, u} l E T) ⥤ _).mapHomologicalComplex
            (.up ℤ)).obj I),
      (∀ (i : ℤ) (n : ℕ),
        σ.hom.f i ≫ C.modules.functor.map (limit.π (I.X i) (op n)) =
          limit.π ((C.towerComplexes.obj I).X i) (op n)) ∧
      C.derived.functor.map
          (derivedLimitComplexComparison
            (lim : (ℕᵒᵖ ⥤ scalarReductionSource.{u, u} l E T) ⥤ _)
            (coefficientConstantTowerLimit.{u, u} l E T)
            (lim : (ℕᵒᵖ ⥤ scalarReductionSource.{u, u} l E T) ⥤ _).rightDerivedFunctorUnit I) =
        C.modules.functor.mapDerivedCategoryFactors.hom.app
            (((lim : (ℕᵒᵖ ⥤ scalarReductionSource.{u, u} l E T) ⥤ _).mapHomologicalComplex
            (.up ℤ)).obj I) ≫
          DerivedCategory.Q.map σ.inv ≫
          reconstructionRlimComparison T d (C.towerComplexes.obj I) ≫
          (reconstructionRlim T d).map
            (C.ordinaryTowers.mapDerivedCategoryFactors.inv.app I) ≫
          rlim.hom.app (DerivedCategory.Q.obj I) := by
  obtain ⟨e, he⟩ := dvrRlimComparison_exists l E d T C
  refine ⟨e, ?_⟩
  intro I
  let s := preservesLimitNatIso C.modules.functor (J := ℕᵒᵖ)
  let σ : ((reconstructionLimit T d).mapHomologicalComplex (.up ℤ)).obj
      (C.towerComplexes.obj I) ≅ C.complexes.obj
        (((lim : (ℕᵒᵖ ⥤ scalarReductionSource.{u, u} l E T) ⥤ _).mapHomologicalComplex
          (.up ℤ)).obj I) :=
    (NatIso.mapHomologicalComplex s (.up ℤ)).symm.app I
  refine ⟨σ, ?_, ?_⟩
  · intro i n
    change (preservesLimitIso C.modules.functor (I.X i)).inv ≫
      C.modules.functor.map (limit.π (I.X i) (op n)) = _
    exact preservesLimitIso_inv_π C.modules.functor (I.X i) (op n)
  · have hσ : σ.inv = (NatIso.mapHomologicalComplex s (.up ℤ)).hom.app I := rfl
    rw [hσ]
    let z := (reconstructionRlim T d).mapIso (C.ordinaryTowers.mapDerivedCategoryFactors.app I)
    let w := e.symm.app (DerivedCategory.Q.obj I) ≪≫ z
    have h := (he I)
    have h' : _ = _ := (Iso.eq_comp_inv w).2 (by
      change (_ ≫ e.inv.app _ ≫ z.hom) = _
      exact h)
    simpa only [w, z, Iso.trans_inv, Iso.symm_inv, Functor.mapIso_inv,
      Iso.app_inv, Iso.app_hom, Category.assoc] using h'

/-- Scalar restriction along the canonical coefficient isomorphism transports limits.
Source: Stacks Tags 05RR and 0941
(blueprint: lem-sf-open-dvr-limit-comparison).

Proof: scalar restriction is an exact equivalence. Its ordinary limit comparison is
preservesLimitNatIso, hence is fixed by all projections. Apply rightDerivedSquare to
the coefficient equivalence and its pointwise tower equivalence, with the universal
right-derived pairs. Its factorization equation is the required equation on complexes.
The localization comparison through the homotopy category is the recorded
reconstructionRlimComparison. Compose the factorization equation with the inverse
tower-localization isomorphism and the derived comparison to obtain limit_model. -/
theorem openDvrLimitComparison
    (d : AdicCoefficientDatum (Padic.coefficientExtensionIntegers l E))
    (T : Scheme.{u}) (C : OpenDvrCoefficientModel l E d T) :
    Nonempty (OpenDvrLimitComparison l E C) := by
  obtain ⟨e, he⟩ := dvrRlimModel_exists l E d T C
  exact ⟨⟨e, he⟩⟩

end WeilConjectures
