/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NX
-/
module

public import Sheaf.Paper.BoundedConstructibleComplete
public import Sheaf.Paper.CompletedBaseChangeMap
import Sheaf.Paper.CompletedTowerCompatibility
import Sheaf.Paper.PbcIntrinsicTowerComplete

/-! # Completed proper base change with compatible retained origins

Source: Stacks 09C9; blueprint order 1354
(blueprint: thm-weil-pbc-complete-proetale).
The published actual-coefficient exchange is used without any auxiliary presentation.
Neither constructibility nor a common cohomological bound is assumed.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme

section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory.Limits

private theorem originScalars_comp
    {A : Type (u + 1)} [CommRing A] (T : Scheme.{u})
    (d : AdicCoefficientDatum A) (n : ℕ) :
    etaleOriginScalars T (A ⧸ d.ideal ^ (n + 1)) ≫
        ((adicLisseForget T).map
          (finiteOriginConstantIso T (A ⧸ d.ideal ^ (n + 1))).hom).hom =
      pbcFunctionScalars T d n := by
  let Λ := A ⧸ d.ideal ^ (n + 1)
  let : TopologicalSpace Λ := ⊥
  let : DiscreteTopology Λ := ⟨rfl⟩
  let c := AdicCoefficients.constants T Λ
  let η := toSheafify (ProEt.topology T) (AdicCoefficients.functionPresheaf T Λ)
  let F := forget₂ CommRingCat.{u + 1} RingCat.{u + 1}
  have hn := toSheafify_naturality (ProEt.topology T) c
  have hη := (AdicCoefficients.finiteRingComparison_exists T Λ).choose_spec.1.2
  change Functor.whiskerRight η F ≫
    (AdicCoefficients.finiteRingComparison T Λ).hom.hom =
      AdicCoefficients.finiteRingUnit T Λ at hη
  have h : Functor.whiskerRight c F ≫ Functor.whiskerRight η F ≫
      (AdicCoefficients.finiteRingComparison T Λ).hom.hom =
        ProEtale.finiteCoefficientScalarMap T Λ := by
    rw [hη]
    rfl
  apply (cancel_mono (AdicCoefficients.finiteRingComparison T Λ).hom.hom).1
  change (etaleOriginScalars T Λ ≫
    ((adicLisseForget T).map (finiteOriginConstantIso T Λ).hom).hom) ≫
      (AdicCoefficients.finiteRingComparison T Λ).hom.hom = _
  have hc : etaleOriginScalars T Λ ≫
      ((adicLisseForget T).map (finiteOriginConstantIso T Λ).hom).hom =
        Functor.whiskerRight c F ≫ Functor.whiskerRight η F := by
    exact congrArg (fun z ↦ Functor.whiskerRight z F) hn.symm
  rw [hc, Category.assoc, h]
  change ProEtale.finiteCoefficientScalarMap T Λ =
    ProEtale.finiteCoefficientScalarMap T Λ ≫
      ((AdicCoefficients.finiteRingComparison T Λ).inv ≫
        (AdicCoefficients.finiteRingComparison T Λ).hom).hom
  rw [Iso.inv_hom_id]
  exact (Category.comp_id _).symm

private def originRealizationIso
    {A : Type (u + 1)} [CommRing A] (T : Scheme.{u})
    (d : AdicCoefficientDatum A) (n : ℕ) :
    etaleOriginRealization T (A ⧸ d.ideal ^ (n + 1)) ≅
      pbcFunctionRealization T d n ⋙
        proEtaleRingRestrictScalars
          (finiteOriginConstantIso T (A ⧸ d.ideal ^ (n + 1))).hom := by
  let Λ := A ⧸ d.ideal ^ (n + 1)
  have h := pbcAssociatedRestriction_exists T Λ Λ
    ((adicLisseForget T).obj (etaleOriginRing T Λ))
    ((adicLisseForget T).obj (finiteOriginFunctionRing T Λ))
    (etaleOriginScalars T Λ) (pbcFunctionScalars T d n)
    (RingHom.id Λ) ((adicLisseForget T).map (finiteOriginConstantIso T Λ).hom)
    (by simpa using originScalars_comp T d n)
  exact h.exists.choose

private theorem ringedOrigins
    {A : Type (u + 1)} [CommRing A] (T : Scheme.{u}) (d : AdicCoefficientDatum A)
    (K : PbcCompletedDerived T d) (h : PbcHasCompatibleEtaleOrigins T d K) :
    Nonempty (∀ n : ℕ, FiniteEtaleOriginWitness T (A ⧸ d.ideal ^ (n + 1))
      ((d.reduction T n).obj K)) := by
  obtain ⟨P, e, _⟩ := h
  refine ⟨fun n ↦ ?_⟩
  letI : (pbcFunctionRealization T d n).Additive := pbcFunctionRealization_additive T d n
  letI : PreservesFiniteLimits (pbcFunctionRealization T d n) :=
    pbcFunctionRealization_limits T d n
  letI : PreservesFiniteColimits (pbcFunctionRealization T d n) :=
    pbcFunctionRealization_colimits T d n
  let a := (finiteOriginConstantIso T (A ⧸ d.ideal ^ (n + 1))).hom
  letI : (proEtaleRingRestrictScalars a).Additive := pbcRestrict_additive a
  letI : PreservesFiniteLimits (proEtaleRingRestrictScalars a) :=
    (proEtaleRingRestrictScalars_properties a).1
  letI : PreservesFiniteColimits (proEtaleRingRestrictScalars a) :=
    (proEtaleRingRestrictScalars_properties a).2.1
  let R := proEtaleRingRestrictScalars a
  have i₁ := (Functor.mapDerivedCategoryCompIso
      (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} (A ⧸ d.ideal ^ (n + 1))) T)
      (etaleOriginRealization T (A ⧸ d.ideal ^ (n + 1)))).app (P.origin n).L.obj
  have i₂ := (etaleOriginRealization T (A ⧸ d.ideal ^ (n + 1))).mapDerivedCategory.mapIso
      (P.alpha n)
  have i₃ := (Functor.mapDerivedCategoryNatIso (originRealizationIso T d n)).app (P.K n)
  have i₄ := (Functor.mapDerivedCategoryCompIso (pbcFunctionRealization T d n) R).app
    (P.K n)
  have i₅ := (finiteOriginToConstant T (A ⧸ d.ideal ^ (n + 1))).mapIso (e n)
  refine ⟨(P.origin n).L, ?_⟩
  exact i₁ ≪≫ i₂ ≪≫ i₃ ≪≫ i₄ ≪≫ i₅

private theorem completedExchange_isIso_of_towerComplete
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    {X' X Y' Y : Scheme.{u}}
    {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (sq : ChosenCartesianSquare g' f' f g) [IsProper f]
    (K : d.derived X) (hK : d.TowerComplete X K)
    (W : ∀ n : ℕ, FiniteEtaleOriginWitness X (A ⧸ d.ideal ^ (n + 1))
      ((d.reduction X n).obj K)) : IsIso (d.completedExchange sq K) := by
  have he (n : ℕ) : IsIso
      ((reductionTowerDerivedEvaluation Y'
        (reductionModuleRing Y' (d.completedRing Y')) n).map (d.towerV' sq K)) := by
    obtain ⟨α, _, _, _, hv⟩ := (d.fourTowers_compatibility sq K hK W n).1
    have : IsIso
        ((reductionTowerDerivedEvaluation Y'
          (reductionModuleRing Y' (d.completedRing Y')) n).map (d.towerV' sq K) ≫
            (α 3).hom) := by
      rw [hv]
      infer_instance
    exact IsIso.of_isIso_comp_right _ (α 3).hom
  have : IsIso (d.towerV' sq K) := by
    rw [DerivedCategory.isIso_iff]
    intro i
    have (n : ℕᵒᵖ) : IsIso
        (((DerivedCategory.homologyFunctor (d.towers Y') i).map
          (d.towerV' sq K)).app n) := by
      let E := reductionTowerEvaluation Y'
        (reductionModuleRing Y' (d.completedRing Y')) n.unop
      have : IsIso ((E.mapDerivedCategory ⋙ DerivedCategory.homologyFunctor _ i).map
          (d.towerV' sq K)) := by
        change IsIso ((DerivedCategory.homologyFunctor _ i).map
          ((reductionTowerDerivedEvaluation Y'
            (reductionModuleRing Y' (d.completedRing Y')) n.unop).map (d.towerV' sq K)))
        have := he n.unop
        infer_instance
      exact (NatIso.isIso_map_iff (E.mapDerivedCategoryHomologyFunctorIso i)
        (d.towerV' sq K)).2 inferInstance
    exact NatIso.isIso_of_isIso_app _
  unfold AdicCoefficientDatum.completedExchange
  infer_instance

end

/-- The specified completed exchange is invertible for an intrinsically complete
object with compatible retained bounded-below etale origins. The strict reduction
tower records canonical computations; no constructibility condition is imposed.
Source: Stacks 09C9 (blueprint: thm-weil-pbc-complete-proetale).
Proof: intrinsic completeness identifies K with the derived limit of its canonical
quotient tower. The perfect projection mate identifies reduction of Rf K with strict
Rf of the reductions. At each positive level the retained bounded-below etale origin
allows finite-coefficient proper base change. Compatibility identifies its maps with
the evaluated canonical tower exchange. Evaluation detects isomorphisms of strict
derived towers because cohomology is pointwise. Apply the actual Rlim functor to this
isomorphism and compose with the specified projection and direct-image/limit
isomorphisms. The resulting ordered composite is exactly d.completedExchange sq K in the
actual completed-ring category. -/
theorem completeProetale_isIso
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    {X' X Y' Y : Scheme.{u}}
    {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (sq : ChosenCartesianSquare g' f' f g) [IsProper f]
    (K : PbcCompletedDerived X d)
    (_hK : PbcIsIntrinsicallyComplete X d K)
    (_origins : PbcHasCompatibleEtaleOrigins X d K) :
    IsIso (d.completedExchange sq K) := by
  have hTower : d.TowerComplete X K :=
    pbcIntrinsicComplete_towerComplete d X K _hK
  obtain ⟨W⟩ := ringedOrigins X d K _origins
  exact completedExchange_isIso_of_towerComplete d sq K hTower W

end AlgebraicGeometry.Scheme
