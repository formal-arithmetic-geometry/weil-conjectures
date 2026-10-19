/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NX
-/
module

public import Sheaf.Paper.BoundedConstructibleComplete
public import Sheaf.Paper.CompletedBaseChangeMap
import Sheaf.Paper.CompletedPullback

/-! # Completed proper base change with compatible retained origins

Source: Stacks 09C9; blueprint order 1354
(blueprint: thm-weil-pbc-complete-proetale).
The published actual-coefficient exchange is used without any auxiliary presentation.
Neither constructibility nor a common cohomological bound is assumed.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme

open CategoryTheory.Limits CategoryTheory.Functor AlgebraicGeometry.ProEtale

section Origins
variable (T : Scheme.{u}) {A : Type (u + 1)} [CommRing A]
variable (d : AdicCoefficientDatum A) (n : ℕ)

private theorem scalar_square :
    etaleOriginScalars T (PbcQuotient d n) ≫
        ((adicLisseForget T).map (finiteOriginConstantIso T (PbcQuotient d n)).hom).hom =
      pbcFunctionScalars T d n := by
  let F := forget₂ CommRingCat.{u + 1} RingCat.{u + 1}
  let Λ := PbcQuotient d n
  let J := ProEt.topology T
  have hc : etaleOriginScalars T Λ ≫
      ((adicLisseForget T).map (finiteOriginConstantIso T Λ).hom).hom =
        Functor.whiskerRight (AdicCoefficients.constants T Λ ≫
          toSheafify J (AdicCoefficients.functionPresheaf T Λ)) F := by
    change Functor.whiskerRight (toSheafify J _) F ≫
      Functor.whiskerRight (sheafifyMap J (AdicCoefficients.constants T Λ)) F = _
    rw [← Functor.whiskerRight_comp, ← toSheafify_naturality]
  apply (cancel_mono (AdicCoefficients.finiteRingComparison T Λ).hom.hom).1
  rw [hc, Functor.whiskerRight_comp, Category.assoc]
  have he : Functor.whiskerRight
      (toSheafify J (AdicCoefficients.functionPresheaf T Λ)) F ≫
        (AdicCoefficients.finiteRingComparison T Λ).hom.hom =
      AdicCoefficients.finiteRingUnit T Λ :=
    (AdicCoefficients.finiteRingComparison_exists T Λ).choose_spec.1.2
  rw [he]
  change _ = finiteCoefficientScalarMap T Λ ≫
    (AdicCoefficients.finiteRingComparison T Λ).inv.hom ≫
      (AdicCoefficients.finiteRingComparison T Λ).hom.hom
  have hi := congrArg (fun k ↦ k.hom)
    (AdicCoefficients.finiteRingComparison T Λ).inv_hom_id
  change (AdicCoefficients.finiteRingComparison T Λ).inv.hom ≫
    (AdicCoefficients.finiteRingComparison T Λ).hom.hom = 𝟙 _ at hi
  rw [hi]
  erw [Category.comp_id]
  rfl

private def fixedRestrictionId (Λ : Type (u + 1)) [CommRing Λ] :
    Sheaf.restrictScalars (ProEt.topology T) (RingHom.id Λ) ≅ 𝟭 _ :=
  NatIso.ofComponents
    (fun M ↦ (fullyFaithfulSheafToPresheaf (ProEt.topology T) _).preimageIso
      (isoWhiskerLeft M.obj (ModuleCat.restrictScalarsId Λ)))
    (fun f ↦ (fullyFaithfulSheafToPresheaf (ProEt.topology T) _).map_injective (by
      ext U x
      rfl))

private def originRealizationIso :
    etaleOriginRealization T (PbcQuotient d n) ≅
      pbcFunctionRealization T d n ⋙
        proEtaleRingRestrictScalars (finiteOriginConstantIso T (PbcQuotient d n)).hom := by
  let Λ := PbcQuotient d n
  let R := (adicLisseForget T).obj (etaleOriginRing T Λ)
  let S := (adicLisseForget T).obj (finiteOriginFunctionRing T Λ)
  let r := (adicLisseForget T).map (finiteOriginConstantIso T Λ).hom
  have h : etaleOriginScalars T Λ ≫ r.hom =
      (Functor.const T.ProEtᵒᵖ).map (RingCat.ofHom (RingHom.id Λ)) ≫
        pbcFunctionScalars T d n := by
    change _ = 𝟙 _ ≫ _
    rw [Category.id_comp]
    exact scalar_square T d n
  let e := (pbcAssociatedRestriction_exists T Λ Λ R S
    (etaleOriginScalars T Λ) (pbcFunctionScalars T d n) (RingHom.id Λ) r h).exists.choose
  exact (Functor.leftUnitor _).symm ≪≫
    isoWhiskerRight (fixedRestrictionId T Λ).symm _ ≪≫ e

private def completeProetale_origins (K : PbcCompletedDerived T d)
    (h : PbcHasCompatibleEtaleOrigins T d K) :
    ∀ n : ℕ, FiniteEtaleOriginWitness T (A ⧸ d.ideal ^ (n + 1))
      ((d.reduction T n).obj K) := by
  let P := h.choose
  let e := h.choose_spec.choose
  intro n
  let Λ := PbcQuotient d n
  let R := proEtaleRingRestrictScalars (finiteOriginConstantIso T Λ).hom
  letI : PreservesFiniteLimits R :=
    (proEtaleRingRestrictScalars_properties (finiteOriginConstantIso T Λ).hom).1
  letI : PreservesFiniteColimits R :=
    (proEtaleRingRestrictScalars_properties (finiteOriginConstantIso T Λ).hom).2.1
  refine ⟨(P.origin n).L, ?_⟩
  exact (Functor.mapDerivedCategoryCompIso
    (comparisonUpperStar (ModuleCat.{u + 1} Λ) T) (etaleOriginRealization T Λ)).app
      (P.origin n).L.obj ≪≫
    (etaleOriginRealization T Λ).mapDerivedCategory.mapIso (P.alpha n) ≪≫
    (Functor.mapDerivedCategoryNatIso (originRealizationIso T d n)).app (P.K n) ≪≫
    (Functor.mapDerivedCategoryCompIso (pbcFunctionRealization T d n) R).app (P.K n) ≪≫
    R.mapDerivedCategory.mapIso (e n)

end Origins

private theorem completeProetale_of_tower
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
  apply completeProetale_of_tower d sq K
    ((d.towerComplete_iff_intrinsic X K).2 _hK)
    (completeProetale_origins X d K _origins)

end AlgebraicGeometry.Scheme
