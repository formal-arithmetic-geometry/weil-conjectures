/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProfiniteFreeSlice.ProfiniteFreeSliceChainData
import WeilConjectures.CategoryTheory.Localization.ResolutionNormalizedComparison
import all WeilConjectures.CategoryTheory.RingedHomUniverses.RingedInternalHomShiftOfUniversesSupplement
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback

/-! # Normalized descent of the profinite free chain model

Source: Stacks Project Tags 08FI, 08J7; HRS Section 3.
(blueprint: new-f3-profinite-free-slice-localization-data).

The input includes a specified natural chain comparison and preservation of
K-injectives by restriction. The remaining obligation is derived descent with
the displayed localization equation, retaining the normalization of that input.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u

-- Avoid the universe-mismatched global instance exposed by newer imports.
attribute [local instance 20000] HasDerivedCategory.ofIsGrothendieckAbelian
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.ProfiniteFreeSlice
open ModuleObjectRingedComparison WeilConjectures
attribute [local instance 1000001] sectionRingHasSheafCompose sectionModulesGrothendieck
variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u}) (P : Profinite.{u})

set_option maxHeartbeats 2000000 in
-- The fixed comparison transports require more elaboration than the default budget.
/-- Descend a specified natural chain comparison with its original normalization.
Source: Stacks Project Tags 08FI, 08J7 and 0A95
(blueprint: new-f3-profinite-free-slice-localization-data).

Proof: resolve every input by the fixed functorial K-injective replacement.
The given hK makes its restriction K-injective, so the fixed right-derived
unit computes direct image on it. Apply Q to the natural chain isomorphism d
on those representatives and transport through the internal/section derived
equivalence. The K-injective localization equivalence descends this natural
isomorphism to gamma on the ordinary unbounded derived category.
Choose the section-module gamma by composing the specified homComparison
with the Hom-resolution factorization, the inverse localized augmentation,
the supplied chain isomorphism, and the inverse direct-image model.
Full faithfulness of the derived section equivalence lifts this natural
isomorphism to internal modules. Naturality on K-injectives and the
K-injective localization equivalence make these components a natural
isomorphism on all derived inputs. Its construction forces the displayed
localization equation after cancelling the named isomorphisms. Thus no
additional tensor-evaluation comparison is needed in this step: the already
given homComparison fixes the transport. -/
theorem exists_localized_chain_comparison
    (freeIso : pulledFree Λ X P ≅ freeOnTest Λ X P)
    (d : ChainComparisonData Λ X P freeIso)
    (hK : ∀ (J : CochainComplex (Internal Λ X) ℤ) [J.IsKInjective],
      CochainComplex.IsKInjective ((restrictionComplex Λ X P).obj J))
    (homComparison : Functor.uncurry.obj (CondensedRing.derivedHom Λ X) ⋙ forward Λ X ≅
      ((forward Λ X).op.prod (forward Λ X)) ⋙ hom Λ X)
    :
    ∃ gamma : (CondensedRing.derivedHom Λ X).obj (op (derivedFree Λ X P)) ≅
      sliceDerived Λ X P, ∀ (J : CochainComplex (Internal Λ X) ℤ) [J.IsKInjective]
      [CochainComplex.IsKInjective ((restrictionComplex Λ X P).obj J)],
    homComparison.hom.app (op (derivedFree Λ X P), DerivedCategory.Q.obj J) ≫
      (hom Λ X).map
        (X := (op ((forward Λ X).obj (derivedFree Λ X P)),
          (forward Λ X).obj (DerivedCategory.Q.obj J)))
        (Y := (op (DerivedCategory.Q.obj (sectionFreeComplex Λ X P)),
          DerivedCategory.Q.obj ((complexForward Λ X).obj J)))
        (Quiver.Hom.op ((localizationIso Λ X).inv.app (freeComplex Λ X P)),
          (localizationIso Λ X).hom.app J) ≫
      (WeilConjectures.coefficientHomResolutionIso.{u, u + 1, u, u + 1}
        (Scheme.ProEt.topology X) (ring Λ X) (sectionFreeComplex Λ X P)
          ((complexForward Λ X).obj J)).hom =
      (forward Λ X).map (gamma.hom.app (DerivedCategory.Q.obj J)) ≫
        (forward Λ X).map (derivedSliceModel Λ X P J).hom ≫
        (localizationIso Λ X).hom.app ((sliceComplex Λ X P).obj J) ≫
        DerivedCategory.Q.map (d.representative J).inv ≫
        DerivedCategory.Q.map
          (((homComplexFunctor (R := ring Λ X)).obj (op (sectionFreeComplex Λ X P))).map
            ((CochainComplex.toKInjectiveResolution.{u + 1} (Modules Λ X)).app
              ((complexForward Λ X).obj J))) := by
  let A := Internal Λ X
  let Q : CochainComplex A ℤ ⥤ DerivedCategory A := DerivedCategory.Q
  let QB : CochainComplex (Modules Λ X) ℤ ⥤ DerivedCategory (Modules Λ X) :=
    DerivedCategory.Q
  let E := forward Λ X
  let EC := complexForward Λ X
  let R := restriction Λ X P
  let D := directImage Λ X P
  let RC := restrictionComplex Λ X P
  let SC := sliceComplex Λ X P
  let H := (homComplexFunctor (R := ring Λ X)).obj (op (sectionFreeComplex Λ X P))
  let HD := (Functor.curry.obj (hom Λ X)).obj
    (op (QB.obj (sectionFreeComplex Λ X P)))
  let F := (CondensedRing.derivedHom Λ X).obj (op (derivedFree Λ X P))
  let S := F ⋙ E
  let T := sliceDerived Λ X P ⋙ E
  let O := EC ⋙ H ⋙ QB
  let theta : S ≅ E ⋙ (Functor.curry.obj (hom Λ X)).obj
      (op (E.obj (derivedFree Λ X P))) :=
    NatIso.ofComponents (fun N ↦ homComparison.app (op (derivedFree Λ X P), N)) (by
      intro N N' f
      simpa only [Iso.app_hom, S, F, E, Functor.comp_map, Functor.uncurry_obj_map,
        Functor.curry_obj_obj_map,
        Functor.map_id, NatTrans.id_app, Category.id_comp, Functor.prod_map,
        Functor.op_map, unop_id, op_id, Functor.curry_obj_obj_obj,
        (CondensedRing.derivedHom Λ X).map_id (op (derivedFree Λ X P)),
        (forward Λ X).map_id (derivedFree Λ X P)] using
        homComparison.hom.naturality (Prod.mkHom (𝟙 (op (derivedFree Λ X P))) f))
  let sourceIso : (Functor.curry.obj (hom Λ X)).obj
      (op (E.obj (derivedFree Λ X P))) ≅ HD :=
    (Functor.curry.obj (hom Λ X)).mapIso
      (((localizationIso Λ X).app (freeComplex Λ X P)).symm.op)
  let c : Q ⋙ S ≅ EC ⋙ QB ⋙ HD :=
    Functor.isoWhiskerLeft Q (theta ≪≫ Functor.isoWhiskerLeft E sourceIso) ≪≫
      Functor.isoWhiskerRight (localizationIso Λ X) HD
  let a₀ : H ⋙ QB ⟶ QB ⋙ HD :=
    { app := fun J ↦ ringedSiteOrdinaryHomComparison.{u + 1, u, u, u + 1}
        (Scheme.ProEt.topology X) (ring Λ X) (sectionFreeComplex Λ X P) J
      naturality := by
        intro J J' f
        simpa only [H, HD, QB, hom, Functor.comp_map,
          RingedHomUniverses.ordinaryComparison_app,
          RingedHomUniverses.ordinaryBifunctor, Functor.uncurry_obj_map,
          Functor.curry_obj_obj_map, Functor.map_id, NatTrans.id_app, Category.id_comp,
          Functor.prod_map, Functor.op_map, unop_id, op_id,
          (homComplexFunctor (R := ring Λ X)).map_id (op (sectionFreeComplex Λ X P)),
          (DerivedCategory.Q (C := Modules Λ X)).map_id (sectionFreeComplex Λ X P)] using
          (RingedHomUniverses.ordinaryComparison.{u + 1, u, u, u + 1}
            (Scheme.ProEt.topology X) (ring Λ X)).naturality
              (Prod.mkHom (𝟙 (op (sectionFreeComplex Λ X P))) f) }
  let a : O ⟶ Q ⋙ S := Functor.whiskerLeft EC a₀ ≫ c.inv
  let chain : EC ⋙ H ≅ SC ⋙ EC := NatIso.ofComponents
    (fun J ↦ d.representative J) (fun f ↦ d.naturality f)
  let unit : SC ⋙ Q ⟶ Q ⋙ sliceDerived Λ X P :=
    { app := fun J ↦ D.rightDerivedFunctorUnitQ (RC.obj J) ≫
        D.rightDerivedFunctor.map (R.mapDerivedCategoryFactors.inv.app J)
      naturality := by
        intro J J' f
        simp only [sliceDerived, CondensedRing.moduleObjectDerivedPushforward,
          Functor.comp_map, Category.assoc]
        have hSC : SC.map f =
            (D.mapHomologicalComplex (.up ℤ)).map (RC.map f) := by
          ext n
          rfl
        rw [hSC]
        change DerivedCategory.Q.map
            ((D.mapHomologicalComplex (.up ℤ)).map (RC.map f)) ≫
              D.rightDerivedFunctorUnitQ (RC.obj J') ≫
                D.rightDerivedFunctor.map (R.mapDerivedCategoryFactors.inv.app J') =
          D.rightDerivedFunctorUnitQ (RC.obj J) ≫
            D.rightDerivedFunctor.map (R.mapDerivedCategoryFactors.inv.app J) ≫
              D.rightDerivedFunctor.map (R.mapDerivedCategory.map (Q.map f))
        rw [D.rightDerivedFunctorUnitQ_naturality_assoc]
        rw [← D.rightDerivedFunctor.map_comp, ← D.rightDerivedFunctor.map_comp]
        apply congrArg (fun t ↦ D.rightDerivedFunctorUnitQ (RC.obj J) ≫ t)
        exact congrArg D.rightDerivedFunctor.map
          (R.mapDerivedCategoryFactors.inv.naturality f) }
  let b : O ⟶ Q ⋙ T :=
    (Functor.isoWhiskerRight chain QB).hom ≫
      (Functor.isoWhiskerLeft SC (localizationIso Λ X)).inv ≫
      Functor.whiskerRight unit E
  let I := CochainComplex.kInjectiveResolutionFunctor.{u + 1} A
  let eta := CochainComplex.toKInjectiveResolution.{u + 1} A
  have ha (J : CochainComplex A ℤ) : IsIso (a.app (I.obj J)) := by
    have : (I.obj J).IsKInjective :=
      CochainComplex.isKInjective_kInjectiveResolutionFunctor_obj.{u + 1} A J
    have : (EC.obj (I.obj J)).IsKInjective := by
      exact inferInstanceAs (CochainComplex.IsKInjective
        (((sectionForward Λ X).mapHomologicalComplex (.up ℤ)).obj (I.obj J)))
    have : IsIso (a₀.app (EC.obj (I.obj J))) :=
      RingedHomUniverses.comparison_isIso_of_kInjective.{u + 1, u, u, u + 1}
        (Scheme.ProEt.topology X) (ring Λ X) _ _
    dsimp only [a, NatTrans.comp_app, Functor.whiskerLeft_app]
    infer_instance
  have hb (J : CochainComplex A ℤ) : IsIso (b.app (I.obj J)) := by
    have : (I.obj J).IsKInjective :=
      CochainComplex.isKInjective_kInjectiveResolutionFunctor_obj.{u + 1} A J
    have := hK (I.obj J)
    have hu : unit.app (I.obj J) = (derivedSliceModel Λ X P (I.obj J)).inv := by
      simp only [unit, Functor.rightDerivedFunctorUnitQ_eq, derivedSliceModel,
        Iso.trans_inv, Functor.mapIso_inv]
      rfl
    dsimp only [b, NatTrans.comp_app, Functor.whiskerRight_app]
    rw [hu]
    infer_instance
  obtain ⟨g, hg, _⟩ := Localization.resolutionNormalizedComparison Q
    (HomologicalComplex.quasiIso A (.up ℤ)) I eta
    (fun J ↦ (CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{u + 1} A J).2)
    O S T (Q ⋙ T) (Iso.refl _) a b ha hb
  have hE : E.IsEquivalence := by
    dsimp [E, forward]
    infer_instance
  let gamma : F ≅ sliceDerived Λ X P := Functor.fullyFaithfulCancelRight E g
  refine ⟨gamma, ?_⟩
  intro J hJ hRJ
  have hh := hg J
  change a.app J ≫ g.hom.app (Q.obj J) ≫ 𝟙 _ = b.app J at hh
  rw [Category.comp_id] at hh
  have haJ : IsIso (a.app J) := by
    have : (EC.obj J).IsKInjective := by
      exact inferInstanceAs (CochainComplex.IsKInjective
        (((sectionForward Λ X).mapHomologicalComplex (.up ℤ)).obj J))
    have : IsIso (a₀.app (EC.obj J)) :=
      RingedHomUniverses.comparison_isIso_of_kInjective.{u + 1, u, u, u + 1}
        (Scheme.ProEt.topology X) (ring Λ X) _ _
    dsimp only [a, NatTrans.comp_app, Functor.whiskerLeft_app]
    infer_instance
  have hu : unit.app J = (derivedSliceModel Λ X P J).inv := by
    simp only [unit, Functor.rightDerivedFunctorUnitQ_eq, derivedSliceModel,
      Iso.trans_inv, Functor.mapIso_inv]
    rfl
  have hgamma : E.map (gamma.hom.app (Q.obj J)) = g.hom.app (Q.obj J) := by
    simp only [gamma, Functor.fullyFaithfulCancelRight_hom_app, Functor.map_preimage]
  have hcomp :
      c.hom.app J ≫
        (coefficientHomResolutionIso.{u, u + 1, u, u + 1}
          (Scheme.ProEt.topology X) (ring Λ X) (sectionFreeComplex Λ X P)
          (EC.obj J)).hom =
      g.hom.app (Q.obj J) ≫ E.map (derivedSliceModel Λ X P J).hom ≫
        (localizationIso Λ X).hom.app (SC.obj J) ≫ QB.map (d.representative J).inv ≫
        QB.map (H.map
          ((CochainComplex.toKInjectiveResolution.{u + 1} (Modules Λ X)).app (EC.obj J))) := by
    apply (cancel_epi (a.app J)).mp
    try simp only [Category.assoc]
    rw [reassoc_of% hh]
    dsimp only [b, NatTrans.comp_app, Functor.whiskerRight_app,
      Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_inv, Functor.whiskerLeft_app,
      NatIso.ofComponents_hom_app]
    rw [hu]
    simp only [Category.assoc, ← E.map_comp_assoc, Iso.inv_hom_id, E.map_id,
      Category.id_comp, Iso.inv_hom_id_app_assoc, ← QB.map_comp_assoc]
    dsimp only [a, NatTrans.comp_app, Functor.whiskerLeft_app]
    simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
    simp only [a₀, ringedSiteOrdinaryHomComparison,
      Category.assoc, Iso.inv_hom_id, Category.comp_id]
    simp only [chain, NatIso.ofComponents_hom_app, Iso.hom_inv_id, QB.map_id,
      Category.id_comp, ringedSiteHomComplexMap, op_id,
      (homComplexFunctor (R := ring Λ X)).map_id (op (sectionFreeComplex Λ X P)),
      NatTrans.id_app]
    rfl
  rw [hgamma]
  change _ = g.hom.app (Q.obj J) ≫ _
  rw [← hcomp]
  simp only [c, theta, sourceIso, Iso.trans_hom, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Iso.app_hom, NatIso.ofComponents_hom_app, NatTrans.comp_app, Functor.mapIso_hom,
    Functor.comp_obj, Functor.curry_obj_map_app, Category.assoc]
  dsimp only [HD]
  simp only [Functor.curry_obj_obj_map]
  rw [← (hom Λ X).map_comp_assoc]
  simp only [prod_comp, Iso.op_hom, Iso.symm_hom, Iso.app_inv,
    Category.comp_id, Category.id_comp]
  rfl

end AlgebraicGeometry.ProEtale.ProfiniteFreeSlice
