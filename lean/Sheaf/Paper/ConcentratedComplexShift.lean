/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NL
-/
module

public import Sheaf.Paper.PurityFiniteSetting
public import Sheaf.Paper.FiniteTorAmplitude
public import Sheaf.Paper.ProEtaleFixedModuleLocalConstancy
public import Sheaf.AlgebraicGeometry.ProEtaleOperations
public import Sheaf.AlgebraicGeometry.ProEtaleGeometricStalk
public import Sheaf.AlgebraicGeometry.ProEtaleConstantExact
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import all Sheaf.Paper.ProEtaleConstantModuleConstructibility
import Sheaf.Paper.ProEtaleConstantModulePullbackHomology
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Conservative

/-!
# Complexes with cohomology in a single degree

Source: the blueprint of the Weil conjectures, chapter `sec-smooth-purity`, unit
`sk-thm-dnc`, node `lem-pur-concentrated-complex-shift`
(blueprint: lem-pur-concentrated-complex-shift).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

namespace AlgebraicGeometry.Scheme

/-- The canonical uncompleted derived pullback for the constant coefficient ring.
It is the derived functor of the specified pro-etale inverse-image module construction,
using the canonical coefficient comparison. Its invertibility is the existing
`finiteCoefficientCommRingMap_isIso`; no coefficient map or equivalence is chosen.
Source: Stacks Project, Tags 0H7J and 09A5; blueprint `sk-thm-dnc`,
node `lem-pur-concentrated-complex-shift`
(blueprint: lem-pur-concentrated-complex-shift). -/
noncomputable def proEtaleConstantDerivedPullback (P : WeilConjectures.PurityFiniteSetting.{u})
    {U T : Scheme.{u}} (u : U ⟶ T) :
    proEtaleDerivedCategory T P.Ring ⥤ proEtaleDerivedCategory U P.Ring :=
  letI : Finite P.Ring := Padic.finite_coefficientExtensionRing
    P.coefficients.l P.extension P.level P.level_pos
  letI : TopologicalSpace (ULift.{u + 1, u} P.Ring) := ⊥
  letI := discreteTopology_bot (ULift.{u + 1, u} P.Ring)
  letI := AlgebraicGeometry.ProEtale.finiteCoefficientCommRingMap_isIso u
    (ULift.{u + 1, u} P.Ring)
  proEtaleRingDerivedPullback u (proEtaleConstantRing T P.Ring)
    (proEtaleConstantRing U P.Ring) (asIso (proEtaleCoefficientInverseImageMap u P.Ring))

/-- The two independent assertions of the single-degree concentration lemma.
The first isomorphism is normalized to the identity on degree-`r` cohomology, using
`singleFunctors.shiftIso` and `singleFunctorCompHomologyFunctorIso`. This determines it
uniquely and records the canonical truncation isomorphism, rather than mere existence.

Source: blueprint `sec-smooth-purity/sk-thm-dnc/lem-pur-concentrated-complex-shift.md`,
Proof Steps 1-2 (blueprint: lem-pur-concentrated-complex-shift).

Proof: (1) Choose a cochain representative. The canonical inclusion from its truncation
at `r` induces cohomology isomorphisms at and below `r`, and both complexes have zero
cohomology above `r` (lem-weil-pbc-truncation-cohomology). The truncation triangle's
cycles-to-cohomology quotient is also a cohomology isomorphism: at `r` it is the canonical
quotient and away from `r` both sides vanish (lem-weil-pbc-truncation-triangle).
(2) Both maps are isomorphisms by lem-weil-pbc-unbounded-derived-iso-cohomology.
Compose the inverse of the inclusion with the quotient. Its map on `H^r` is the identity;
full faithfulness of the single-degree embedding makes this normalization unique.
(3) For the independent descent assertion, the finite coefficient ring is finite by
def-weil-l-adic-coefficient-extension. A surjective etale map is a pro-etale singleton
cover (lem-pur-etale-proetale-cover). Exact inverse image commutes with kernels, images
and their quotients, so computes derived pullback and commutes with cohomology
(prop-weil-pbc-proetale-constant-exact). The shifted sheaf has no other cohomology;
covering-family conservativity gives vanishing downstairs (lem-cbc-proetale-stalk-conservative).
(4) The localization equivalence of lem-weil-proetale-weakly-etale-localization identifies
inverse image with localized restriction: the inverse-image indexing category for an
object over U has its graph as initial object, so its opposite colimit evaluates at
that object. The identification preserves constant scalars and module actions.
(5) Choose a pro-etale trivializing cover of L. Localization identifies its constant
models with those over T, and composition with U to T is again a cover. Iterated
restriction therefore trivializes H^r(K) (def-weil-proetale-locally-constant-sheaf).
(6) Lift a geometric point of T to U (lem-weil-pbc-etale-cover-geometric-point-lift).
The stalk restriction comparison is surjective by pulling a neighbourhood back to U.
It is injective by a common pointed refinement followed by equalization of its two
maps to U (def-weil-proetale-geometric-stalk and the localization lemma). It is linear,
so the stalk of H^r(K) is isomorphic to the finite stalk of L. No uniform bound is used. -/
theorem concentratedComplexShift (P : WeilConjectures.PurityFiniteSetting.{u})
    (T : Scheme.{u}) (a : T ⟶ Spec (CommRingCat.of P.field.k))
    [IsSeparated a] [LocallyOfFiniteType a] [QuasiCompact a]
    (K : proEtaleDerivedCategory T P.Ring)
    (hK : WeilConjectures.finiteTorConstructible P.coefficients.l P.extension P.level
      P.level_pos T K)
    (r : ℤ) :
    ((∀ i : ℤ, i ≠ r →
      IsZero ((DerivedCategory.homologyFunctor
        (proEtaleRingModules T (proEtaleConstantRing T P.Ring)) i).obj K)) →
      ∃! e : K ≅
      ((DerivedCategory.singleFunctor
        (proEtaleRingModules T (proEtaleConstantRing T P.Ring)) 0).obj
        ((DerivedCategory.homologyFunctor
          (proEtaleRingModules T (proEtaleConstantRing T P.Ring)) r).obj K))⟦-r⟧,
        (DerivedCategory.homologyFunctor
          (proEtaleRingModules T (proEtaleConstantRing T P.Ring)) r).map
          (e.hom ≫
            (((DerivedCategory.singleFunctors
              (proEtaleRingModules T (proEtaleConstantRing T P.Ring))).shiftIso
                (-r) r 0 (neg_add_cancel r)).hom.app
              ((DerivedCategory.homologyFunctor
                (proEtaleRingModules T (proEtaleConstantRing T P.Ring)) r).obj K))) =
          (DerivedCategory.singleFunctorCompHomologyFunctorIso
            (proEtaleRingModules T (proEtaleConstantRing T P.Ring)) r).inv.app
              ((DerivedCategory.homologyFunctor
                (proEtaleRingModules T (proEtaleConstantRing T P.Ring)) r).obj K)) ∧
    ∀ (U : Scheme.{u}) (u : U ⟶ T) [Surjective u] [Etale u],
      ∀ (L : proEtaleRingModules U (proEtaleConstantRing U P.Ring)),
        Nonempty ((proEtaleConstantDerivedPullback P u).obj K ≅
          ((DerivedCategory.singleFunctor
            (proEtaleRingModules U (proEtaleConstantRing U P.Ring)) 0).obj L)⟦-r⟧) →
        IsLocallyConstantProEtaleModuleSheaf U P.Ring L ∧
        (∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
          (y : Spec (.of Ω) ⟶ U),
          Finite (proEtaleGeometricModuleStalk y (proEtaleConstantRing U P.Ring) L)) →
        (∀ i : ℤ, i ≠ r →
          IsZero ((DerivedCategory.homologyFunctor
            (proEtaleRingModules T (proEtaleConstantRing T P.Ring)) i).obj K)) ∧
        IsLocallyConstantProEtaleModuleSheaf T P.Ring
          ((DerivedCategory.homologyFunctor
            (proEtaleRingModules T (proEtaleConstantRing T P.Ring)) r).obj K) ∧
        (∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
          (y : Spec (.of Ω) ⟶ T),
          Finite (proEtaleGeometricModuleStalk y (proEtaleConstantRing T P.Ring)
            ((DerivedCategory.homologyFunctor
              (proEtaleRingModules T (proEtaleConstantRing T P.Ring)) r).obj K))) := by
  have _ := hK
  constructor
  · intro hv
    let C := proEtaleRingModules T (proEtaleConstantRing T P.Ring)
    let H := (DerivedCategory.homologyFunctor C r).obj K
    have : K.IsGE r := (DerivedCategory.isGE_iff K r).2 (fun i hi ↦ hv i (ne_of_lt hi))
    have : K.IsLE r := (DerivedCategory.isLE_iff K r).2 (fun i hi ↦ hv i (ne_of_gt hi))
    obtain ⟨H', ⟨e0⟩⟩ := DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE K r
    -- e0 : K ≅ singleFunctor C r H'
    let α : H' ≅ H :=
      (DerivedCategory.singleFunctorCompHomologyFunctorIso C r).symm.app H' ≪≫
        ((DerivedCategory.homologyFunctor C r).mapIso e0).symm
    let e1 : K ≅ (DerivedCategory.singleFunctor C r).obj H :=
      e0 ≪≫ (DerivedCategory.singleFunctor C r).mapIso α
    let E := DerivedCategory.singleFunctorCompHomologyFunctorIso C r
    have he1 : (DerivedCategory.homologyFunctor C r).map e1.hom = E.inv.app H := by
      apply (cancel_mono (E.hom.app H)).1
      dsimp only [e1, Iso.trans_hom, Functor.mapIso_hom]
      rw [Functor.map_comp, Category.assoc]
      have hn := E.hom.naturality α.hom
      change (DerivedCategory.homologyFunctor C r).map
        ((DerivedCategory.singleFunctor C r).map α.hom) ≫ E.hom.app H =
        E.hom.app H' ≫ α.hom at hn
      rw [hn]
      dsimp [α, E]
      simp
      rfl
    let sh := (DerivedCategory.singleFunctors C).shiftIso (-r) r 0 (neg_add_cancel r)
    refine ⟨e1 ≪≫ (sh.app H).symm, ?_, ?_⟩
    · change (DerivedCategory.homologyFunctor C r).map
        ((e1.hom ≫ (sh.app H).inv) ≫ (sh.app H).hom) = E.inv.app H
      simpa using he1
    · intro e he
      apply Iso.ext
      apply (cancel_mono (sh.hom.app H)).1
      change e.hom ≫ sh.hom.app H = (e1.hom ≫ (sh.app H).inv) ≫ sh.hom.app H
      simp only [Category.assoc]
      change e.hom ≫ (sh.app H).hom = e1.hom ≫
        ((sh.app H).inv ≫ (sh.app H).hom)
      rw [Iso.inv_hom_id, Category.comp_id]
      apply (cancel_epi e0.inv).1
      obtain ⟨f, hf⟩ := (DerivedCategory.singleFunctor C r).map_surjective
        (e0.inv ≫ e.hom ≫ sh.hom.app H)
      obtain ⟨g, hg⟩ := (DerivedCategory.singleFunctor C r).map_surjective
        (e0.inv ≫ e1.hom)
      change e0.inv ≫ e.hom ≫ sh.hom.app H = e0.inv ≫ e1.hom
      rw [← hf, ← hg]
      congr 1
      apply (cancel_epi (E.hom.app H')).1
      have hf' := E.hom.naturality f
      have hg' := E.hom.naturality g
      change (DerivedCategory.homologyFunctor C r).map
        ((DerivedCategory.singleFunctor C r).map f) ≫ E.hom.app H = _ at hf'
      change (DerivedCategory.homologyFunctor C r).map
        ((DerivedCategory.singleFunctor C r).map g) ≫ E.hom.app H = _ at hg'
      dsimp only [Functor.id_map] at hf' hg'
      rw [← hf', ← hg', hf, hg]
      simp only [Functor.map_comp, Category.assoc]
      have he' := congrArg (fun f ↦ f ≫ E.hom.app H) he
      rw [Functor.map_comp] at he'
      simp only [Category.assoc] at he'
      rw [he', he1]
  · intro U f _ _ L he hl
    obtain ⟨e⟩ := he
    let : Finite P.Ring := Padic.finite_coefficientExtensionRing
      P.coefficients.l P.extension P.level P.level_pos
    let C := proEtaleRingModules T (proEtaleConstantRing T P.Ring)
    let D := proEtaleRingModules U (proEtaleConstantRing U P.Ring)
    let F := proEtaleConstantModulePullbackFunctor f P.Ring
    let R := proEtaleModuleRestriction T P.Ring
    let S := proEtaleModuleRestriction U P.Ring
    have : S.Additive := ⟨by intros; rfl⟩
    let A := ULift.{u + 1, u} P.Ring
    have hF (i : ℤ) : F.obj ((DerivedCategory.homologyFunctor C i).obj K) ≅
        (DerivedCategory.homologyFunctor D i).obj
          ((DerivedCategory.singleFunctor D r).obj L) :=
      (F.mapDerivedCategoryHomologyFunctorIso i).app K ≪≫
        (DerivedCategory.homologyFunctor D i).mapIso
          (e ≪≫ ((DerivedCategory.singleFunctors D).shiftIso
            (-r) r 0 (neg_add_cancel r)).app L)
    have hcover : Presieve.ofArrows (fun _ : PUnit.{u + 2} ↦ U) (fun _ ↦ f) ∈
        Scheme.proetalePrecoverage T := by
      apply Scheme.etalePrecoverage_le_proetalePrecoverage
      apply (Scheme.ofArrows_mem_precoverage_iff _).mpr
      exact ⟨fun x ↦ ⟨PUnit.unit, Surjective.surj x⟩, fun _ ↦ inferInstance⟩
    have hz (i : ℤ) (hi : i ≠ r) :
        IsZero (F.obj ((DerivedCategory.homologyFunctor C i).obj K)) := by
      apply IsZero.of_iso _ (hF i)
      rcases lt_or_gt_of_ne hi with hi | hi
      · exact DerivedCategory.isZero_of_isGE _ r i hi
      · exact DerivedCategory.isZero_of_isLE _ r i hi
    constructor
    · intro i hi
      let H := (DerivedCategory.homologyFunctor C i).obj K
      obtain ⟨ep⟩ := proEtaleModuleRestriction_pullback f P.Ring H
      have hzu : IsZero ((ProEtale.upperStar (ModuleCat.{u + 1} A) f).obj (R.obj H)) :=
        (S.map_isZero (hz i hi)).of_iso ep.symm
      let loc := ProEtale.upperStarIsoLocalizationRestriction
        (ModuleCat.{u + 1} A) f inferInstance
      have hzl : IsZero ((ProEtale.localizationRestriction
          (ModuleCat.{u + 1} A) f inferInstance).obj (R.obj H)) :=
        hzu.of_iso (loc.app (R.obj H)).symm
      have hzero : IsZero (R.obj H) := by
        have : IsIso (0 : R.obj H ⟶ R.obj H) := by
          apply ProEtale.isIso_of_isIso_localizationRestriction
            (ModuleCat.{u + 1} A) _ (fun _ : PUnit.{u + 2} ↦ f) hcover
          intro _
          change IsIso ((ProEtale.localizationRestriction
            (ModuleCat.{u + 1} A) f inferInstance).map (0 : R.obj H ⟶ R.obj H))
          exact hzl.isIso hzl _
        exact IsZero.of_mono_zero (R.obj H) (R.obj H)
      have := proEtaleModuleRestriction_isEquivalence T P.Ring
      exact (IsZero.iff_id_eq_zero _).mpr (R.map_injective (by
        rw [R.map_id, R.map_zero]
        exact hzero.eq_of_src _ _))
    · have eL : F.obj ((DerivedCategory.homologyFunctor C r).obj K) ≅ L :=
        hF r ≪≫ (DerivedCategory.singleFunctorCompHomologyFunctorIso D r).app L
      have hlF := ProEtale.isFiniteLocallyConstant_of_iso
        (S.mapIso eL).symm ((finiteLocal_iff U P.Ring L).mpr hl)
      obtain ⟨ep⟩ := proEtaleModuleRestriction_pullback f P.Ring
        ((DerivedCategory.homologyFunctor C r).obj K)
      have hlocal := ProEtale.isFiniteLocallyConstant_of_iso ep hlF
      obtain ⟨I, V, g, hg, hm⟩ := hlocal
      have hloc : ProEtale.IsFiniteLocallyConstant A
          (R.obj ((DerivedCategory.homologyFunctor C r).obj K)) := by
        refine ⟨Σ _ : PUnit.{u + 2}, I, fun p ↦ V p.2,
          fun p ↦ g p.2 ≫ f, ?_, fun p ↦ ?_⟩
        · exact Precoverage.IsStableUnderComposition.comp_mem_coverings
            (fun _ : PUnit.{u + 2} ↦ f) hcover (fun _ ↦ g) (fun _ ↦ hg)
        · obtain ⟨M, hM, ⟨em⟩⟩ := hm p.2
          exact ⟨M, hM, ⟨(ProEtale.upperStarComp _ (g p.2) f).app _ ≪≫ em⟩⟩
      exact (finiteLocal_iff T P.Ring _).mp hloc

end AlgebraicGeometry.Scheme
