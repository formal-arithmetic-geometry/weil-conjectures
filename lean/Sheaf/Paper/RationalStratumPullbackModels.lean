/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U1
-/
module

public import Sheaf.Paper.RationalStratumPullbackData
import Sheaf.Paper.RationalAmbientPullModels
import Sheaf.Paper.RationalAmbientPullComposition
import Sheaf.Paper.RationalPullSingleComputation
import Sheaf.Paper.RationalBalancedFreePullback
import Sheaf.Paper.RationalContinuousSliceTransport
import Sheaf.AlgebraicGeometry.ContinuousCoefficientPullbackIso
import Mathlib.Algebra.Homology.DerivedCategory.TStructure

/-! # Rational pullback on arbitrary trivializing stratum charts -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u v
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.RationalStratumPullback
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

private theorem coefficient_normalized {X Y : Scheme.{u}} (f : Y ⟶ X) :
    rationalCoefficientRestrictionNormalized l E f (coefficient l E f) := by
  let := coefficientExtensionNormedField l E
  exact continuousCoefficientPullback_normalized (ULift.{u + 1, u} E) f

private theorem normalized_coefficient_eq {X Y : Scheme.{u}} (f : Y ⟶ X)
    (c : (adicTowerInverseImage f).obj (rationalCoefficientSheaf l X E) ⟶
      rationalCoefficientSheaf l Y E)
    (hc : rationalCoefficientRestrictionNormalized l E f c) : c = coefficient l E f := by
  let := coefficientExtensionNormedField l E
  apply ((proEtaleSheafAdjunction f CommRingCat.{u + 1}).homEquiv _ _).injective
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext V
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro b
  apply ContinuousMap.ext
  intro x
  exact (hc V.unop b x).trans ((coefficient_normalized l E f) V.unop b x).symm

private theorem chart_coefficient_iso {X : Scheme.{u}} (U : X.ProEt) :
    IsIso (coefficient l E U.hom) := by
  obtain ⟨b⟩ := ContinuousRational.rationalContinuousSliceTransport l E X U
  rw [← normalized_coefficient_eq l E U.hom b.coefficient b.normalized]
  exact b.coefficient_iso

private theorem immersion_coefficient_iso {X Y : Scheme.{u}} [IsNoetherian X]
    (i : Y ⟶ X) [IsImmersion i] : IsIso (coefficient l E i) := by
  let := coefficientExtensionNormedField l E
  exact (continuousCoefficientPullback_isIso l E X i).2

private theorem finite_free (X : Scheme.{u}) (r : ℕ) :
    (free l E X r).IsFiniteLocallyFree := by
  let q := (SheafOfModules.free.generatingSections
    (R := (adicLisseForget X).obj (rationalCoefficientSheaf l X E))
    (ULift.{u + 1} (Fin r))).localGeneratorsData
  have hq : q.IsLocallyFreeData := inferInstance
  have hf : SheafOfModules.LocalGeneratorsData.IsFiniteType (M := free l E X r) q := by
    constructor
    intro j
    constructor
    change Finite (ULift.{u + 1} (Fin r))
    infer_instance
  exact { exists_localGeneratorsData := ⟨q, hq, hf⟩ }

/-- Realized rational pullback has the stated normalized stratum and arbitrary-chart
models and is concentrated in degree zero on the pulled-back stratum.
Source: BS Lemma 6.8.2, Definitions 6.8.6/6.8.8, Remark 6.8.15
(blueprint: lem-per-rational-stratum-pullback-models).

Proof: obtain normalized ambient pullbacks and the two compositors for the stratum
square. Invertibility of the immersion coefficient map gives exact single restriction,
so these records assemble Stratum. Its comparison, followed by single computation
on the finite locally free restricted sheaf, identifies the actual pulled-back
realization with an ordinary sheaf in degree zero. Transfer both standard derived
bounds through this isomorphism. For each arbitrary chart use its ambient pullbacks
and compositors. Continuous slice transport identifies its coefficient map with an
isomorphism, giving exactChart. The ordinary balanced finite-free comparison gives
the forward and inverse section formulas. Finite free modules are finite locally free
by their canonical generating sections, so single computation supplies the final
FreeModel field. These records assemble Chart. Rank zero uses the same finite-free
generators with an empty basis; no nonemptiness of any chart or stratum is assumed. -/
theorem rational_stratum_pullback_models
    (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    (_embedding : E →ₐ[ℚ_[l]] Ω)
    (X Y : ContinuousRational.Base.{u} l) (g : Y.scheme ⟶ X.scheme)
    (aX : ContinuousRational.At l E X) (aY : ContinuousRational.At l E Y)
    (a : ContinuousRational.Along l E g aY aX)
    (F : pbcModules X.scheme (rationalCoefficientSheaf l X.scheme E))
    (_hF : ContinuousRational.IsConstructible l E X.scheme aX.encoding F)
    (K : PbcRationalCategory X.scheme (pbcIntegralDatum l E) (pbcUniformizer l E))
    (_eK : aX.J.obj K ≅ (DerivedCategory.singleFunctor _ 0).obj F)
    (S : Scheme.{u}) (i : S ⟶ X.scheme) [IsImmersion i]
    (_hS : ((ContinuousRational.modulePull i (coefficient l E i)).obj F).IsFiniteLocallyFree) :
    ∃ m : Stratum l E g aX aY a i,
      ((ContinuousRational.derivedPull (pullback.fst g i)
        (coefficient l E (pullback.fst g i))).obj (aY.J.obj ((a.raw l E).obj K))).IsGE 0 ∧
      ((ContinuousRational.derivedPull (pullback.fst g i)
        (coefficient l E (pullback.fst g i))).obj (aY.J.obj ((a.raw l E).obj K))).IsLE 0 ∧
      ∀ (U : S.ProEt) (r : ℕ)
        (e : (ContinuousRational.modulePull U.hom (coefficient l E U.hom)).obj
          ((ContinuousRational.modulePull i (coefficient l E i)).obj F) ≅ free l E U.left r),
        Nonempty (Chart l E m F U r e) := by
  obtain ⟨pi⟩ := rational_ambient_pull_models l E i
  obtain ⟨pp⟩ := rational_ambient_pull_models l E (pullback.fst g i)
  obtain ⟨ps⟩ := rational_ambient_pull_models l E (pullback.snd g i)
  obtain ⟨pl⟩ := rational_ambient_pull_models l E (pullback.fst g i ≫ g)
  obtain ⟨pr⟩ := rational_ambient_pull_models l E (pullback.snd g i ≫ i)
  obtain ⟨cl⟩ := rational_ambient_pull_composition l E g (pullback.fst g i)
    a.coefficient (coefficient l E (pullback.fst g i)) a.normalized
    (coefficient_normalized l E _) (pullAlong l E a) pp pl
  obtain ⟨cr⟩ := rational_ambient_pull_composition l E i (pullback.snd g i)
    (coefficient l E i) (coefficient l E (pullback.snd g i))
    (coefficient_normalized l E _) (coefficient_normalized l E _) pi ps pr
  let m : Stratum l E g aX aY a i :=
    { inclusion := pi
      projection := pp
      stratumMap := ps
      compositeLeft := pl
      compositeRight := pr
      leftComposition := cl
      rightComposition := cr
      exactInclusion := fun M ↦ rational_pull_single_computation l E i pi M
        (Or.inl (immersion_coefficient_iso l E i)) }
  have hs := rational_pull_single_computation l E (pullback.snd g i) ps
    ((ContinuousRational.modulePull i (coefficient l E i)).obj F) (Or.inr _hS)
  let := hs
  let e := m.comparison l E F K _eK ≪≫ asIso
    (ps.singleMap l E ((ContinuousRational.modulePull i (coefficient l E i)).obj F))
  refine ⟨m, DerivedCategory.TStructure.t.isGE_of_iso e.symm 0,
    DerivedCategory.TStructure.t.isLE_of_iso e.symm 0, ?_⟩
  intro U r eU
  obtain ⟨pu⟩ := rational_ambient_pull_models l E U.hom
  obtain ⟨pb⟩ := rational_ambient_pull_models l E
    ((proEtaleBaseChange (pullback.snd g i)).obj U).hom
  obtain ⟨pf⟩ := rational_ambient_pull_models l E (pullback.fst U.hom (pullback.snd g i))
  obtain ⟨pbl⟩ := rational_ambient_pull_models l E
    (((proEtaleBaseChange (pullback.snd g i)).obj U).hom ≫ pullback.snd g i)
  obtain ⟨pbr⟩ := rational_ambient_pull_models l E
    (pullback.fst U.hom (pullback.snd g i) ≫ U.hom)
  obtain ⟨cbl⟩ := rational_ambient_pull_composition l E (pullback.snd g i)
    ((proEtaleBaseChange (pullback.snd g i)).obj U).hom
    (coefficient l E _) (coefficient l E _)
    (coefficient_normalized l E _) (coefficient_normalized l E _) ps pb pbl
  obtain ⟨cbr⟩ := rational_ambient_pull_composition l E U.hom
    (pullback.fst U.hom (pullback.snd g i))
    (coefficient l E _) (coefficient l E _)
    (coefficient_normalized l E _) (coefficient_normalized l E _) pu pf pbr
  obtain ⟨ef, hf, hb⟩ := rational_balanced_free_pullback l E
    (pullback.fst U.hom (pullback.snd g i)) r
  exact ⟨{
    chart := pu
    baseChange := pb
    chartMap := pf
    compositeLeft := pbl
    compositeRight := pbr
    leftComposition := cbl
    rightComposition := cbr
    exactChart := rational_pull_single_computation l E U.hom pu _
      (Or.inl (chart_coefficient_iso l E U))
    freeModel := {
      ordinary := ef
      forward := hf
      backward := hb
      computes := rational_pull_single_computation l E _ pf _ (Or.inr (finite_free l E _ r)) }
  }⟩

end AlgebraicGeometry.Scheme.RationalStratumPullback
