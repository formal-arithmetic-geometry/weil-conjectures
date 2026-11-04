/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Adic.AdicCoefficientDatumSupplement
public import WeilConjectures.Compactification.BaseChange
public import WeilConjectures.AlgebraicGeometry.Projection.ProjectionCompactification
public import WeilConjectures.Algebra.Homology.SmoothPurity.LocalizedModuleExactIndependent
public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicCompletionCompletedSupplement
public import WeilConjectures.AlgebraicGeometry.Ringed.RingedEtaleOriginWitness
public import WeilConjectures.AlgebraicGeometry.Pbc.PbcActualStrictPullback
public import WeilConjectures.AlgebraicGeometry.Completed.CompletedExtensionZeroComparison
public import WeilConjectures.AlgebraicGeometry.Open.OpenImmersionSquare
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.Algebra.Category.ModuleCat.Ulift
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
public import WeilConjectures.AlgebraicGeometry.Completed.Pullback.CompletedPullbackReduction
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
public import WeilConjectures.AlgebraicGeometry.Compact.CompactSupportFiniteTorsion
public import WeilConjectures.AlgebraicGeometry.StrictTower.StrictTowerProperOpenCalculus
public import WeilConjectures.SixFunctors.Supporting.ConstantCompletionEquivalence
public import WeilConjectures.AlgebraicGeometry.AdicCoefficientDatum.CompletedExchangeCoherence
public import WeilConjectures.Compactification.Refinement
public import WeilConjectures.Compactification.RefinementCategory
public import Mathlib.CategoryTheory.Adjunction.Mates

import WeilConjectures.Compactification.Cofiltered
import WeilConjectures.AlgebraicGeometry.AdicCoefficientDatum.CompletedPullbackReflection

import all WeilConjectures.Algebra.Homology.ProperBaseChange.OpenImmersionTensorPiece
import WeilConjectures.AlgebraicGeometry.Clopen.ClopenScalarRestrictionReverseAdjunction
import WeilConjectures.Algebra.Homology.OpenTensorNormalization.ExactDerivedAdjunctionSupplement
import WeilConjectures.AlgebraicGeometry.Strict.Tower.StrictTowerExchangeMateNormalization
import WeilConjectures.AlgebraicGeometry.Ringed.RingedOpenStrictReduction
import WeilConjectures.AlgebraicGeometry.Completed.Koszul.CompletedKoszulQuotientComparison
import all WeilConjectures.AlgebraicGeometry.Completed.CompletedFiniteExchangeCoordinates
import all WeilConjectures.AlgebraicGeometry.Complete.CompleteCompactSupportProetale
import all WeilConjectures.AlgebraicGeometry.Complete.CompleteProperOpenGamma

/-!
Lower construction API (blueprint: def-cbc-open-exact-adjunction-api).

# Section-normalized open adjunction

These proved helpers use their own `CompletedOpenAdjunction` namespace, so the
compact-support module keeps all of its original declarations.

Source: Weil conjectures blueprint, sec-smooth-purity/sk-prop-sf-cbc,
node thm-cbc-complete-proetale (blueprint: thm-cbc-complete-proetale).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false

universe t

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme
namespace CompletedOpenAdjunction

variable {A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A)

/-- The projection of an open pullback, as an arrow in the original pro-etale site.
Source: Stacks 09AE, localization (blueprint: thm-cbc-complete-proetale). -/
def cbcOpenProjection {U T : Scheme.{t}} (j : U ⟶ T) [IsOpenImmersion j]
    (V : T.ProEt) :
    (cbcOpenSiteFunctor j inferInstance).obj ((proEtaleBaseChange j).obj V) ⟶ V :=
  MorphismProperty.Over.homMk (pullback.fst V.hom j) pullback.condition

/-- Restriction of sections is the unit from a module to direct image of open restriction.
Its section formula fixes the comparison, including its completed scalar action.
Source: Stacks 03DI and 09AE (blueprint: thm-cbc-complete-proetale).
Proof: apply each presheaf restriction to the displayed pullback projection. Functoriality
makes these maps natural. The finite coefficient projections show scalar compatibility;
limit uniqueness gives the same compatibility for completed coefficients. The formula on
all sections uniquely determines a sheaf map and then the natural transformation. -/
theorem cbcRestrictionUnit_existsUnique {U T : Scheme.{t}} (j : U ⟶ T)
    [IsOpenImmersion j] :
    ∃! η : 𝟭 (proEtaleRingModules T (d.completedRing T)) ⟶
        cbcOpenRestriction d j inferInstance ⋙
          proEtaleRingModuleDirectImage j (d.completedRing T) (d.completedRing U)
            (d.integralRingIso j),
      ∀ (M : proEtaleRingModules T (d.completedRing T)) (V : T.ProEt)
        (x : M.val.obj (op V)),
        (η.app M).val.app (op V) x = M.val.map (cbcOpenProjection j V).op x := by
  refine ⟨(cbcRestrictionAdjunction d j).unit,
    cbcRestrictionAdjunction_unit d j, ?_⟩
  intro θ hθ
  ext M V x
  exact (hθ M V.unop x).trans (cbcRestrictionAdjunction_unit d j M V.unop x).symm

/-- The section-normalized restriction unit.
Source: Stacks 03DI (blueprint: thm-cbc-complete-proetale). -/
def cbcRestrictionUnit {U T : Scheme.{t}} (j : U ⟶ T) [IsOpenImmersion j] :=
  (cbcRestrictionUnit_existsUnique d j).choose

set_option maxHeartbeats 800000 in
-- Transposing the section unit compares the concrete and small-model module categories.
/-- Ordinary inverse image identifies with open restriction by transposing its section unit.
Source: Stacks 03DI and 09AE (blueprint: thm-cbc-complete-proetale). -/
def cbcPullToRestriction {U T : Scheme.{t}} (j : U ⟶ T) [IsOpenImmersion j] :
    proEtaleRingModulePullback j (d.completedRing T) (d.completedRing U)
        (d.integralRingIso j) ⟶ cbcOpenRestriction d j inferInstance :=
  (((proEtaleRingModuleAdjunction j (d.completedRing T) (d.completedRing U)
    (d.integralRingIso j)).whiskerRight
      (proEtaleRingModules T (d.completedRing T))).homEquiv
        (𝟭 (proEtaleRingModules T (d.completedRing T)))
          (cbcOpenRestriction d j inferInstance)).symm (cbcRestrictionUnit d j)

/-- The specified restriction comparison is invertible.
Source: Stacks 03DI and 09AE (blueprint: thm-cbc-complete-proetale).
Proof: the open-site adjunction, with its finite-projection-normalized coefficient maps,
lifts to an adjunction between restriction and direct image. Its unit has exactly the
specified section formula. Uniqueness of that unit identifies the displayed transpose
with the comparison between the two left adjoints to the same direct image. Uniqueness
of left adjoints makes this comparison invertible. -/
theorem cbcPullToRestriction_isIso {U T : Scheme.{t}} (j : U ⟶ T)
    [IsOpenImmersion j] : IsIso (cbcPullToRestriction d j) := by
  let a := proEtaleRingModuleAdjunction j (d.completedRing T) (d.completedRing U)
    (d.integralRingIso j)
  let b := cbcRestrictionAdjunction d j
  have hu : cbcRestrictionUnit d j = b.unit := by
    apply (cbcRestrictionUnit_existsUnique d j).unique
    · exact (cbcRestrictionUnit_existsUnique d j).choose_spec.1
    · exact cbcRestrictionAdjunction_unit d j
  have he : cbcPullToRestriction d j = (a.leftAdjointUniq b).hom := by
    apply (a.whiskerRight (proEtaleRingModules T (d.completedRing T))).homEquiv
      (𝟭 _) (cbcOpenRestriction d j inferInstance) |>.injective
    rw [cbcPullToRestriction, Equiv.apply_symm_apply, hu]
    apply NatTrans.ext
    funext M
    exact (Adjunction.homEquiv_leftAdjointUniq_hom_app a b M).symm
  rw [he]
  infer_instance

/-- The exact, section-normalized open adjunction on completed coefficients.
Source: Stacks 03DI and 03DJ (blueprint: thm-cbc-complete-proetale). -/
def cbcDerivedOpenAdjunction {U T : Scheme.{t}} (j : U ⟶ T) [IsOpenImmersion j] :
    cbcDerivedOpenShriek d j inferInstance ⊣ d.pull j :=
  Adjunction.ofNatIsoRight
    ((Adjunction.ofNatIsoRight (cbcOpenAdjunction d j inferInstance)
      (@asIso _ _ _ _ (cbcPullToRestriction d j)
        (cbcPullToRestriction_isIso d j)).symm).mapDerivedCategoryRightDerivedAdjunction)
    (proEtaleRingModulePullback j (d.completedRing T) (d.completedRing U)
      (d.integralRingIso j)).rightDerivedFunctorIsoMapDerivedCategory


end CompletedOpenAdjunction
end AlgebraicGeometry.Scheme
