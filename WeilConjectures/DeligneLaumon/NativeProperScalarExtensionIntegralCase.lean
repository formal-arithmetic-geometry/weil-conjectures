/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.AlgebraicGeometry.CondensedModuleDerivedPushpull
public import WeilConjectures.AlgebraicGeometry.ProfiniteFiniteConstantLocalModel
public import WeilConjectures.AlgebraicGeometry.CondensedIntegralCriterion
public import WeilConjectures.SixFunctors.RingedDerivedMonoidalComparisons
public import WeilConjectures.AlgebraicGeometry.SemilinearDerivedSections
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import WeilConjectures.SixFunctors.ScalarDirectImageMateCoherence
public import WeilConjectures.AlgebraicGeometry.RootTowerCoordinateFace
public import WeilConjectures.AlgebraicGeometry.SectionModuleOperationsData
public import WeilConjectures.Topology.ProfiniteCondensedRing
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension
public import WeilConjectures.CategoryTheory.ModuleObjects.EllAdicRationalization
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
public import Mathlib.CategoryTheory.Adjunction.Mates

/-! Fixed integral-to-field branch of native proper scalar extension.
(blueprint: lem-dla1-native-proper-scalar-extension) -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- Integral-to-field case `O_E → E` of `nativeProperScalarExtension`.

Source: `literature/blueprint/latest/blueprint/sec-six-functors-basics/`
`sk-prop-scalar-six/det-prop-scalar-six-direct-image.proof.md`, paragraphs
"O_E → E" (localization) and "Preservation"; Hemo–Richarz–Scholbach, Lemmas 5.3(1), 5.6.

Proof:
1. Finite type over the field `k` makes `Z`, `Y` Noetherian, so the proper map `p`
   is qcqs (lem-weil-pbc-finite-type-over-noetherian,
   lem-sfb-noetherian-space-compact-subsets).
2. By lem-sfb-internal-scalar-pullback-normalization and
   lem-sfb-scalar-direct-image-mate-coherence, `scalarDirectImageMate a p` is the
   transpose of the scalar-changed counit, i.e. the canonical balanced comparison
   `(Rp_* K) ⊗ E → Rp_*(K ⊗ E)`.
3. `K` is bounded, hence bounded below; lem-sfb-localized-direct-image-comparison
   applied to the qcqs `p` shows this comparison is invertible (first conjunct).
4. Scalar extension `O_E → E` is exact (lem-weil-pbc-continuous-integral-scalar-exact,
   and it is a left adjoint), so it keeps the cohomological bounds and turns a finite
   scalar presentation `O^m → O^n → P → 0` on each stratum into a finite-dimensional
   `E`-model; hence `K ⊗ E` is bounded constructible on `Z` (second conjunct).
5. lem-dla1-native-reduction-proper-direct-image gives the third conjunct `Rp_* K`;
   step 4 on `Y` gives the fourth `(Rp_* K) ⊗ E`; the fifth `Rp_*(K ⊗ E)` follows
   from the fourth through the isomorphism of step 3 (or directly from
   lem-per-condensed-finite-extension-direct-image applied to step 4).
(blueprint: lem-dla1-native-proper-scalar-extension-integral-case) -/
theorem nativeProperScalarExtension_integral_case
    (ell : ℕ) [Fact ell.Prime] (k : Type u) [Field k] [PerfectField k]
    (hell : IsUnit (ell : k))
    (E : PadicAlgCl.FiniteIntermediateField ell)
    {Z Y : Scheme.{u}} (aZ : Z ⟶ Spec (.of k)) (aY : Y ⟶ Spec (.of k))
    [LocallyOfFiniteType aZ] [QuasiCompact aZ] [IsSeparated aZ]
    [LocallyOfFiniteType aY] [QuasiCompact aY] [IsSeparated aY]
    (p : Z ⟶ Y) [IsProper p] (hp : p ≫ aY = aZ)
    (K : DerivedCategory
      (ModuleRingedComparison.internalModules
        (Profinite.padicIntegersRingObj ell E.1) Z))
    (hK : constantModelBoundedConstructible
      (Profinite.padicIntegersRingObj ell E.1) Z K) :
    IsIso ((scalarDirectImageMate
      (CommMon.homMk
        (A := CommMon.mk (Profinite.padicIntegersRingObj ell E.1))
        (B := CommMon.mk (Profinite.continuousMapRingObj E.1))
        (Mon.Hom.mk (padicIntegersRingObjToContinuousMapRingObj ell E))) p).app K) ∧
      constantModelBoundedConstructible (Profinite.continuousMapRingObj E.1) Z
        ((scalarSixChange
          (CommMon.homMk
            (A := CommMon.mk (Profinite.padicIntegersRingObj ell E.1))
            (B := CommMon.mk (Profinite.continuousMapRingObj E.1))
            (Mon.Hom.mk (padicIntegersRingObjToContinuousMapRingObj ell E))) Z).obj K) ∧
      constantModelBoundedConstructible
        (Profinite.padicIntegersRingObj ell E.1) Y
        ((RootCoordinateFace.lower
          (Profinite.padicIntegersRingObj ell E.1) p).obj K) ∧
      constantModelBoundedConstructible (Profinite.continuousMapRingObj E.1) Y
        ((scalarSixChange
          (CommMon.homMk
            (A := CommMon.mk (Profinite.padicIntegersRingObj ell E.1))
            (B := CommMon.mk (Profinite.continuousMapRingObj E.1))
            (Mon.Hom.mk (padicIntegersRingObjToContinuousMapRingObj ell E))) Y).obj
          ((RootCoordinateFace.lower
            (Profinite.padicIntegersRingObj ell E.1) p).obj K)) ∧
      constantModelBoundedConstructible (Profinite.continuousMapRingObj E.1) Y
        ((RootCoordinateFace.lower
          (Profinite.continuousMapRingObj E.1) p).obj
          ((scalarSixChange
            (CommMon.homMk
              (A := CommMon.mk (Profinite.padicIntegersRingObj ell E.1))
              (B := CommMon.mk (Profinite.continuousMapRingObj E.1))
              (Mon.Hom.mk (padicIntegersRingObjToContinuousMapRingObj ell E))) Z).obj K)) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
