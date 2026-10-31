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

/-! Fixed finite-field branch of native proper scalar extension.
(blueprint: lem-dla1-native-proper-scalar-extension) -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- Finite field-extension case `E → F` (`E ≤ F` in `ℚ̄_ℓ`) of
`nativeProperScalarExtension`.

Source: `literature/blueprint/latest/blueprint/sec-six-functors-basics/`
`sk-prop-scalar-six/det-prop-scalar-six-direct-image.proof.md`, paragraphs
"Finite free coefficient extensions" and "Preservation"; Stacks Tag 0944.

Proof:
1. By lem-sfb-internal-scalar-pullback-normalization and
   lem-sfb-scalar-direct-image-mate-coherence, `scalarDirectImageMate a p` is the
   transpose of the scalar-changed counit, i.e. the canonical balanced comparison
   `(Rp_* K) ⊗_E F → Rp_*(K ⊗_E F)`.
2. By sk-prop-sfb-cartesian-coefficients, `F_Y` is finite free over `E_Y` of rank
   `[F:E]`, compatibly with pullback. lem-pur-finite-free-proper-scalar-comparison
   shows the specified scalar-adjunction mate is invertible; the normalization of
   step 1 and lem-sfb-internal-section-scalar-adjunction identify its functors and
   adjunctions with the internal ones, and injectivity of the Hom bijection
   identifies that mate with `scalarDirectImageMate a p` (first conjunct).
3. Tensor with a finite free module is exact, keeps the cohomological bounds and
   sends a finite-dimensional `E`-model on each stratum to a finite-dimensional
   `F`-model; hence `K ⊗_E F` is bounded constructible on `Z` (second conjunct).
4. lem-per-condensed-finite-extension-direct-image gives the third conjunct
   `Rp_* K`; step 3 on `Y` gives the fourth `(Rp_* K) ⊗_E F`; the fifth
   `Rp_*(K ⊗_E F)` follows from the fourth through the isomorphism of step 2 (or
   from lem-per-condensed-finite-extension-direct-image over `F` applied to step 3).
(blueprint: lem-dla1-native-proper-scalar-extension-finite-case) -/
theorem nativeProperScalarExtension_finite_case
    (ell : ℕ) [Fact ell.Prime] (k : Type u) [Field k] [PerfectField k]
    (hell : IsUnit (ell : k))
    (E F : PadicAlgCl.FiniteIntermediateField ell) (hEF : E ≤ F)
    {Z Y : Scheme.{u}} (aZ : Z ⟶ Spec (.of k)) (aY : Y ⟶ Spec (.of k))
    [LocallyOfFiniteType aZ] [QuasiCompact aZ] [IsSeparated aZ]
    [LocallyOfFiniteType aY] [QuasiCompact aY] [IsSeparated aY]
    (p : Z ⟶ Y) [IsProper p] (hp : p ≫ aY = aZ)
    (K : DerivedCategory
      (ModuleRingedComparison.internalModules
        (Profinite.continuousMapRingObj E.1) Z))
    (hK : constantModelBoundedConstructible
      (Profinite.continuousMapRingObj E.1) Z K) :
    IsIso ((scalarDirectImageMate
      (CommMon.homMk
        (A := CommMon.mk (Profinite.continuousMapRingObj E.1))
        (B := CommMon.mk (Profinite.continuousMapRingObj F.1))
        (Mon.Hom.mk (Profinite.padicSubfieldRingObjMap ell hEF))) p).app K) ∧
      constantModelBoundedConstructible (Profinite.continuousMapRingObj F.1) Z
        ((scalarSixChange
          (CommMon.homMk
            (A := CommMon.mk (Profinite.continuousMapRingObj E.1))
            (B := CommMon.mk (Profinite.continuousMapRingObj F.1))
            (Mon.Hom.mk (Profinite.padicSubfieldRingObjMap ell hEF))) Z).obj K) ∧
      constantModelBoundedConstructible
        (Profinite.continuousMapRingObj E.1) Y
        ((RootCoordinateFace.lower
          (Profinite.continuousMapRingObj E.1) p).obj K) ∧
      constantModelBoundedConstructible (Profinite.continuousMapRingObj F.1) Y
        ((scalarSixChange
          (CommMon.homMk
            (A := CommMon.mk (Profinite.continuousMapRingObj E.1))
            (B := CommMon.mk (Profinite.continuousMapRingObj F.1))
            (Mon.Hom.mk (Profinite.padicSubfieldRingObjMap ell hEF))) Y).obj
          ((RootCoordinateFace.lower
            (Profinite.continuousMapRingObj E.1) p).obj K)) ∧
      constantModelBoundedConstructible (Profinite.continuousMapRingObj F.1) Y
        ((RootCoordinateFace.lower
          (Profinite.continuousMapRingObj F.1) p).obj
          ((scalarSixChange
            (CommMon.homMk
              (A := CommMon.mk (Profinite.continuousMapRingObj E.1))
              (B := CommMon.mk (Profinite.continuousMapRingObj F.1))
              (Mon.Hom.mk (Profinite.padicSubfieldRingObjMap ell hEF))) Z).obj K)) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
