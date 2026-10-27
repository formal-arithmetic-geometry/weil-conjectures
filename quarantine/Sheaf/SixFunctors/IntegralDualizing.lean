/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q48
-/
module

public import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
public import Sheaf.Paper.SfIntegralConstructible
public import Sheaf.Paper.SfDerivedComplete
public import Sheaf.Paper.NormalizedDVREffectivity
public import Sheaf.AlgebraicGeometry.CompactifiableOverField
public import Sheaf.AlgebraicGeometry.SfFiniteExceptionalInverseImage
public import Sheaf.Paper.FiniteTorAmplitude
public import Sheaf.AlgebraicGeometry.ProEtaleTorAmplitude
public import Sheaf.Paper.IntrinsicFiniteTorsionConstructibility
public import Sheaf.Paper.CompletedIntegralConstantMapOfUniverses
public import Sheaf.Paper.CompactSupportReductionTower
public import Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitOfUniverses
public import Sheaf.Paper.CoefficientDuality
public import Sheaf.Paper.IntegralRationalQbarCompactSupport
public import Sheaf.Paper.FiniteCoefficientPoint
public import Sheaf.Paper.DirectImagesConstructible
public import WeilConjectures.Mathlib.Topology.KrullDimension

public import Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses
public import Sheaf.SixFunctors.FiniteDualizing

public import Sheaf.SixFunctors.IntegralDualizingRoosModel
import Sheaf.SixFunctors.IntegralDualizingFiniteBounds
import Sheaf.SixFunctors.IntegralDualizingMappingLimit
import Sheaf.Paper.SfDerivedCompleteLegacyComparison

/- Stage-2 statement delivery metadata: Q117, 2026-10-18. -/
/-!
# The integral dualizing object and its adjunction

Source: blueprint `sec-six-functors/sk-prop-sf-biduality-general`, order 2145
(blueprint: prop-coef-integral-dualizing).

All coefficients are ordinary module sheaves over the completed coefficient sheaf.
The mapping complexes retain the coefficient-module action. Compact support is the
actual strict reduction-tower functor followed by total right derived inverse limit.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

/--
Fix the finite-field datum, a prime different from its characteristic, a finite coefficient
extension, and a separated finite-type scheme over the algebraic closure. There is a bounded
constructible derived-complete integral object `ω`, presented by a normalized DVR tower whose
finite terms are the exceptional inverse images of the coefficient units. Every reduction is
identified with the corresponding finite term and has Tor amplitude `[-2d,0]`. For every
constructible integral `K`, the value `C` of integral compact support at the coefficient point
has the asserted adjunction bijection with `ω` and the coefficient unit.

Source: blueprint node `prop-coef-integral-dualizing`, order 2145
(blueprint: prop-coef-integral-dualizing).

Proof plan from the node.  Finite dualizing comparisons give coherent quotient transitions,
and strictification produces a normalized DVR tower.  Derived-limit effectivity identifies
each reduction with the corresponding finite term and gives derived completeness.  Constant
coefficient objects are constructible; Verdier preservation of strata and finite site
comparison give the uniform Tor interval `[-2d,0]`.  For bounded constructible `K`, residue
Tor invariance and compact-support reduction identify its finite compact-support values with
the reductions of the integral value `C`.  Scalar extension--restriction adjunction gives
the finite mapping-complex comparisons, and the finite counit transitions make them a map
of towers.  The ringed-site derived-limit comparison identifies mapping out of the limit
with the limit of the finite mapping complexes.  The tower pairing, coaugmentation and
currying identify that tower with the coefficient-point Hom tower.  Completeness of the
DVR identifies the derived limit of its coefficient quotients with `R`; composing these
natural isomorphisms gives the stated coefficient-point adjunction.  The plan uses
`lem-coef-finite-dualizing`, `def-coef-normalized-dvr-tower`,
`lem-coef-normalized-dvr-effectivity`, `lem-coef-integral-compact-support`,
`lem-coef-integral-residue-tor`, `lem-pod-point-sections-derived-reduction`,
`lem-weil-pbc-ringed-strict-tower-homotopy-limit`,
`lem-coef-finite-mapping-adjunction`, `lem-coef-finite-adjunction-transition`,
`lem-coef-tower-trace-rectification`, `lem-coef-tower-evaluation-pairing`,
`lem-coef-tower-coaugmentation`, and `lem-coef-tower-natural-currying`, together with
the recorded internal-Hom, global-sections, finite-duality, and point-fibre comparisons.
-/
theorem prop_coef_integral_dualizing
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]
    (d : ℕ) (hd : topologicalKrullDim X ≤ (d : WithBot ℕ∞)) :
    ∃ (ω : sfIntegralConstructibleCategory l E X)
      (T : NormalizedDVRTower l E X D hl),
      (∀ n : ℕ, Nonempty (T.M n ≅ integralDualizingFiniteTerm (l := l) (E := E)
        (D := D) (X := X) n)) ∧
      (∃ (e : ∀ n : ℕ, T.M n ≅ integralDualizingFiniteTerm (l := l) (E := E)
        (D := D) (X := X) n),
        (∀ {m n : ℕ} (h : n ≤ m),
          T.tau h ≫ (normalizedDVRRes l E X h).map (e n).hom =
            (e m).hom ≫
              (Adjunction.ofIsRightAdjoint (normalizedDVRRes l E X h)).homEquiv _ _
                (integralDualizingFiniteComparison l E D X hl h))) ∧
      Nonempty (ω.obj ≅ (integralDualizingLimit l E X).obj T.tower) ∧
      IntegralDualizingLimitPresentation l E D hl X T ω.obj ∧
      (∀ n : ℕ, HasProEtaleTorAmplitude X (Padic.coefficientExtensionRing l E (n + 1))
        ((scalarReductionDerivedExtension l E X n).obj ω.obj) (-(2 * (d : ℤ))) 0) ∧
      Nonempty (integralDualizingGlobalHom l E X ω.obj ≅
        (integralDualizingCompactSections l E D hl X).op ⋙
          coefficientDerivedDual (integralDualizingCoefficients l E)) ∧
      ∀ K : sfIntegralConstructibleCategory l E X,
        Nonempty ((K.obj ⟶ ω.obj) ≃
          ((integralDualizingLimit l E (Spec (.of D.k))).obj
            ((integralDualizingCompactTower l E D hl X).obj K.obj) ⟶
              (DerivedCategory.singleFunctor (scalarReductionSource l E (Spec (.of D.k))) 0).obj
                (SheafOfModules.unit
                  (completedIntegralCoefficientSheafUnrestricted l E (Spec (.of D.k)))))) := by
  obtain ⟨T, e, he, p, δ, htriangle⟩ := integralDualizing_roos_model D l hl E X
  let : HasCountableProducts (completedIntegralDerivedCategory l E X D hl) :=
    integralOperationsDerivedCountableProducts l E X
  let M := (integralDualizingLimit l E X).obj T.tower
  obtain ⟨hred, hcoherent, hcomplete⟩ :=
    normalizedDVRTower_effectivity l E X D hl T M p δ htriangle
  have hpresentation : IntegralDualizingLimitPresentation l E D hl X T M :=
    ⟨p, δ, htriangle, hred, fun m n h ↦ hcoherent h⟩
  have hbounds (n : ℕ) := integralDualizing_finite_bounds D l hl E X d hd n
    ((scalarReductionDerivedExtension l E X n).obj M)
    (@asIso _ _ _ _ (normalizedDVRCounitComparison l E X D hl T M p n) (hred n) ≪≫ e n)
  have hconstructible : sfIntegralConstructible l E X M := by
    refine ⟨(sfDerivedComplete_iff_legacy l E X D hl M).mpr hcomplete,
      -(2 * (d : ℤ)), 0, ?_, ?_⟩
    · omega
    · intro n
      exact ⟨(hbounds n).1, (hbounds n).2.1⟩
  let ω : sfIntegralConstructibleCategory l E X := ⟨M, hconstructible⟩
  obtain ⟨hglobal, hhom⟩ := integralDualizing_mapping_limit D l hl E X T e he ω hpresentation
  exact ⟨ω, T, (fun n ↦ ⟨e n⟩), ⟨e, he⟩, ⟨Iso.refl M⟩, hpresentation,
    (fun n ↦ (hbounds n).2.2), hglobal, hhom⟩

end WeilConjectures
