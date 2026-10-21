/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E5
-/
module

public import Sheaf.Paper.IntegralModelOpenClosedBasic
import Sheaf.Paper.ContinuousModuleOpenRestriction
import Sheaf.Paper.OpenClosedAdjunctionTransport
import all Sheaf.AlgebraicGeometry.ProEtaleOperations

/-!
# Localization with continuous coefficients

Source: Stacks Project, Tags 09AH and 03DI
(blueprint: lem-weil-pbc-continuous-module-localization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale

/-- The concrete continuous-coefficient functors carry the usual open-closed
localization sequence. Source: Stacks Project, Tags 09AH and 03DI
(blueprint: lem-weil-pbc-continuous-module-localization).
Proof: apply ringed localization to the continuous ring on X. The explicit site
equivalence identifies open restriction with pullback. On the closed site, scalar
restriction along the coefficient isomorphism is an equivalence, with scalar
extension as its left adjoint. Transport localization through these equivalences;
the transported unit and counit give exactly the displayed sequence. -/
theorem continuousModule_localization {X Z : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] (U : X.ProEt) [IsOpenImmersion U.hom] [QuasiCompact U.hom]
    (hU : Set.range U.hom = (Set.range i)ᶜ)
    (T : Type u) [TopologicalSpace T] [CommRing T] [IsTopologicalRing T]
    (cU : (Scheme.proEtaleSheafInverseImage U.hom CommRingCat.{u + 1}).obj
      (latticeCoefficientSheaf X T) ≅ latticeCoefficientSheaf U.left T)
    (cZ : (Scheme.proEtaleSheafInverseImage i CommRingCat.{u + 1}).obj
      (latticeCoefficientSheaf X T) ≅ latticeCoefficientSheaf Z T)
    (hcU : cU.hom = continuousCoefficientInverseImageMap U.hom T)
    (hcZ : cZ.hom = continuousCoefficientInverseImageMap i T) :
    ∃ (aj : continuousModuleExtensionByZero U T ⊣
        Scheme.proEtaleRingModulePullback U.hom (latticeCoefficientSheaf X T)
          (latticeCoefficientSheaf U.left T) cU)
      (ai : Scheme.proEtaleRingModulePullback i (latticeCoefficientSheaf X T)
        (latticeCoefficientSheaf Z T) cZ ⊣ continuousModuleDirectImage i T),
      ∀ L, Mono (aj.counit.app L) ∧ Epi (ai.unit.app L) ∧
        (ComposableArrows.mk₂ (aj.counit.app L) (ai.unit.app L)).Exact := by
  obtain ⟨_, _, ai₀, aj₀, _, _, _, _, _, _, _, _, hs, _⟩ :=
    Scheme.proEtale_ringed_open_closed i U hU (latticeCoefficientSheaf X T)
  obtain ⟨hq, ⟨e⟩⟩ := continuousModule_open_restriction U T cU hcU
  let := hq
  let Q := (openSliceModules U T).asEquivalence
  let RC := SheafOfModules.restrictScalars
    ((sheafCompose (Scheme.ProEt.topology Z)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map cZ.hom)
  let qZ := Scheme.proEtaleScalarEquivalence Z
    ((sheafCompose (Scheme.ProEt.topology Z)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).mapIso cZ)
  let : RC.IsEquivalence := inferInstanceAs qZ.functor.IsEquivalence
  have h := localization_equivalence_transport Q
    (Scheme.proEtaleRingModulePullback U.hom (latticeCoefficientSheaf X T)
      (latticeCoefficientSheaf U.left T) cU)
    (Scheme.proEtaleRingedExtensionByZero U (latticeCoefficientSheaf X T))
    (SheafOfModules.overFunctor (latticeModuleRing X T) U) aj₀ e
    (Scheme.proEtaleModuleInverseImage i (latticeCoefficientSheaf X T))
    (Scheme.proEtaleRingedDirectImage i (latticeCoefficientSheaf X T)) ai₀
    (Scheme.proEtaleRingExtension i (latticeCoefficientSheaf X T)
      (latticeCoefficientSheaf Z T) cZ) RC
    (Scheme.proEtaleRingExtensionAdjunction i (latticeCoefficientSheaf X T)
      (latticeCoefficientSheaf Z T) cZ) hs
  unfold continuousModuleDirectImage
  rw [← hcZ]
  exact h

end AlgebraicGeometry.ProEtale
