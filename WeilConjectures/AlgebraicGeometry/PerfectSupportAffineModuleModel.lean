/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import WeilConjectures.AlgebraicGeometry.DerivedGlobalScalar
import WeilConjectures.AlgebraicGeometry.AffineQCohDerivedEquivalence
import WeilConjectures.AlgebraicGeometry.AffineLocalizedSiteDerivedTransport
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel
import Mathlib.CategoryTheory.Preadditive.LeftExact
import WeilConjectures.AlgebraicGeometry.AffineOpenPerfectSourceModel
import WeilConjectures.AlgebraicGeometry.AffineOpenSupportedTargetModel
import WeilConjectures.AlgebraicGeometry.AffineOpenRealizationScalar
public import Mathlib.AlgebraicGeometry.AffineScheme

/-! # Affine module models with supported cohomology

Source: Stacks Project, Tags 08EJ, 08EB and 06Z0.
(blueprint: lem-sc-perfect-support-affine-module-model).
-/

@[expose] public section

universe u w
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

private theorem affineSheafification_preservesFiniteLimits
    (X : Scheme.{u}) (U : X.Opens) (hU : IsAffineOpen U) :
    PreservesFiniteLimits (affinePerfectSheafification X U hU) := by
  let : (Modules.restrictFunctor hU.isoSpec.hom).Additive :=
    Functor.additive_of_preserves_binary_products _
  let A := X.presheaf.obj (op U)
  let T := tilde.functor A
  let : T.PreservesMonomorphisms := ⟨by
    intro M N g hg
    let : Mono g := hg
    apply (SheafOfModules.forget _).mono_of_mono_map
    apply PresheafOfModules.mono_of_injective
    intro V s t h
    apply Subtype.ext
    funext x
    apply IsLocalizedModule.map_injective x.1.asIdeal.primeCompl
      (LocalizedModule.mkLinearMap x.1.asIdeal.primeCompl M)
      (LocalizedModule.mkLinearMap x.1.asIdeal.primeCompl N)
      g.hom ((ModuleCat.mono_iff_injective g).mp inferInstance)
    exact congrArg (fun z ↦ z.val x) h⟩
  let : T.PreservesHomology :=
    Functor.preservesHomology_of_preservesMonos_and_cokernels T
  let : PreservesFiniteLimits T := T.preservesFiniteLimits_of_preservesHomology
  unfold affinePerfectSheafification
  exact comp_preservesFiniteLimits _ _

end AlgebraicGeometry.Scheme
