/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Reduction.ReductionExceptionalObjects
public import WeilConjectures.AlgebraicGeometry.Reduction.ReductionExceptionalRealization
public import WeilConjectures.AlgebraicGeometry.Reduction.ReductionExceptionalConservativity
public import WeilConjectures.AlgebraicGeometry.Reduction.ReductionExceptionalChart
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantModuleConstructibility
public import WeilConjectures.AlgebraicGeometry.Reduction.ReductionDirectImage
public import WeilConjectures.AlgebraicGeometry.Scalar.ScalarExtensionFunctor
public import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteModulesSupplement
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.AlgebraicGeometry.Finite.Compact.FiniteCompactSiteCoherence
public import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedEtaleCompactSupportComparisonsSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleTorAmplitudePresentations
public import WeilConjectures.AlgebraicGeometry.ProEtale.Fixed.ProEtaleFixedModuleConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteLocalizingExceptionalPreservation
import Mathlib.CategoryTheory.Adjunction.Unique

/-! # Counit transposes for finite exceptional composition

Source: blueprint, sec-smooth-purity/sk-prop-sp-composition/
sk-prop-sp-composition-comparisons.proof.md, (1)-(2)
(blueprint: lem-sp-finite-adjoint-compositor-transposes).

All categories below are the ordinary intrinsic constant-ring Dctf categories.
The left adjoints and scalar functors are the recorded constructions. The compositor
is normalized on every bounded-below etale witness by the proper counit mate and
open-extension comparisons, not by an arbitrary choice of natural isomorphism.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.ProEtale
open Scheme

/-- The recorded compact-support restriction for a specified compactification.
Source: blueprint comparisons (1), with coefficient-independent compactifications
(blueprint: lem-sp-finite-adjoint-compositor-transposes). -/
abbrev finiteAdjointSupport (R : Type u) [CommRing R] [Finite R]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (h : ∀ M : spFiniteConstructibleTorCategory X R,
      spFiniteConstructibleTor Y R ((reductionCompactSupport R c.i c.g).obj M.obj)) :=
  reductionCtfCompactSupport R c.i c.g h

/-- The proper/open site comparison with the bounded-below/ambient compatibility
inserted explicitly. This is a paste of the recorded comparisons, with real data.
Source: blueprint comparisons (1); finite compact-support site coherence
(blueprint: lem-sp-finite-adjoint-compositor-transposes). -/
def finiteAdjointSiteSupportIso (R : Type u) [CommRing R] [Finite R]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :
    DerivedCategory.Plus.ι ⋙ reductionSite R X ⋙ reductionCompactSupport R c.i c.g ≅
      Etale.rightDerivedLowerShriekOfCompactificationPlus
          (ModuleCat.{u + 1} (ULift.{u + 1, u} R)) c ⋙
        DerivedCategory.Plus.ι ⋙ reductionSite R Y :=
  reductionSiteCompactSupportIso R c.i c.g ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (Etale.rightDerivedLowerShriekOfCompactificationPlusCompatibility
        (ModuleCat.{u + 1} (ULift.{u + 1, u} R)) c).symm _ ≪≫
    Functor.associator _ _ _

/-- The given constructible adjunctions and the specified proper/open compositor.
The last field states its normalization through the actual site comparisons on every
etale witness whose realization belongs to Dctf. No witness of etale origin is imposed
on the objects of Dctf itself.
Source: blueprint comparisons (1)-(2); finite compact-support site coherence
(blueprint: lem-sp-finite-adjoint-compositor-transposes). -/
structure FiniteAdjointCompositorDatum (R : Type u) [CommRing R] [Finite R]
    {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    [QuasiCompact f] [QuasiCompact g]
    (cf : Compactification f) (cg : Compactification g)
    (ch : Compactification (f ≫ g)) where
  hFf : ∀ M : spFiniteConstructibleTorCategory X R,
    spFiniteConstructibleTor Y R ((reductionCompactSupport R cf.i cf.g).obj M.obj)
  hFg : ∀ M : spFiniteConstructibleTorCategory Y R,
    spFiniteConstructibleTor Z R ((reductionCompactSupport R cg.i cg.g).obj M.obj)
  hFh : ∀ M : spFiniteConstructibleTorCategory X R,
    spFiniteConstructibleTor Z R ((reductionCompactSupport R ch.i ch.g).obj M.obj)
  Hf : spFiniteConstructibleTorCategory Y R ⥤ spFiniteConstructibleTorCategory X R
  Hg : spFiniteConstructibleTorCategory Z R ⥤ spFiniteConstructibleTorCategory Y R
  Hh : spFiniteConstructibleTorCategory Z R ⥤ spFiniteConstructibleTorCategory X R
  adjf : finiteAdjointSupport R cf hFf ⊣ Hf
  adjg : finiteAdjointSupport R cg hFg ⊣ Hg
  adjh : finiteAdjointSupport R ch hFh ⊣ Hh
  alpha : finiteAdjointSupport R cf hFf ⋙ finiteAdjointSupport R cg hFg ≅
    finiteAdjointSupport R ch hFh
  normalization :
    ∀ (E : DerivedCategory.Plus
        (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1, u} R))))
      (hE : spFiniteConstructibleTor X R ((reductionSite R X).obj E.obj)),
      (alpha.hom.app ⟨(reductionSite R X).obj E.obj, hE⟩).hom =
        (reductionCompactSupport R cg.i cg.g).map
            ((finiteAdjointSiteSupportIso R cf).hom.app E) ≫
          (finiteAdjointSiteSupportIso R cg).hom.app
            ((Etale.rightDerivedLowerShriekOfCompactificationPlus
              (ModuleCat.{u + 1} (ULift.{u + 1, u} R)) cf).obj E) ≫
          (reductionSite R Z).map
            ((coherenceEtaleCompositor (ULift.{u + 1, u} R) cf cg ch).hom.app E).hom ≫
          (finiteAdjointSiteSupportIso R ch).inv.app E

section Categorical

variable {C D C' D' : Type*} [Category* C] [Category* D]
  [Category* C'] [Category* D']

end Categorical

end AlgebraicGeometry.ProEtale
