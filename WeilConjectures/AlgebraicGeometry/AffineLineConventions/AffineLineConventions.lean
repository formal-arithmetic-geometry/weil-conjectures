/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeL2.L2NativePunctualWeights
public import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeL2.NativeL2MiddleImage
public import WeilConjectures.AlgebraicGeometry.CondensedLisseExtensionInertia.CondensedLisseExtensionInertia
public import WeilConjectures.SmoothPurity.CondensedWeilModules
public import WeilConjectures.TateTwist.ProEtale
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Line
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.LineOver

/-!
# Affine-line and weight conventions

This module records the condensed pro-étale conventions used in the Deligne--Laumon
part of the blueprint.  A Weil sheaf is an actual condensed Weil module on the geometric
base change; lissity is the finite locally free pro-étale condition.  The two predicates
below are the geometric-constancy and unramified-at-infinity conditions from the opening
conventions.

Source: `literature/blueprint/latest/blueprint/sec-deligne-laumon-a1/sk-lem-wft-curve-heart/`
`rem-dl-a1-conventions.md` (blueprint: sk-d-dl-a1-setup).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.AffineLineConventions



/-- A condensed Weil sheaf on the geometric base change of a finite-field model.

The carrier is a constructible condensed `ℚ̄_ℓ`-module equipped with the canonical
geometric-Frobenius Weil isomorphism, exactly the pair used by
`sk-def-sf-weil-complexes`: the full subcategory of the Weil modules
`WeilConjectures.NativeL2.WeilModule D l U₀` whose carrier is constructible.
Source: `rem-dl-a1-conventions.md`, Weil-sheaf paragraph.
(blueprint: sk-d-dl-a1-setup). -/
abbrev WeilSheaf (D : WeilConjectures.FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    (U₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType U₀.hom] [QuasiCompact U₀.hom] :=
  WeilConjectures.condensedConstructibleWeilSheaves (Profinite.padicAlgClRingObj l)
    (WeilConjectures.FiniteFieldDatum.geometricFrobenius D U₀).hom

/-- The lisse condition for a condensed Weil sheaf: the underlying module is locally
free of finite rank in the pro-étale topology.
Source: `rem-dl-a1-conventions.md`, Weil-sheaf paragraph.
(blueprint: sk-d-dl-a1-setup). -/
def IsLisse {D : WeilConjectures.FiniteFieldDatum.{u}} {l : ℕ} [Fact l.Prime]
    {U₀ : Over (Spec (.of D.k₀))} [LocallyOfFiniteType U₀.hom] [QuasiCompact U₀.hom]
    (F : WeilSheaf D l U₀) : Prop :=
  IsLisseCoefficientModule (Profinite.padicAlgClRingObj l) F.obj.carrier

/-- Geometric constancy: on every connected open of the geometric fibre, the underlying
condensed module is a finite direct sum of the coefficient unit.  The Weil structure is
retained by `F`, so its Frobenius module can remain nontrivial.
Source: `rem-dl-a1-conventions.md`, geometric-constancy paragraph.
(blueprint: sk-d-dl-a1-setup). -/
def IsGeometricallyConstant {D : WeilConjectures.FiniteFieldDatum.{u}} {l : ℕ}
    [Fact l.Prime] {U₀ : Over (Spec (.of D.k₀))} [LocallyOfFiniteType U₀.hom] [QuasiCompact U₀.hom]
    (F : WeilSheaf D l U₀) : Prop :=
  ∀ V : (WeilConjectures.FiniteFieldDatum.geometricFiber D U₀).left.Opens,
    ConnectedSpace V →
      ∃ n : ℕ, Nonempty
        (((CondensedRing.upperStar (Profinite.padicAlgClRingObj l) V.ι).obj F.obj.carrier) ≅
          ⨁ fun _ : Fin n ↦
            Mod.regular (condensedRingObj (Profinite.padicAlgClRingObj l) V.toScheme))


end AlgebraicGeometry.ProEtale.AffineLineConventions
