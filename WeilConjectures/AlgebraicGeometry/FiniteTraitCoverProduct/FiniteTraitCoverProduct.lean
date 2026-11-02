/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.StrictLocalizationMap
public import WeilConjectures.AlgebraicGeometry.Sites.StrictHenselizationLocal
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationExtension
public import WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree
public import WeilConjectures.AlgebraicGeometry.Curve
public import WeilConjectures.Mathlib.RingTheory.Henselian
public import WeilConjectures.RingTheory.IsRegularSystemOfParameters
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.MvPowerSeries.Basic

/-!
# Equal-degree finite trait covers and their product

Source: blueprint `det-tf-restriction-zero-covers`, clause (ii), with the
normalization input from proof (i) (blueprint: lem-trf-finite-trait-cover-product).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits IsLocalRing

namespace AlgebraicGeometry.FiniteTraitCoverProduct

/-- A smooth pointed curve over an algebraically closed field.
Source: blueprint `det-tf-restriction-zero-covers`, clause (ii)
(blueprint: lem-trf-finite-trait-cover-product). -/
structure CurvePoint (k : Type u) [Field k] [IsAlgClosed k] where
  C : Scheme.{u}
  f : C ⟶ Spec (.of k)
  curve : IsCurve f
  smooth : Smooth f
  relativeDimension : SmoothOfRelativeDimension 1 f
  x : Spec (.of k) ⟶ C
  x_f : x ≫ f = 𝟙 _

attribute [instance] CurvePoint.curve CurvePoint.smooth CurvePoint.relativeDimension

attribute [instance] Cover.alg Cover.domain Cover.noetherian Cover.dvr Cover.regular
attribute [instance] Cover.strictlyHenselian Cover.Salg Cover.Sdomain Cover.Snoetherian
attribute [instance] Cover.Sdvr Cover.Sregular Cover.SstrictlyHenselian Cover.SalgK
attribute [instance] Cover.extensionField Cover.fractionAlgebra Cover.separable
attribute [instance] Cover.finiteExtension Cover.extensionAlgebra Cover.fractionTower

variable {k : Type u} [Field k] [IsAlgClosed k] (D₁ D₂ : Cover k)

/-- The marked point on the product of the base curves.
Source: blueprint proof (ii) (blueprint: lem-trf-finite-trait-cover-product). -/
noncomputable def basePoint : Spec (.of k) ⟶ pullback D₁.base.f D₂.base.f :=
  pullback.lift D₁.base.x D₂.base.x
    (D₁.base.x_f.trans D₂.base.x_f.symm)

/-- The completed local ring at a point of the product.
Source: Stacks Tag 0C0S (blueprint: lem-trf-finite-trait-cover-product). -/
noncomputable abbrev completion (t : product D₁ D₂) :=
  AdicCompletion (maximalIdeal ((product D₁ D₂).presheaf.stalk t))
    ((product D₁ D₂).presheaf.stalk t)

/-- The coefficient map from the ground field to a product stalk.
Source: blueprint proof (ii) (blueprint: lem-trf-finite-trait-cover-product). -/
noncomputable def coefficients (t : product D₁ D₂) : k →+* (product D₁ D₂).presheaf.stalk t :=
  (toStalk (pullback.snd _ _ ≫ pullback.fst _ _) t).comp (algebraMap k D₁.S)

end AlgebraicGeometry.FiniteTraitCoverProduct
