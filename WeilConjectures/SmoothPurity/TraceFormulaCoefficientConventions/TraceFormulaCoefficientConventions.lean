/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Pbc.PbcCohomologySheaves
public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorHom
public import WeilConjectures.SmoothPurity.Finite.FiniteCoefficientPoint
public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.SixFunctors.Finite.FiniteTorAmplitude
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleTorAmplitude
public import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructible
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleCohomologicalSupport
public import WeilConjectures.SmoothPurity.Sf.SfDerivedComplete
public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicFiniteTorsionConstructibility
public import WeilConjectures.ZetaWeil.OrdinaryCompactCohomology
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import WeilConjectures.AlgebraicGeometry.ProEtale.Intrinsic.ProEtaleIntrinsicFiniteOperations
public import WeilConjectures.Compactification.Defs
public import WeilConjectures.AlgebraicGeometry.SmoothPurity.CompactifiableOverField
public import Mathlib.AlgebraicGeometry.Pullbacks

/-!
# Trace-formula coefficient conventions

Source: Weil conjectures blueprint, `main-20261015`,
`sec-six-functors-basics/sk-def-sf-admissible/def-trf-coefficient-conventions.md`
(blueprint: def-trf-coefficient-conventions).

The structure fixes the finite-field datum, a finite coefficient extension and level,
and a separated finite-type scheme over the base.  The abbreviations below reuse the
recorded finite constructible categories, derived operations, cohomology functors and
compact-support construction; no parallel coefficient category is introduced.
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures

/-- The finite-field, finite-coefficient and geometric scheme data used by the trace formula.
Source: Weil conjectures blueprint, `main-20261015`,
`sec-six-functors-basics/sk-def-sf-admissible/def-trf-coefficient-conventions.md`
(blueprint: def-trf-coefficient-conventions).

The finite extension is a finite intermediate field in the chosen algebraic closure, and
`X₀` is presented as an object over `Spec k₀`; its three morphism properties are stored as
instance fields so that the geometric fibre and all finite coefficient constructions use
exactly the hypotheses of the source.
-/
structure TraceFormulaCoefficientConventions where
  datum : FiniteFieldDatum.{u}
  coefficients : datum.CoefficientDatum
  extension : Padic.FiniteCoefficientFields coefficients.l coefficients.Qbar
  level : ℕ
  level_pos : 1 ≤ level
  X₀ : Over (Spec (CommRingCat.of datum.k₀))
  [finite_type : LocallyOfFiniteType X₀.hom]
  [quasi_compact : QuasiCompact X₀.hom]
  [separated : IsSeparated X₀.hom]

attribute [instance] TraceFormulaCoefficientConventions.finite_type
  TraceFormulaCoefficientConventions.quasi_compact
  TraceFormulaCoefficientConventions.separated

namespace TraceFormulaCoefficientConventions

/-- The recorded small model of the chosen finite field inside the algebraic closure.
It is transported by `Shrink.algEquiv`, retaining the field and its inclusion.
Source: blueprint (blueprint: def-trf-coefficient-conventions). -/
noncomputable abbrev coefficientField (T : TraceFormulaCoefficientConventions.{u}) : Type u :=
  AlgebraicallyClosedCoefficients.Coefficient.{u} T.coefficients.l T.coefficients.Qbar
    T.extension

/-- The finite coefficient ring `A = O_E / ϖ_E^n`.
Source: blueprint (blueprint: def-trf-coefficient-conventions). -/
noncomputable abbrev coefficientRing (T : TraceFormulaCoefficientConventions.{u}) : Type u :=
  Padic.coefficientExtensionRing T.coefficients.l T.coefficientField T.level

/-- The geometric base change `X = X₀ ×_{k₀} k`, with its structure morphism.
Source: blueprint (blueprint: def-trf-coefficient-conventions). -/
noncomputable abbrev geometricBaseChange (T : TraceFormulaCoefficientConventions.{u}) :
    Scheme.{u} := (T.datum.geometricFiber T.X₀).left

/-- The structure morphism `a_X : X → Spec k`.
Source: blueprint (blueprint: def-trf-coefficient-conventions). -/
noncomputable abbrev structureMap (T : TraceFormulaCoefficientConventions.{u}) :
    T.geometricBaseChange ⟶ Spec (CommRingCat.of T.datum.k) :=
  (T.datum.geometricFiber T.X₀).hom

/-- The recorded finite-coefficient inverse image along an arbitrary scheme morphism.
Source: blueprint (blueprint: def-trf-coefficient-conventions). -/
noncomputable def derivedPullback (T : TraceFormulaCoefficientConventions.{u})
    {Y Z : Scheme.{u}} (f : Y ⟶ Z) :
    proEtaleDerivedCategory Z T.coefficientRing ⥤
      proEtaleDerivedCategory Y T.coefficientRing := by
  unfold coefficientRing
  rw [← Nat.sub_add_cancel T.level_pos]
  exact finiteDerivedPullback T.coefficients.l T.coefficientField (T.level - 1) f

/-- Finite type and separation survive the geometric base change used in the conventions.
These are the usual pullback instances, with no additional geometric hypothesis.
Source: blueprint (blueprint: def-trf-coefficient-conventions). -/
noncomputable instance geometricFiniteType (T : TraceFormulaCoefficientConventions.{u}) :
    LocallyOfFiniteType T.structureMap := by
  change LocallyOfFiniteType (CategoryTheory.Limits.pullback.snd T.X₀.hom
    (Spec.map (CommRingCat.ofHom (algebraMap T.datum.k₀ T.datum.k))))
  infer_instance

/-- Quasi-compactness survives the geometric base change.
Source: blueprint (blueprint: def-trf-coefficient-conventions). -/
noncomputable instance geometricQuasiCompact (T : TraceFormulaCoefficientConventions.{u}) :
    QuasiCompact T.structureMap := by
  change QuasiCompact (CategoryTheory.Limits.pullback.snd T.X₀.hom
    (Spec.map (CommRingCat.ofHom (algebraMap T.datum.k₀ T.datum.k))))
  infer_instance

/-- Separation survives the geometric base change.
Source: blueprint (blueprint: def-trf-coefficient-conventions). -/
noncomputable instance geometricSeparated (T : TraceFormulaCoefficientConventions.{u}) :
    IsSeparated T.structureMap := by
  change IsSeparated (CategoryTheory.Limits.pullback.snd T.X₀.hom
    (Spec.map (CommRingCat.ofHom (algebraMap T.datum.k₀ T.datum.k))))
  infer_instance

end TraceFormulaCoefficientConventions
end WeilConjectures
