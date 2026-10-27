/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE
-/
module

public import Sheaf.Paper.PbcCohomologySheaves
public import Sheaf.Paper.DerivedPullbackTensorHom
public import Sheaf.Paper.FiniteCoefficientPoint
public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.Paper.FiniteTorAmplitude
public import Sheaf.AlgebraicGeometry.ProEtaleTorAmplitude
public import Sheaf.Paper.SfIntegralConstructible
public import Sheaf.AlgebraicGeometry.ProEtaleCohomologicalSupport
public import Sheaf.Paper.SfDerivedComplete
public import Sheaf.Paper.IntrinsicFiniteTorsionConstructibility
public import Sheaf.Paper.OrdinaryCompactCohomology
public import Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory
public import Sheaf.AlgebraicGeometry.ProEtaleIntrinsicFiniteOperations
public import WeilConjectures.Compactification.Defs
public import Sheaf.AlgebraicGeometry.CompactifiableOverField
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

/-- The bounded constructible finite-torsion coefficient category `D^b_c(X,A)`.
Source: blueprint (blueprint: def-trf-coefficient-conventions). -/
noncomputable abbrev boundedConstructible (T : TraceFormulaCoefficientConventions.{u}) :
    ObjectProperty (proEtaleDerivedCategory T.geometricBaseChange T.coefficientRing) :=
  intrinsicFiniteTorsionConstructible T.coefficients.l T.coefficientField T.level
    T.level_pos T.geometricBaseChange

/-- The finite-Tor subcategory `D^b_ctf(X,A)`.
Source: blueprint (blueprint: def-trf-coefficient-conventions). -/
noncomputable abbrev boundedConstructibleFiniteTor
    (T : TraceFormulaCoefficientConventions.{u}) :
    ObjectProperty (proEtaleDerivedCategory T.geometricBaseChange T.coefficientRing) :=
  finiteTorConstructible T.coefficients.l T.coefficientField T.level T.level_pos
    T.geometricBaseChange

/-- The recorded finite-coefficient inverse image along an arbitrary scheme morphism.
Source: blueprint (blueprint: def-trf-coefficient-conventions). -/
noncomputable def derivedPullback (T : TraceFormulaCoefficientConventions.{u})
    {Y Z : Scheme.{u}} (f : Y ⟶ Z) :
    proEtaleDerivedCategory Z T.coefficientRing ⥤
      proEtaleDerivedCategory Y T.coefficientRing := by
  unfold coefficientRing
  rw [← Nat.sub_add_cancel T.level_pos]
  exact finiteDerivedPullback T.coefficients.l T.coefficientField (T.level - 1) f

/-- The recorded derived tensor on the geometric fibre at the specified positive level.
Source: blueprint (blueprint: def-trf-coefficient-conventions). -/
noncomputable def derivedTensor (T : TraceFormulaCoefficientConventions.{u}) :
    proEtaleDerivedCategory T.geometricBaseChange T.coefficientRing ×
      proEtaleDerivedCategory T.geometricBaseChange T.coefficientRing ⥤
        proEtaleDerivedCategory T.geometricBaseChange T.coefficientRing := by
  unfold coefficientRing
  rw [← Nat.sub_add_cancel T.level_pos]
  exact finiteIntrinsicDerivedTensor T.coefficients.l T.coefficientField
    T.geometricBaseChange (T.level - 1)

/-- The recorded derived internal Hom, with contravariant first argument.
Source: blueprint (blueprint: def-trf-coefficient-conventions). -/
noncomputable def derivedInternalHom (T : TraceFormulaCoefficientConventions.{u}) :
    (proEtaleDerivedCategory T.geometricBaseChange T.coefficientRing)ᵒᵖ ×
      proEtaleDerivedCategory T.geometricBaseChange T.coefficientRing ⥤
        proEtaleDerivedCategory T.geometricBaseChange T.coefficientRing := by
  unfold coefficientRing
  rw [← Nat.sub_add_cancel T.level_pos]
  exact finiteIntrinsicDerivedInternalHom T.coefficients.l T.coefficientField
    T.geometricBaseChange (T.level - 1)

/-- Degree-`i` cohomology as a sheaf of modules on the small pro-etale site.
Source: blueprint (blueprint: def-trf-coefficient-conventions). -/
noncomputable abbrev cohomologySheaf (T : TraceFormulaCoefficientConventions.{u}) (i : ℤ) :
    proEtaleDerivedCategory T.geometricBaseChange T.coefficientRing ⥤
      proEtaleRingModules T.geometricBaseChange
        (proEtaleConstantRing T.geometricBaseChange T.coefficientRing) :=
  DerivedCategory.homologyFunctor _ i

/-- The finite coefficient point fibre, with its bounded finite-cohomology codomain.
Source: blueprint (blueprint: def-trf-coefficient-conventions). -/
noncomputable abbrev pointFibre (T : TraceFormulaCoefficientConventions.{u}) :=
  pointFiniteFibre T.datum T.coefficients.l T.coefficients.different T.coefficientField
    T.level T.level_pos

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

/-- The compact-support coefficient complex `Fib_s(Ra_X! K)`, in `D^b_fin(A)`.
The compactification supplies the recorded representative of `Ra_X!`; it is not a
new hypothesis on `X₀` or on `K`.
Source: blueprint (blueprint: def-trf-coefficient-conventions). -/
noncomputable def compactSupportComplex (T : TraceFormulaCoefficientConventions.{u})
    (c : Compactification T.structureMap) (K : T.boundedConstructible.FullSubcategory) :
    (DerivedCategory.pointFiniteCohomology
      (ULift.{u + 1, u} T.coefficientRing)).FullSubcategory := by
  letI : T.geometricBaseChange.Over (Spec (CommRingCat.of T.datum.k)) :=
    ⟨T.structureMap⟩
  letI : LocallyOfFiniteType (T.geometricBaseChange ↘ Spec (CommRingCat.of T.datum.k)) :=
    T.geometricFiniteType
  letI : QuasiCompact (T.geometricBaseChange ↘ Spec (CommRingCat.of T.datum.k)) :=
    T.geometricQuasiCompact
  letI : IsSeparated (T.geometricBaseChange ↘ Spec (CommRingCat.of T.datum.k)) :=
    T.geometricSeparated
  exact (finiteConstructibleSections T.datum T.coefficients.l T.coefficients.different
    T.geometricBaseChange T.coefficients.Qbar T.extension c T.level T.level_pos K).2

/-- Compact-support cohomology is the degree-`i` cohomology of `RΓ_c(X,K)`.
Source: blueprint (blueprint: def-trf-coefficient-conventions). -/
noncomputable def compactSupportCohomology (T : TraceFormulaCoefficientConventions.{u})
    (c : Compactification T.structureMap) (K : T.boundedConstructible.FullSubcategory)
    (i : ℤ) : ModuleCat.{u + 1} (ULift.{u + 1, u} T.coefficientRing) :=
  (DerivedCategory.coefficientFiniteCohomology _ i).obj (T.compactSupportComplex c K)

end TraceFormulaCoefficientConventions
end WeilConjectures
