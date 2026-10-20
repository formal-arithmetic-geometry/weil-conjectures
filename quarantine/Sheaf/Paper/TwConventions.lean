/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NL
-/
module

public import Sheaf.Paper.OrdinaryCompactCohomology

/-! # Conventions for weights

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors/
sk-rem-sf-pf-done/def-tw-conventions.md (blueprint: def-tw-conventions).

The finite-field, coefficient, geometric-base-change and coefficient-category data used
by the weight conventions are bundled in `TwConventions`.  The compactly supported
cohomology abbreviation uses the existing constant-coefficient construction.

## Main definitions

* `TwConventions` bundles the given finite-field, coefficient and scheme data.
* `TwConventions.coefficientCategory` is the recorded PBC pair category.
* `TwConventions.compactlySupportedCohomology` is constant-coefficient cohomology.
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace WeilConjectures

/-- The finite-field, coefficient and separated finite-type scheme data in the weight
conventions.
Source: literature/blueprint/main-20261015/blueprint/sec-six-functors/
sk-rem-sf-pf-done/def-tw-conventions.md (blueprint: def-tw-conventions). -/
structure TwConventions where
  datum : FiniteFieldDatum.{u}
  coefficients : datum.CoefficientDatum
  X : Over (Spec (CommRingCat.of datum.k₀))
  [finite_type : LocallyOfFiniteType X.hom]
  [quasi_compact : QuasiCompact X.hom]
  [separated : IsSeparated X.hom]

attribute [instance] TwConventions.finite_type TwConventions.quasi_compact
  TwConventions.separated

namespace TwConventions

/-- Finite type survives the specified geometric base change.
Source: blueprint main-20261015, def-tw-conventions (blueprint: def-tw-conventions). -/
instance geometricFiniteType (T : TwConventions.{u}) :
    LocallyOfFiniteType ((T.datum.geometricFiber T.X).left ↘ Spec (.of T.datum.k)) :=
  inferInstanceAs (LocallyOfFiniteType (pullback.snd T.X.hom
    (Spec.map (CommRingCat.ofHom (algebraMap T.datum.k₀ T.datum.k)))))

/-- Quasi-compactness survives the specified geometric base change.
Source: blueprint main-20261015, def-tw-conventions (blueprint: def-tw-conventions). -/
instance geometricQuasiCompact (T : TwConventions.{u}) :
    QuasiCompact ((T.datum.geometricFiber T.X).left ↘ Spec (.of T.datum.k)) :=
  inferInstanceAs (QuasiCompact (pullback.snd T.X.hom
    (Spec.map (CommRingCat.ofHom (algebraMap T.datum.k₀ T.datum.k)))))

/-- Separatedness survives the specified geometric base change.
Source: blueprint main-20261015, def-tw-conventions (blueprint: def-tw-conventions). -/
instance geometricSeparated (T : TwConventions.{u}) :
    IsSeparated ((T.datum.geometricFiber T.X).left ↘ Spec (.of T.datum.k)) :=
  inferInstanceAs (IsSeparated (pullback.snd T.X.hom
    (Spec.map (CommRingCat.ofHom (algebraMap T.datum.k₀ T.datum.k)))))

/-- The coefficient category is exactly the recorded PBC finite-stage pair category.
No envelope or alternative coefficient category is introduced.
Source: literature/blueprint/main-20261015/blueprint/sec-six-functors/
sk-rem-sf-pf-done/def-tw-conventions.md (blueprint: def-tw-conventions). -/
abbrev coefficientCategory (T : TwConventions.{u}) :=
  let Xbar := (T.datum.geometricFiber T.X).left
  let f := Xbar ↘ Spec (.of T.datum.k)
  letI : IsNoetherian Xbar := isNoetherian_of_locallyOfFiniteType f
  letI : Fact (∃ n : ℕ, topologicalKrullDim Xbar ≤ (n : WithBot ℕ∞)) :=
    ⟨exists_topologicalKrullDim_le f⟩
  letI : Fact (∀ t : Xbar, IsUnit (T.coefficients.l : Xbar.presheaf.stalk t)) :=
    ⟨fun t ↦
      let φ : T.datum.k →+* Xbar.presheaf.stalk t :=
        (Xbar.presheaf.germ ⊤ t trivial).hom.comp
          (f.appTop.hom.comp (Scheme.ΓSpecIso (.of T.datum.k)).inv.hom)
      (map_natCast φ T.coefficients.l) ▸
        (finiteFieldDatumPrimeUnit T.datum T.coefficients.l T.coefficients.different).map φ⟩
  Scheme.pbcQbarCategory T.coefficients.l T.coefficients.Qbar Xbar

/-- Compactly supported cohomology of the constant coefficient object on the geometric base
change, in every integer degree.
Source: literature/blueprint/main-20261015/blueprint/sec-six-functors/
sk-rem-sf-pf-done/def-tw-conventions.md (blueprint: def-tw-conventions). -/
noncomputable def compactlySupportedCohomology (T : TwConventions.{u}) (i : ℤ) :=
  let Xbar := (T.datum.geometricFiber T.X).left
  letI : HasCompactification (Xbar ↘ Spec (.of T.datum.k)) :=
    hasCompactification_of_finiteType_over_field T.datum.k Xbar
      (Spec (.of T.datum.k)) (Xbar ↘ Spec (.of T.datum.k))
  (qbarConstantCohomology T.datum T.coefficients.l T.coefficients.different
    Xbar T.coefficients.Qbar
    (HasCompactification.compactification (Xbar ↘ Spec (.of T.datum.k)))
    (Padic.finiteCoefficientBase T.coefficients.l T.coefficients.Qbar) i).2

end TwConventions
end WeilConjectures
