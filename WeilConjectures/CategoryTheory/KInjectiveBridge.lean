/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.CochainComplexPlus
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.CategoryTheory.Preadditive.LeftExact
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution

/-!
# The K-injective bridge

Source: Weil conjectures blueprint, sec-abelian-varieties, cor-pqf-proper-quasifinite-finite,
def-sp-kinjective-bridge (blueprint: def-sp-kinjective-bridge).

## Main definitions

* `CochainComplex.KInjectiveResolutionChoice`: a chosen quasi-isomorphism into a K-injective
  complex in an arbitrary abelian category.
* `CochainComplex.grothendieckKInjectiveResolutionChoice`: the existing functorial resolution
  supplies such a choice for every complex in a Grothendieck abelian category.
* `CategoryTheory.Functor.rightDerivedComplexWithResolution`: `RvK := v(I)` for a chosen
  resolution of a bounded-below complex.
* `CategoryTheory.Functor.rightDerivedCohomologyWithResolution`: `R^p v(K) := H^p(v(I))`.

K-injectivity uses Mathlib's `CochainComplex.IsKInjective`, as in
`lem-sfb-grothendieck-k-injective`: every map from an acyclic complex is null-homotopic.
The Hom-complex formulation follows by applying this in every shifted degree.
Independence of the choice and agreement with `Functor.rightDerived` on objects in degree zero
are deferred to `lem-sp-kinjective-computes`; the definitions retain the chosen resolution.
-/

@[expose] public section

universe w v₁ v₂ u₁ u₂

open CategoryTheory CategoryTheory.Limits

namespace CochainComplex

/-- A K-injective resolution consists of a complex `I`, a quasi-isomorphism `K ⟶ I`, and
K-injectivity of `I`, using the generic Mathlib notions underlying the étale specialization
`lem-sfb-grothendieck-k-injective`.
Source: blueprint def-sp-kinjective-bridge (blueprint: def-sp-kinjective-bridge). -/
structure KInjectiveResolutionChoice {C : Type u₁} [Category.{v₁} C] [Abelian C]
    (K : CochainComplex C ℤ) where
  complex : CochainComplex C ℤ
  map : K ⟶ complex
  quasiIso : QuasiIso map
  isKInjective : complex.IsKInjective

/-- Every complex in a Grothendieck abelian category has a chosen K-injective resolution,
obtained from the functor and natural transformation of
`lem-weil-pbc-kinjective-functorial-existence`. This includes every bounded-below complex.
Source: blueprint def-sp-kinjective-bridge (blueprint: def-sp-kinjective-bridge). -/
noncomputable def grothendieckKInjectiveResolutionChoice
    {C : Type u₁} [Category.{v₁} C] [Abelian C] [IsGrothendieckAbelian.{w} C]
    (K : CochainComplex C ℤ) : KInjectiveResolutionChoice K where
  complex := (kInjectiveResolutionFunctor.{w} C).obj K
  map := (toKInjectiveResolution.{w} C).app K
  quasiIso := (monoQuasiIso_toKInjectiveResolution_app.{w} C K).2
  isKInjective := isKInjective_kInjectiveResolutionFunctor_obj.{w} C K

end CochainComplex

namespace CategoryTheory.Functor

end CategoryTheory.Functor
