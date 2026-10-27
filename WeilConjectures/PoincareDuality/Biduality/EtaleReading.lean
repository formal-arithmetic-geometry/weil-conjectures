/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.PoincareDuality.Biduality.EtaleReadingHom
public import WeilConjectures.PoincareDuality.Biduality.EtaleReductionDualizing
public import WeilConjectures.PoincareDuality.Biduality.Reduction
public import WeilConjectures.SixFunctors.Etale.Derived.VerdierBiduality

/-!
# Finite-coefficient biduality on the pro-étale site from the étale site

Let `Λ = 𝒪_E ⧸ ℓⁿ` and write `ρ_X = Rν_* ∘ Φ : D(Mod_{Λ_X}) ⥤ D(X_ét, Λ)` for the étale reading of
condensed `Λ`-module objects (`ProEtale.CondensedRing.finiteEtaleReading` on bounded constructible
complexes). This file proves the finite step (i) of blueprint `det-pd-biduality-coefficients` for
the reductions `R K₀` of bounded constructible `𝒪_E`-complexes `K₀`: the étale reading is fully
faithful on them, carries `R ω_{X, 𝒪_E}` to the étale dualizing complex and commutes with the
internal homs into it, so the condensed Verdier dual `RHom(-, R ω_{X, 𝒪_E})` is fully faithful on
these objects as soon as the étale one is on their étale readings, which is étale Verdier
biduality. A fully faithful self-adjoint dual has invertible double-dual morphisms.

## Main results

- `ProEtale.CondensedRing.isIso_toIhomIhom_integersModPowReductionAmbient_of_etale`: if étale
  Verdier biduality holds on `Dctf(X_ét, Λ)`, then the double-dual morphism of `R K₀` relative to
  `R ω_{X, 𝒪_E}` is an isomorphism.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory MonoidalClosed

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] (E : PadicAlgCl.FiniteIntermediateField ℓ) (n : ℕ)

variable {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom]

attribute [local instance] DerivedCategory.braidedCategory'

/-- **Finite-coefficient biduality on the reductions of integral complexes** (blueprint
`det-pd-biduality-coefficients`, (i)): if étale Verdier biduality holds on `Dctf(X_ét, Λ)`,
`Λ = 𝒪_E ⧸ ℓⁿ`, then for every bounded constructible `𝒪_E`-complex `K₀` the double-dual morphism
of its reduction `R K₀`, relative to the reduction `R ω_{X, 𝒪_E}` of the integral dualizing
complex, is an isomorphism. -/
theorem isIso_toIhomIhom_integersModPowReductionAmbient_of_etale
    (hét : ∀ {M : DerivedCategory (Sheaf X.left.smallEtaleTopology
        (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E.1 n)))},
      Etale.DerivedCategory.constructibleFiniteTor
        (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E.1 n)) X.left M →
      IsIso ((Etale.verdierDualDoubleDual (integersModPowCoeff.{u} ℓ E.1 n) X.hom).app M))
    (K₀ : Dᵇc(X.left)⟦Profinite.padicIntegersRingObj ℓ E.1⟧) :
    IsIso (toIhomIhom
      ((integersModPowReductionAmbient ℓ E n X).obj (PadicIntegersRingObj.dualizingComplex ℓ E.1 X))
      ((integersModPowReductionAmbient ℓ E n X).obj K₀)) :=
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
