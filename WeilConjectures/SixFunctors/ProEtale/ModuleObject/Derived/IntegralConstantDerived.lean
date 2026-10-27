/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Tensor
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.IntegralLisseLocalStructure

/-!
# Derived tensor products and duals of constant `𝒪_E`-modules

Let `E ⊆ ℚ̄_ℓ` be a finite subextension of `ℚ_ℓ` with uniformizer `ϖ`, and let
`C = ⊕ⱼ 𝒪_E/ϖ^{eⱼ} ⊕ 𝒪_E^r` be a constant module object over `𝒪_{E,V}` on a scheme `V`
(`ProEtale.integralConstantModule`). Each `𝒪_E/ϖ^e` has the free resolution
`𝒪_E --ϖ^e--> 𝒪_E`, so:

* the derived tensor product `C[0] ⊗ᴸ C'[0]` of two constant modules has locally finitely
  presented cohomology sheaves (the constant modules `Tor_i^{𝒪_E}`), concentrated in degrees
  `-1` and `0` (`ProEtale.CondensedRing.integralConstantModule_tensorObj_homology`);
* `C[q]` is dualizable in `D(Mod_{𝒪_{E,V}})`, with a bounded dual whose cohomology sheaves are
  locally finitely presented (`ProEtale.CondensedRing.exists_exactPairing_integralConstantModule`).

This file does not import
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E]
  [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E]
  (V : Scheme.{u}) (ϖ : PadicAlgCl.integers ℓ E)
  (hϖ : IsLocalRing.maximalIdeal (PadicAlgCl.integers ℓ E) = Ideal.span {ϖ})

include hϖ in
/-- The derived tensor product of two constant `𝒪_E`-modules placed in degree `0` has locally
finitely presented cohomology sheaves, concentrated in degrees `-1` and `0`. -/
theorem integralConstantModule_tensorObj_homology (k r k' r' : ℕ) (e : Fin k → ℕ)
    (e' : Fin k' → ℕ) (n : ℤ) :
    IsLocallyFinitelyPresented (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) V)
        ((DerivedCategory.homologyFunctor _ n).obj
          ((DerivedCategory.singleFunctor _ 0).obj (integralConstantModule ℓ E V ϖ k r e) ⊗
            (DerivedCategory.singleFunctor _ 0).obj (integralConstantModule ℓ E V ϖ k' r' e'))) ∧
      ((n < -1 ∨ 0 < n) → IsZero ((DerivedCategory.homologyFunctor _ n).obj
          ((DerivedCategory.singleFunctor _ 0).obj (integralConstantModule ℓ E V ϖ k r e) ⊗
            (DerivedCategory.singleFunctor _ 0).obj (integralConstantModule ℓ E V ϖ k' r' e')))) :=
  sorry

include hϖ in
/-- A constant `𝒪_E`-module placed in degree `q` is dualizable in `D(Mod_{𝒪_{E,V}})`, with a
bounded left dual whose cohomology sheaves are locally finitely presented. -/
theorem exists_exactPairing_integralConstantModule (k r : ℕ) (e : Fin k → ℕ) (q : ℤ) :
    ∃ D : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology V) Ab.{u + 1})
        (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) V)),
      DerivedCategory.TStructure.t.bounded D ∧
      (∀ n, IsLocallyFinitelyPresented (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) V)
        ((DerivedCategory.homologyFunctor _ n).obj D)) ∧
      Nonempty (ExactPairing D
        ((DerivedCategory.singleFunctor _ q).obj (integralConstantModule ℓ E V ϖ k r e))) :=
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
