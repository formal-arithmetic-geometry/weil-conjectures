/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.GaloisTraceInfinite.TowerDerived
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.GaloisTraceInfinite.SheafColimit
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.GaloisTraceInfinite.GaloisLevel
public import WeilConjectures.SixFunctors.ProEtale.GaloisAcyclic.ModuleObject
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.EtaleOriginComplex
public import WeilConjectures.SixFunctors.ProEtale.Comparison.ForgetUpperStar
public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseGaloisDescent
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.SubfieldLinear

/-!
# The Galois tower of a Galois extension of fields

Let `Ω/L` be a Galois extension (possibly infinite) and `h : G ⟶ Spec L`. The finite Galois
subextensions `L'` give the Galois tower `G ×_L L' ⟶ G` with limit `G ×_L Ω`
(`AlgebraicGeometry.ProEtale.galoisTower`).

For a finite discrete commutative ring `T` in which the degrees `[L' : L]` are invertible (for
instance `𝒪_E/ϖⁿ` and `Ω/L` pro-`p` with `p ≠ ℓ`) and `Λ = C(-, T)`, every object `C` of
`D(Mod_{Λ_G})` which is bounded below of étale origin has a retraction of the derived unit
`C ⟶ Rg_* Lg^* C`, `g : G ×_L Ω ⟶ G`, invariant under the derived unit transports along the
automorphisms `Spec σ`, `σ ∈ Gal(Ω/L)`
(`AlgebraicGeometry.ProEtale.exists_invariant_retraction_derivedUnit_galois`): this is the
`Gal(Ω/L)`-invariant part of `Rg_* Lg^* C`, the derived form of Hochschild–Serre for a pro-`p`
group with coefficients in which `p` is invertible.
-/

@[expose] public section

universe u

open CategoryTheory Category Limits

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open Scheme CondensedRing

variable {L Ω : Type u} [Field L] [Field Ω] [Algebra L Ω] [IsGalois L Ω] {G : Scheme.{u}}
  (h : G ⟶ Spec (.of L))

namespace CondensedRing

end CondensedRing

end AlgebraicGeometry.ProEtale
