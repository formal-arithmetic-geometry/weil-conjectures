/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ConstructibleSheafRegularDevissage
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UniformExtBoundPadicAlgCl
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UniformExtBoundRational
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LisseLattice
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LocallyFreeConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LocallyFreeOfFinitelyPresentedField

/-!
# The uniform `Ext` bound for constructible `E`-sheaves, from `𝒪_E`, by dévissage

Blueprint `det-uniform-constructible-ext-rational`, coefficients `E`. Let `E ⊆ ℚ̄_ℓ` be a finite
subextension of `ℚ_ℓ` and `X` a noetherian scheme locally of finite type over a perfect field. If
constructible `𝒪_{E,X}`-modules satisfy the uniform `Ext` bound and `Hom(M[0], -[q])` factors
through filtered colimits for constructible `𝒪_{E,X}`-modules `M`, then constructible
`E_X`-modules satisfy the uniform `Ext` bound
(`ProEtale.hasUniformConstructibleExtBound_continuousMapRingObj_of_padicIntegersRingObj`).

Both arguments of `Hom(M[0], B[n])` are dévissé to the generators `Rc_* j_! Rc'_* L`, `L` a lisse
`E`-module on a connected regular noetherian scheme
(`ProEtale.CondensedRing.prop_singleFunctor_of_isConstructibleModuleObject_of_perfectField`). Such
`L` has a lattice (`ProEtale.exists_isLocallyFree_padicIntegers_extendScalars_iso`), so the
generators are `E ⊗ G₀` placed in degree `0` for constructible `𝒪_{E,X}`-modules `G₀`
(`ProEtale.exists_iso_singleFunctor_extendScalars_padicIntegersToPadicSubfield_of_lowerShriek`).
The classes of objects with a uniform vanishing are closed under extensions, and
`Ext^q_E(E ⊗ M₀, E ⊗ B₀)` is computed over `𝒪_E`
(`ProEtale.eq_zero_of_extendScalars_padicIntegersToPadicSubfield`). This does not use integral
models of bounded constructible `E`-complexes.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Pretriangulated

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open Scheme PadicAlgCl CondensedRing

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : FiniteIntermediateField ℓ)

end AlgebraicGeometry.ProEtale
