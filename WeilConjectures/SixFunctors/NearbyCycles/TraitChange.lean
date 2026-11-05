/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.NearbyCycles.HomComp
public import WeilConjectures.SixFunctors.NearbyCycles.OpenExchange
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.CoefficientChangeRestricted
public import WeilConjectures.Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension
public import WeilConjectures.RingTheory.ProEtale.StrictlyHenselianRetraction
public import WeilConjectures.SixFunctors.NearbyCycles.TraitChangeInduction.Basic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.ResidueFieldEtaleOrigin
public import WeilConjectures.Tactic.TransportExact

/-!

# Invariance of nearby cycles under change of strictly henselian trait

Let `ι : R₁ ⟶ R₂` be an injective local homomorphism of strictly henselian discrete valuation
rings, so that `g : S₂ = Spec R₂ ⟶ S₁ = Spec R₁` is a morphism of strictly henselian traits, with
compatible geometric generic points `Spec Ω₂ ⟶ Spec Ω₁` (`Ωᵢ` algebraically closed) and closed
points `Spec κᵢ ⟶ Sᵢ` (`κᵢ` separably closed). Let `N` be a model of finite type over `S₁` and
`M` its base change to `S₂`, related by a morphism of models `φ : M ⟶ N` whose square of total
spaces is cartesian. Deligne's theorem (SGA 4½, [Th. finitude], Prop. 3.7) says that the
formation of nearby cycles commutes with the change of trait: the pullback exchange
`α : g_s^* Ψ_N ⟶ Ψ_M g^*` is an isomorphism on complexes whose restriction to the geometric
generic fibre is bounded constructible
(`NearbyCyclesModel.Hom.isIso_pullbackExchange_app_of_isPullback_trait`).

This is the common input of the trait-change step of Gabber's Künneth formula (for
`Spec K⟦t⟧ ⟶ Spec k'⟦t⟧`) and of the slice step of Deligne's finiteness theorem (for
`Spec K⟦t⟧ ⟶ S'`, `S'` the strict localization of `𝔸¹_S` at the generic point of its special
fibre).

## Proof outline (Deligne, loc. cit., 3.7–3.9)

By a limit argument and Zariski localization one may assume `N` affine, then projective over
`S₁`, and one argues by induction on the dimension `n` of the generic fibre. Let `C` be the cone
of `α`.
* (A) The cohomology sheaves of `C` have local sections with finite support: on the geometric
  generic fibres of the coordinate projections `X_s ⟶ 𝔸¹_s`, the nearby cycles are the
  invariants under a pro-`p` group of the nearby cycles over the strict localizations of `𝔸¹`
  (Th. finitude, Lemme 3.4), and the induction hypothesis applies to the slices, of dimension
  `n - 1`, over these strict localizations.
* (B) `RΓ(X_{s₂}, C) = 0`: by properness both sides compute the cohomology of the geometric generic
  fibres (proper base change), which is invariant under the extension `Ω₁ ⟶ Ω₂` of algebraically
  closed fields.
A complex with cohomology sheaves of finite support and no global cohomology on a proper scheme
vanishes, so `C = 0`.

## Coefficients

The theorem is deduced from its case with coefficients `𝔽_E = 𝒪_E/ϖ`
(`NearbyCyclesModel.Hom.isIso_map_exchangeRight_app_of_isPullback_trait_residueField`), the
statement proved by Deligne for torsion coefficients. The pullback exchange is invertible once the
base change morphism of `Rj_*`, restricted to the special fibre, is; an integral model of the
`ℚ̄_ℓ`-complex reduces this to `𝒪_E`-coefficients, and derived Nakayama (the complexes involved are
derived `ϖ`-complete, PR #1792) to `𝔽_E`-coefficients
(`ProEtale.CondensedRing.isIso_map_baseChangeMap_app_padicAlgCl_of_integral`).

The case of `𝔽_E`-coefficients is Deligne's induction above
(`NearbyCyclesModel.traitChangeInvariance`), which needs the change of trait to be unramified
(`𝔪_{R₂} = 𝔪_{R₁} R₂`) and the geometric generic points to be algebraic, for the slicing
argument.

-/

@[expose] public section

universe u

open CategoryTheory Limits IsLocalRing

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

namespace NearbyCyclesModel.Hom

section Abstract

end Abstract

variable {ℓ : ℕ} [Fact ℓ.Prime]
  {R₁ R₂ : Type u} [CommRing R₁] [IsDomain R₁] [IsDiscreteValuationRing R₁]
  [IsStrictlyHenselianLocalRing R₁] [CommRing R₂] [IsDomain R₂] [IsDiscreteValuationRing R₂]
  [IsStrictlyHenselianLocalRing R₂] {ι : R₁ →+* R₂}
  {Ω₁ Ω₂ : Type u} [Field Ω₁] [IsAlgClosed Ω₁] [Field Ω₂] [IsAlgClosed Ω₂]
  {a₁ : R₁ →+* Ω₁} {a₂ : R₂ →+* Ω₂} {c : Ω₁ →+* Ω₂}
  {κ₁ κ₂ : Type u} [Field κ₁] [IsSepClosed κ₁] [Field κ₂] [IsSepClosed κ₂]
  {b₁ : R₁ →+* κ₁} {b₂ : R₂ →+* κ₂}
  {X X' Y Y' : Scheme.{u}} {M : NearbyCyclesModel X X'} {N : NearbyCyclesModel Y Y'}
  {f : X ⟶ Y} {f' : X' ⟶ Y'}

end NearbyCyclesModel.Hom

end AlgebraicGeometry.ProEtale.CondensedRing
