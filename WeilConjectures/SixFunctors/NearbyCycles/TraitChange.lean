/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.NearbyCycles.HomComp
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension
public import WeilConjectures.RingTheory.ProEtale.StrictlyHenselianRetraction

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

## Unfinished

The theorem is `sorry`ed. Its proof is Deligne's induction above, run jointly with the finiteness
of nearby cycles: step (A) needs the generic slicing identification of Lemme 3.4 (Hochschild–Serre
for the pro-`p` kernel, for pro-étale `ℚ̄_ℓ`-sheaves) and the finite-support criterion for
complexes not yet known to be bounded constructible; step (B) needs proper base change and the
proper exchange of nearby cycles. The trait case and the case of models finite over the trait
are proved for `Spec K⟦t⟧ ⟶ Spec k'⟦t⟧` on `trace2/nearby-slice-trait` (#1777).

-/

@[expose] public section

universe u

open CategoryTheory Limits IsLocalRing

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

namespace NearbyCyclesModel.Hom

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

/-- **Invariance of nearby cycles under change of strictly henselian trait** (SGA 4½,
[Th. finitude], Prop. 3.7). Let `ι : R₁ ⟶ R₂` be an injective local homomorphism of strictly
henselian discrete valuation rings, with compatible maps `aᵢ : Rᵢ ⟶ Ωᵢ` to algebraically closed
fields (`c ∘ a₁ = a₂ ∘ ι`) and maps `bᵢ : Rᵢ ⟶ κᵢ` with kernel the maximal ideal to separably
closed fields, `ℓ` invertible in `κ₁`. Let `N` be a model separated and of finite type over
`S₁ = Spec R₁` along `q₁` (generic fibre over `Spec Ω₁`, special fibre over `Spec κ₁`), `M` a
model over `S₂ = Spec R₂` along `q₂`, and `φ : M ⟶ N` a morphism of models whose square of total
spaces over `Spec ι` is cartesian and whose map of generic fibres lies over `Spec c`. Then the
pullback exchange `α : Lf'^* Ψ_N B ⟶ Ψ_M (Lf^* B)` is an isomorphism for every `B` whose
restriction `Lε^* B` to the geometric generic fibre of `N` is bounded constructible.
See the module docstring; `sorry`ed. -/
theorem isIso_pullbackExchange_app_of_isPullback_trait [IsLocalHom ι]
    (hι : Function.Injective ι) (ha₁ : Function.Injective a₁) (ha₂ : Function.Injective a₂)
    (hc : c.comp a₁ = a₂.comp ι) (hb₁ : RingHom.ker b₁ = maximalIdeal R₁)
    (hb₂ : RingHom.ker b₂ = maximalIdeal R₂) [Fact (ringChar κ₁ ≠ ℓ)]
    (φ : M.Hom N f f') (q₁ : N.total ⟶ Spec (.of R₁)) [LocallyOfFiniteType q₁]
    [QuasiCompact q₁] [IsSeparated q₁] (g₁ : N.generic ⟶ Spec (.of Ω₁))
    (hNj : IsPullback N.j g₁ q₁ (Spec.map (CommRingCat.ofHom a₁))) (p₁ : Y' ⟶ Spec (.of κ₁))
    (hNi : IsPullback N.i p₁ q₁ (Spec.map (CommRingCat.ofHom b₁)))
    (q₂ : M.total ⟶ Spec (.of R₂)) (g₂ : M.generic ⟶ Spec (.of Ω₂))
    (hMj : IsPullback M.j g₂ q₂ (Spec.map (CommRingCat.ofHom a₂))) (p₂ : X' ⟶ Spec (.of κ₂))
    (hMi : IsPullback M.i p₂ q₂ (Spec.map (CommRingCat.ofHom b₂)))
    (hφ : IsPullback φ.total q₂ q₁ (Spec.map (CommRingCat.ofHom ι)))
    (hgen : φ.generic ≫ g₁ = g₂ ≫ Spec.map (CommRingCat.ofHom c))
    {B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Y))}
    (hB : boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) N.generic)
      (L((N.ε)^*⟦Profinite.padicAlgClRingObj ℓ⟧).obj B)) :
    IsIso ((φ.pullbackExchange (Profinite.padicAlgClRingObj ℓ)).app B) :=
  sorry

end NearbyCyclesModel.Hom

end AlgebraicGeometry.ProEtale.CondensedRing
