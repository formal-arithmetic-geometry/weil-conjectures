/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.GenericFibre.SeparatedDirectImage
public import WeilConjectures.SixFunctors.Etale.Derived.GenericFibre.ClosedSupport
public import WeilConjectures.SixFunctors.Etale.Derived.GenericFibre.InternalHomGeneric

/-!
# Restriction to the generic fibre

Let `S` be an integral scheme of finite type over a field `k`, let `Λ` be a finite ring whose
exponent is invertible on `S`, and let `t : T ⟶ S` be a morphism from a noetherian scheme lying
over the generic point of `S`, for instance a geometric generic point. For `X` of finite type
over `S`, with base change `g : X_T ⟶ X`, pulling back along `g` commutes with the derived direct
image along a separated morphism of finite type, with the exceptional inverse image along a
closed immersion and with the internal Hom out of a constructible complex of finite Tor
dimension (`AlgebraicGeometry.Etale.isIso_baseChangeComparisons_of_generic`).

## Main statements

- `AlgebraicGeometry.Etale.isIso_baseChangeComparisons_of_generic`
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

/-- **Restriction to the generic fibre.** Let `S` be integral and of finite type over a field
`k`, let `Λ` be a finite ring whose exponent is invertible on `S`, and let `t : T ⟶ S` be a
morphism from a noetherian scheme lying over the generic point of `S`. Let `X` be of finite type
over `S`, with base change `g : X_T ⟶ X`, let `h : W ⟶ X` be a separated morphism of finite type
and `i : Z ⟶ X` a closed immersion, with base changes `h_T` and `i_T` along `g`. Let `L` on `W`
and `M` on `X` be bounded constructible and `K` on `X` constructible of finite Tor dimension.
Then the three comparison maps
* `g^* Rh_* L ⟶ Rh_{T,*} g_W^* L`,
* `g_Z^* Ri^! M ⟶ Ri_T^! g^* M`,
* `g^* RHom(K, M) ⟶ RHom(g^* K, g^* M)`

are isomorphisms. -/
theorem isIso_baseChangeComparisons_of_generic {k : Type u} [Field k]
    {S : Scheme.{u}} [IsIntegral S] (aS : S ⟶ Spec (.of k)) [LocallyOfFiniteType aS]
    [QuasiCompact aS] [HasInvertibleExponent Λ S] {T : Scheme.{u}} [IsNoetherian T] (t : T ⟶ S)
    (ht : ∀ x, t.base x = genericPoint S) {X X' : Scheme.{u}} (fX : X ⟶ S)
    [LocallyOfFiniteType fX] [QuasiCompact fX] {g : X' ⟶ X} {fT : X' ⟶ T}
    (hX : IsPullback g fT fX t) {W W' : Scheme.{u}} (h : W ⟶ X) [IsSeparated h]
    [LocallyOfFiniteType h] [QuasiCompact h] {gW : W' ⟶ W} {hT : W' ⟶ X'}
    (sqh : IsPullback gW hT h g) {Z Z' : Scheme.{u}} {i : Z ⟶ X} {iT : Z' ⟶ X'} {gZ : Z' ⟶ Z}
    [IsClosedImmersion i] [IsClosedImmersion iT] (sqi : IsPullback gZ iT i g)
    {L : _root_.DerivedCategory (Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hL : DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) W L)
    {K M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hK : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X K)
    (hM : DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) X M) :
    IsIso ((derivedBaseChangeMap (ModuleCat.{u + 1} Λ) sqh.toCommSq).app L) ∧
      IsIso ((rightDerivedUpperShriekBaseChangeMap Λ sqi).app M) ∧
      IsIso (derivedHomUpperStarComparison (ModuleCat.{u + 1} Λ) g K M) := by
  refine ⟨isIso_derivedBaseChangeMap_app_of_generic Λ aS t ht fX h hX sqh hL, ?_,
    isIso_derivedHomUpperStarComparison_of_generic Λ aS t ht fX hX hK hM⟩
  let U : X.Opens := ⟨(Set.range i.base)ᶜ, i.isClosedEmbedding.isClosed_range.isOpen_compl⟩
  have sqU := IsPullback.of_hasPullback U.ι g
  have hij : Set.range i.base = (Set.range U.ι.base)ᶜ := by simp [U]
  have hij' : Disjoint (Set.range iT.base) (Set.range (pullback.snd U.ι g).base) := by
    rw [Set.disjoint_left]
    rintro _ ⟨z, rfl⟩ ⟨u, hu⟩
    have h₁ : g.base (iT.base z) ∈ Set.range i.base :=
      ⟨gZ.base z, by rw [← Scheme.Hom.comp_apply, sqi.w, Scheme.Hom.comp_apply]⟩
    have h₂ : g.base (iT.base z) ∈ Set.range U.ι.base :=
      ⟨(pullback.fst U.ι g).base u, by
        rw [← hu, ← Scheme.Hom.comp_apply, sqU.w, Scheme.Hom.comp_apply]⟩
    rw [hij] at h₁
    exact h₁ h₂
  exact isIso_rightDerivedUpperShriekBaseChangeMap_app_of_generic Λ aS t ht fX hX sqi sqU hij hij'
    hM

end Etale

end AlgebraicGeometry
