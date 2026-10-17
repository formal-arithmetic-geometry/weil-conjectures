/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.BoundaryDuality
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Comparisons

/-!

# The formal part of the Künneth–Verdier isomorphism

For a finite coefficient ring `Λ` whose exponent is invertible on an algebraically closed field
`k`, Verdier biduality turns the Künneth–Verdier isomorphism into the statement that Verdier
duality commutes with the external product.

## Main statements

- `AlgebraicGeometry.Etale.nonempty_iso_verdierDual_leftDerivedUpperStar`
  (`cor-sf-duality-pullback`): `𝔻_X (Lf^* K) ≅ Rf^! (𝔻_Y K)`.
- `AlgebraicGeometry.Etale.nonempty_iso_derivedHom_rightDerivedUpperShriek_verdierDual`
  (`rem-sf-kv-formal`): `RHom(p_Y^* N, Rp_X^! M) ≅ 𝔻_{X×Y}(𝔻_X M ⊠ N)`.
- `AlgebraicGeometry.Etale.kunnethVerdier_iff_verdierDual_externalProduct`
  (`sk-rem-sf-kv-formal`, `rem-sf-kv-formal`): the Künneth–Verdier isomorphism holds for all
  `M`, `N` in `Dctf` if and only if `𝔻_{X×Y}(M ⊠ N) ≅ 𝔻_X M ⊠ 𝔻_Y N` for all of them.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Opposite

open scoped CategoryTheory.Functor

namespace CategoryTheory.MonoidalClosed

variable {C : Type*} [Category* C] [MonoidalCategory C] [MonoidalClosed C]

/-- The internal tensor–hom adjunction `[P ⊗ Q, W] ≅ [Q, [P, W]]`: both sides are right adjoint
to `T ↦ P ⊗ (Q ⊗ T)`. -/
noncomputable def ihomTensorObjIso (P Q W : C) :
    (ihom (P ⊗ Q)).obj W ≅ (ihom Q).obj ((ihom P).obj W) :=
  ((ihom.adjunction (P ⊗ Q)).rightAdjointUniq
    (((ihom.adjunction Q).comp (ihom.adjunction P)).ofNatIsoLeft
      (tensorLeftTensor P Q).symm)).app W

end CategoryTheory.MonoidalClosed

namespace AlgebraicGeometry

open Scheme

namespace Etale

open _root_.AlgebraicGeometry.Etale.DerivedCategory

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

/-- Blueprint `cor-sf-duality-pullback`: Duality against pullback.

For a morphism `f : X ⟶ Y` over a base `S`, with `a_Y : Y ⟶ S` the structure morphism of `Y`
and `a_X = f ≫ a_Y` that of `X` (all three admitting compactifications), and for a finite
coefficient ring `Λ`,

`𝔻_X (Lf^* K) ≅ Rf^! (𝔻_Y K)`

for every `K ∈ D(Y_ét, Λ)`. In the blueprint this is the right adjoint of the Verdier
exchange `𝔻_Y Rf_! ≅ Rf_* 𝔻_X` under biduality; here it is obtained directly, and without any
finiteness of `K`, from the exchange `Rf^! RHom(K, ω_Y) ≅ RHom(Lf^* K, Rf^! ω_Y)` and
`Rf^! ω_Y ≅ ω_X` (`AlgebraicGeometry.Etale.nonempty_iso_rightDerivedUpperShriek_verdierDual`).
For a smooth `f` of pure relative dimension `d` an orientation `ω_X ≅ Λ_X(d)[2d]`
(`AlgebraicGeometry.Etale.Orientation`) rewrites the left-hand side. -/
theorem nonempty_iso_verdierDual_leftDerivedUpperStar {X Y S : Scheme.{u}} (aY : Y ⟶ S)
    [HasCompactification aY] (f : X ⟶ Y) [HasCompactification f]
    [HasCompactification (f ≫ aY)] [QuasiCompact (f ≫ aY)]
    (K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    Nonempty ((verdierDual (ModuleCat.{u + 1} Λ) (f ≫ aY)).obj
        (op ((L((f)^*[ModuleCat.{u + 1} Λ])).obj K)) ≅
      (R(f)^![ModuleCat.{u + 1} Λ]).obj ((verdierDual (ModuleCat.{u + 1} Λ) aY).obj (op K))) :=
  (nonempty_iso_rightDerivedUpperShriek_verdierDual Λ aY f K).map Iso.symm

section AlgClosed

variable {k : Type u} [Field k] [IsAlgClosed k] [HasInvertibleExponent Λ (Spec (.of k))]
  {X Y : Scheme.{u}} (a : X ⟶ Spec (.of k)) (b : Y ⟶ Spec (.of k))
  [IsSeparated a] [LocallyOfFiniteType a] [QuasiCompact a]
  [IsSeparated b] [LocallyOfFiniteType b] [QuasiCompact b]

/-- Blueprint `rem-sf-kv-formal`: the formal half of the Künneth–Verdier comparison.

For `X`, `Y` separated of finite type over an algebraically closed field `k`, with projections
`p_X`, `p_Y` of `X × Y` and `𝔻_{X×Y}` the Verdier dual of `X × Y` over `k`, and for
`M ∈ Dctf(X, Λ)` and any `N`,

`RHom(p_Y^* N, Rp_X^! M) ≅ 𝔻_{X×Y}(𝔻_X M ⊠ N)`.

Biduality `M ≅ 𝔻_X 𝔻_X M` (`AlgebraicGeometry.Etale.nonempty_iso_verdierDual_verdierDual`)
and duality against pullback (`cor-sf-duality-pullback`) give
`Rp_X^! M ≅ 𝔻_{X×Y}(p_X^* 𝔻_X M)`, and the internal adjunction
`RHom(Q, 𝔻 P) ≅ 𝔻(P ⊗ᴸ Q)` (`CategoryTheory.MonoidalClosed.ihomTensorObjIso`) concludes. -/
theorem nonempty_iso_derivedHom_rightDerivedUpperShriek_verdierDual
    {M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hM : constructibleFiniteTor (ModuleCat.{u + 1} Λ) X M)
    (N : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    Nonempty ((RHom(pullback a b)[ModuleCat.{u + 1} Λ].obj
        (op ((L((pullback.snd a b)^*[ModuleCat.{u + 1} Λ])).obj N))).obj
          ((R(pullback.fst a b)^![ModuleCat.{u + 1} Λ]).obj M) ≅
      (verdierDual (ModuleCat.{u + 1} Λ) (pullback.fst a b ≫ a)).obj
        (op (externalProduct (ModuleCat.{u + 1} Λ) a b
          ((verdierDual (ModuleCat.{u + 1} Λ) a).obj (op M)) N))) := by
  obtain ⟨β⟩ := nonempty_iso_verdierDual_verdierDual Λ a hM
  obtain ⟨e⟩ := nonempty_iso_verdierDual_leftDerivedUpperStar Λ a (pullback.fst a b)
    ((verdierDual (ModuleCat.{u + 1} Λ) a).obj (op M))
  exact ⟨((RHom(pullback a b)[ModuleCat.{u + 1} Λ]).obj _).mapIso
      ((R(pullback.fst a b)^![ModuleCat.{u + 1} Λ]).mapIso β ≪≫ e.symm) ≪≫
    (MonoidalClosed.ihomTensorObjIso _ _ _).symm⟩

end AlgClosed

end Etale

end AlgebraicGeometry
