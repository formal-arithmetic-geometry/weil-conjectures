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

/-- Blueprint `sk-rem-sf-kv-formal` (also `rem-sf-kv-formal`): What is formal and what is not.

For `X`, `Y` separated of finite type over an algebraically closed field `k` and a finite
coefficient ring `Λ` whose exponent is invertible in `k`, the Künneth–Verdier isomorphism
`M ⊠ 𝔻_Y N ≅ RHom(p_Y^* N, Rp_X^! M)` holds for all `M ∈ Dctf(X, Λ)` and `N ∈ Dctf(Y, Λ)` if and
only if Verdier duality commutes with the external product,
`𝔻_{X×Y}(M ⊠ N) ≅ 𝔻_X M ⊠ 𝔻_Y N`, for all of them. Both directions are formal: biduality, the
preservation of `Dctf` by `𝔻_X`, and
`AlgebraicGeometry.Etale.nonempty_iso_derivedHom_rightDerivedUpperShriek_verdierDual`, which
rewrites `RHom(p_Y^* N, Rp_X^! M)` as `𝔻_{X×Y}(𝔻_X M ⊠ N)`. The non-formal content is the
statement itself; at `M = Λ_X`, `N = Λ_Y` it reads `ω_{X×Y} ≅ ω_X ⊠ ω_Y`. -/
theorem kunnethVerdier_iff_verdierDual_externalProduct :
    (∀ {M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
        {N : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))},
        constructibleFiniteTor (ModuleCat.{u + 1} Λ) X M →
        constructibleFiniteTor (ModuleCat.{u + 1} Λ) Y N →
        Nonempty (externalProduct (ModuleCat.{u + 1} Λ) a b M
            ((verdierDual (ModuleCat.{u + 1} Λ) b).obj (op N)) ≅
          (RHom(pullback a b)[ModuleCat.{u + 1} Λ].obj
              (op ((L((pullback.snd a b)^*[ModuleCat.{u + 1} Λ])).obj N))).obj
            ((R(pullback.fst a b)^![ModuleCat.{u + 1} Λ]).obj M))) ↔
      ∀ {M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
        {N : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))},
        constructibleFiniteTor (ModuleCat.{u + 1} Λ) X M →
        constructibleFiniteTor (ModuleCat.{u + 1} Λ) Y N →
        Nonempty ((verdierDual (ModuleCat.{u + 1} Λ) (pullback.fst a b ≫ a)).obj
            (op (externalProduct (ModuleCat.{u + 1} Λ) a b M N)) ≅
          externalProduct (ModuleCat.{u + 1} Λ) a b
            ((verdierDual (ModuleCat.{u + 1} Λ) a).obj (op M))
            ((verdierDual (ModuleCat.{u + 1} Λ) b).obj (op N))) := by
  -- `M ≅ 𝔻𝔻M` transported into the first factor of the external product
  have hext (M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
      (hM : constructibleFiniteTor (ModuleCat.{u + 1} Λ) X M)
      (N : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
      Nonempty (externalProduct (ModuleCat.{u + 1} Λ) a b M N ≅
        externalProduct (ModuleCat.{u + 1} Λ) a b ((verdierDual (ModuleCat.{u + 1} Λ) a).obj
          (op ((verdierDual (ModuleCat.{u + 1} Λ) a).obj (op M)))) N) := by
    obtain ⟨β⟩ := nonempty_iso_verdierDual_verdierDual Λ a hM
    exact ⟨((derivedTensor _ _).mapIso
      ((L((pullback.fst a b)^*[ModuleCat.{u + 1} Λ])).mapIso β)).app _⟩
  constructor
  · intro hκ M N hM hN
    have hDM := constructibleFiniteTor_verdierDual Λ a hM
    obtain ⟨κ⟩ := hκ hDM hN
    obtain ⟨φ⟩ := nonempty_iso_derivedHom_rightDerivedUpperShriek_verdierDual Λ a b hDM N
    obtain ⟨β⟩ := hext M hM N
    exact ⟨(verdierDual (ModuleCat.{u + 1} Λ) (pullback.fst a b ≫ a)).mapIso β.symm.op ≪≫
      φ.symm ≪≫ κ.symm⟩
  · intro hδ M N hM hN
    have hDM := constructibleFiniteTor_verdierDual Λ a hM
    obtain ⟨δ⟩ := hδ hDM hN
    obtain ⟨φ⟩ := nonempty_iso_derivedHom_rightDerivedUpperShriek_verdierDual Λ a b hM N
    obtain ⟨β⟩ := hext M hM ((verdierDual (ModuleCat.{u + 1} Λ) b).obj (op N))
    exact ⟨β ≪≫ δ.symm ≪≫ φ.symm⟩

end AlgClosed

/-- Blueprint `sk-rem-sf-kv-formal`: the formal case of duality of external products.

If the dualizing complexes satisfy `ω_{X×Y} ≅ ω_X ⊠ ω_Y` (the constant-coefficient exceptional
Künneth isomorphism), then for **dualizable** `M` and `N` (for instance perfect complexes on
smooth `X`, `Y`) Verdier duality commutes with the external product,
`𝔻_{X×Y}(M ⊠ N) ≅ 𝔻_X M ⊠ 𝔻_Y N`: internal homs out of dualizable objects commute with the
external product (`AlgebraicGeometry.Etale.nonempty_iso_externalProduct_derivedHom_of_isDualizable`).
As the blueprint stresses, this perfect case is the base of the induction, not a substitute
for it. -/
theorem nonempty_iso_verdierDual_externalProduct_of_isDualizable {S X Y : Scheme.{u}}
    (a : X ⟶ S) (b : Y ⟶ S) [HasCompactification a] [HasCompactification b]
    [HasCompactification (pullback.fst a b ≫ a)]
    {M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    {N : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hM : IsDualizable M) (hN : IsDualizable N)
    (hω : Nonempty (dualizingComplex (ModuleCat.{u + 1} Λ) (pullback.fst a b ≫ a) ≅
      externalProduct (ModuleCat.{u + 1} Λ) a b (dualizingComplex _ a) (dualizingComplex _ b))) :
    Nonempty ((verdierDual (ModuleCat.{u + 1} Λ) (pullback.fst a b ≫ a)).obj
        (op (externalProduct (ModuleCat.{u + 1} Λ) a b M N)) ≅
      externalProduct (ModuleCat.{u + 1} Λ) a b
        ((verdierDual (ModuleCat.{u + 1} Λ) a).obj (op M))
        ((verdierDual (ModuleCat.{u + 1} Λ) b).obj (op N))) := by
  obtain ⟨ω⟩ := hω
  obtain ⟨e⟩ := nonempty_iso_externalProduct_derivedHom_of_isDualizable (ModuleCat.{u + 1} Λ) a b
    (N₁ := dualizingComplex _ a) (N₂ := dualizingComplex _ b) hM hN
  exact ⟨((RHom(pullback a b)[ModuleCat.{u + 1} Λ]).obj _).mapIso ω ≪≫ e.symm⟩

end Etale

end AlgebraicGeometry
