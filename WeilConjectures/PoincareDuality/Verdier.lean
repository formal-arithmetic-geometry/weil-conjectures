/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Braided
public import WeilConjectures.PoincareDuality.ProjectionFormula
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriek

/-!

# Verdier duality on bounded constructible complexes on the pro-étale site

Let `Λ` be a commutative condensed ring (in practice `ℚ̲̄_ℓ`), `k` a field of characteristic
`≠ ℓ` and `f : X ⟶ Y` a morphism of separated `k`-schemes of finite type, a morphism of
`Over (Spec (.of k))`. This file specializes
the abstract constructions of `WeilConjectures.PoincareDuality.Abstract` to the six functors on
the bounded constructible derived categories `Dᵇc(X)⟦Λ⟧`: the adjunctions `Lf^* ⊣ Rf_*` and
`Rf_! ⊣ Rf^!`, the internal hom `RHom` and the derived exceptional projection morphism `PF^!` of
`WeilConjectures.PoincareDuality.ProjectionFormula`.

The exceptional inverse image `Rf^!` only exists on `Dᵇc`
(`ProEtale.CondensedRing.boundedConstructibleUpperShriek`), and requires `Rg_*` along the proper
half of the chosen compactification to be a left adjoint; this is an instance argument here
(provided for `ℚ̲̄_ℓ` by
`ProEtale.CondensedRing.isLeftAdjoint_boundedConstructibleLowerStar_padicAlgClRingObj`). The
monoidal closed structure on `Dᵇc` is that of
`ProEtale.CondensedRing.isMonoidal_boundedConstructible` and
`ProEtale.CondensedRing.isMonoidalClosed_boundedConstructible`.

## Main definitions

- `ProEtale.CondensedRing.verdierExchange`: the Verdier exchange morphism
  `Φ_{f,K,L} : Rf_* RHom(K, Rf^! L) ⟶ RHom(Rf_! K, L)`.
- `ProEtale.CondensedRing.dualizingComplex`: for a structure morphism `a : X ⟶ S`, the
  dualizing complex `ω_X = Ra^! Λ_S`, and `ProEtale.CondensedRing.verdierDual`: the Verdier
  dual `𝔻_X K = RHom(K, ω_X)`.
- `ProEtale.CondensedRing.verdierBiduality`: the double-dual morphism `δ_K : K ⟶ 𝔻_X 𝔻_X K`.
- `ProEtale.CondensedRing.absoluteVerdierExchange` and
  `ProEtale.CondensedRing.dualVerdierExchange`: for an `S`-morphism `f` and a given
  identification `γ : Rf^! ω_Y ≅ ω_X`, the absolute exchange `Rf_* 𝔻_X K ⟶ 𝔻_Y Rf_! K` and the
  opposite exchange `Θ_K : Rf_! 𝔻_X K ⟶ 𝔻_Y Rf_* K`.

The identification `γ` is taken as an argument: it is an instance of the composition
isomorphism `R(f ≫ a_Y)^! ≅ Ra_Y^! ⋙ Rf^!` for exceptional inverse images, which depends on the
compatibility of the chosen compactifications and is not yet available.

## Main results

- `ProEtale.CondensedRing.isIso_verdierExchange`: **Verdier duality**, the exchange morphism
  is an isomorphism, deduced from the derived projection formula
  (`isIso_boundedConstructibleExceptionalProjectionMorphism`) by the Yoneda argument.

## Sorried input

- `ProEtale.CondensedRing.isIso_verdierBiduality`: **constructible biduality**, `δ_K` is an
  isomorphism for `K` bounded constructible (Input 3.3 of the specification).

-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory MonoidalClosed

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]

/-! ### The Verdier exchange morphism -/

section Exchange

variable {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom]
  (f : X ⟶ Y)
  [(boundedConstructibleLowerStar Λ ℓ (compactificationOverField f).overG).IsLeftAdjoint]

/-- The **Verdier exchange morphism** `Φ_{f,K,L} : Rf_* RHom(K, Rf^! L) ⟶ RHom(Rf_! K, L)` on
bounded constructible complexes: the transpose of the pairing
```
Rf_! K ⊗ᴸ Rf_* RHom(K, Rf^! L) ⟶ Rf_! (K ⊗ᴸ Lf^* Rf_* RHom(K, Rf^! L))
  ⟶ Rf_! (K ⊗ᴸ RHom(K, Rf^! L)) ⟶ Rf_! Rf^! L ⟶ L,
```
see `CategoryTheory.Verdier.exchange`. -/
noncomputable def verdierExchange (K : Dᵇc(X.left)⟦Λ⟧) (L : Dᵇc(Y.left)⟦Λ⟧) :
    (boundedConstructibleLowerStar Λ ℓ f).obj
        ((ihom K).obj ((boundedConstructibleUpperShriek Λ ℓ f).obj L)) ⟶
      (ihom ((boundedConstructibleLowerShriek Λ ℓ f).obj K)).obj L :=
  Verdier.exchange (boundedConstructibleUpperStarLowerStarAdjunction Λ ℓ f)
    (boundedConstructibleUpperShriekAdjunction Λ ℓ f)
    (boundedConstructibleExceptionalProjection Λ ℓ f) K L

/-- **Verdier duality**: the exchange morphism `Φ_{f,K,L}` is an isomorphism, by the derived
projection formula and the Yoneda lemma. -/
theorem isIso_verdierExchange (K : Dᵇc(X.left)⟦Λ⟧) (L : Dᵇc(Y.left)⟦Λ⟧) :
    IsIso (verdierExchange Λ ℓ f K L) :=
  Verdier.isIso_exchange_of_isIso _ _ _ K L

end Exchange

/-! ### The dualizing complex and the double-dual morphism -/

section Dualizing

variable {X S : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType S.hom]
  [QuasiCompact S.hom] [IsSeparated S.hom]
  (a : X ⟶ S)
  [(boundedConstructibleLowerStar Λ ℓ (compactificationOverField a).overG).IsLeftAdjoint]

/-- The **dualizing complex** `ω_X = Ra^! Λ_S` of `X` relative to the structure morphism
`a : X ⟶ S`. -/
noncomputable def dualizingComplex : Dᵇc(X.left)⟦Λ⟧ :=
  (boundedConstructibleUpperShriek Λ ℓ a).obj (𝟙_ _)

/-- The **Verdier dual** `𝔻_X K = RHom(K, ω_X)` relative to the structure morphism `a : X ⟶ S`. -/
noncomputable def verdierDual (K : Dᵇc(X.left)⟦Λ⟧) : Dᵇc(X.left)⟦Λ⟧ :=
  (ihom K).obj (dualizingComplex Λ ℓ a)

/-- The **double-dual morphism** `δ_K : K ⟶ 𝔻_X 𝔻_X K`: the transpose of the evaluation pairing
`𝔻_X K ⊗ᴸ K ⟶ K ⊗ᴸ 𝔻_X K ⟶ ω_X`. -/
noncomputable def verdierBiduality (K : Dᵇc(X.left)⟦Λ⟧) :
    K ⟶ verdierDual Λ ℓ a (verdierDual Λ ℓ a K) :=
  Verdier.bidualityMap (dualizingComplex Λ ℓ a) K

/-- **Constructible Verdier biduality**: the double-dual morphism `δ_K` is an isomorphism for
`K` bounded constructible. See the module docstring. -/
theorem isIso_verdierBiduality (K : Dᵇc(X.left)⟦Λ⟧) : IsIso (verdierBiduality Λ ℓ a K) :=
  sorry

end Dualizing

/-! ### The absolute and opposite exchange morphisms -/

section Absolute

variable {X Y S : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom] [LocallyOfFiniteType S.hom] [QuasiCompact S.hom]
  [IsSeparated S.hom]
  (f : X ⟶ Y) (aX : X ⟶ S) (aY : Y ⟶ S)
  [(boundedConstructibleLowerStar Λ ℓ (compactificationOverField f).overG).IsLeftAdjoint]
  [(boundedConstructibleLowerStar Λ ℓ (compactificationOverField aX).overG).IsLeftAdjoint]
  [(boundedConstructibleLowerStar Λ ℓ (compactificationOverField aY).overG).IsLeftAdjoint]
  (γ : (boundedConstructibleUpperShriek Λ ℓ f).obj (dualizingComplex Λ ℓ aY) ≅
    dualizingComplex Λ ℓ aX)

/-- The **absolute Verdier exchange morphism** `Rf_* 𝔻_X K ⟶ 𝔻_Y Rf_! K`, given an
identification `γ : Rf^! ω_Y ≅ ω_X`: the exchange morphism `Φ_{f,K,ω_Y}` precomposed with
`γ⁻¹`. -/
noncomputable def absoluteVerdierExchange (K : Dᵇc(X.left)⟦Λ⟧) :
    (boundedConstructibleLowerStar Λ ℓ f).obj (verdierDual Λ ℓ aX K) ⟶
      verdierDual Λ ℓ aY ((boundedConstructibleLowerShriek Λ ℓ f).obj K) :=
  Verdier.absoluteExchange (boundedConstructibleUpperStarLowerStarAdjunction Λ ℓ f)
    (boundedConstructibleUpperShriekAdjunction Λ ℓ f)
    (boundedConstructibleExceptionalProjection Λ ℓ f)
    (dualizingComplex Λ ℓ aX) (dualizingComplex Λ ℓ aY) γ K

/-- The **opposite Verdier exchange morphism** `Θ_K : Rf_! 𝔻_X K ⟶ 𝔻_Y Rf_* K`, given an
identification `γ : Rf^! ω_Y ≅ ω_X`: the double-dual morphism of `Rf_! 𝔻_X K`, followed by the
dual of `Rf_* K ⟶ Rf_* 𝔻_X 𝔻_X K ⟶ 𝔻_Y Rf_! 𝔻_X K`. The familiar `𝔻_Y Rf_* K ≅ Rf_! 𝔻_X K` is its
inverse, when it is invertible. -/
noncomputable def dualVerdierExchange (K : Dᵇc(X.left)⟦Λ⟧) :
    (boundedConstructibleLowerShriek Λ ℓ f).obj (verdierDual Λ ℓ aX K) ⟶
      verdierDual Λ ℓ aY ((boundedConstructibleLowerStar Λ ℓ f).obj K) :=
  Verdier.dualExchange (boundedConstructibleUpperStarLowerStarAdjunction Λ ℓ f)
    (boundedConstructibleUpperShriekAdjunction Λ ℓ f)
    (boundedConstructibleExceptionalProjection Λ ℓ f)
    (dualizingComplex Λ ℓ aX) (dualizingComplex Λ ℓ aY) γ K

end Absolute

end AlgebraicGeometry.ProEtale.CondensedRing
