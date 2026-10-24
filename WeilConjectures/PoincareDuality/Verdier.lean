/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Braided
public import WeilConjectures.PoincareDuality.ProjectionFormula
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ShriekComposition

/-!

# Verdier duality on bounded constructible complexes on the pro-étale site

Let `k` be a field of characteristic `≠ ℓ` and `f : X ⟶ Y` a morphism of separated `k`-schemes
of finite type, a morphism of `Over (Spec (.of k))`. This file specializes the abstract
constructions of `WeilConjectures.PoincareDuality.Abstract` to the six functors on the bounded
constructible derived categories `Dᵇc(X)⟦ℚ̲̄_ℓ⟧` with coefficients in the condensed ring `ℚ̲̄_ℓ`
(`Profinite.padicAlgClRingObj ℓ`): the adjunctions `Lf^* ⊣ Rf_*` and `Rf_! ⊣ Rf^!`, the internal
hom `RHom` and the derived exceptional projection morphism `PF^!` of
`WeilConjectures.PoincareDuality.ProjectionFormula`.

The exceptional inverse image `Rf^!` only exists on `Dᵇc`
(`ProEtale.CondensedRing.boundedConstructibleUpperShriek`), and requires `Rg_*` along the proper
half of the chosen compactification to be a left adjoint. This is why the coefficients are
`ℚ̲̄_ℓ` rather than a general condensed ring: for `ℚ̲̄_ℓ` it is the instance
`ProEtale.CondensedRing.isLeftAdjoint_boundedConstructibleLowerStar_padicAlgClRingObj`. The
monoidal closed structure on `Dᵇc` is that of
`ProEtale.CondensedRing.isMonoidal_boundedConstructible` and
`ProEtale.CondensedRing.isMonoidalClosed_boundedConstructible`.

## Main definitions

- `ProEtale.CondensedRing.verdierExchange`: the Verdier exchange morphism
  `Φ_{f,K,L} : Rf_* RHom(K, Rf^! L) ⟶ RHom(Rf_! K, L)`.
- `ProEtale.CondensedRing.dualizingComplex`: the absolute dualizing complex
  `ω_X = Ra_X^! ℚ̄_ℓ` of `X`, for its structure morphism `a_X : X ⟶ Spec k`, and
  `ProEtale.CondensedRing.verdierDual`: the Verdier dual `𝔻_X K = RHom(K, ω_X)`.
- `ProEtale.CondensedRing.verdierBiduality`: the double-dual morphism `δ_K : K ⟶ 𝔻_X 𝔻_X K`.
- `ProEtale.CondensedRing.upperShriekDualizingComplexIso`: for `f : X ⟶ Y`, the identification
  `γ : Rf^! ω_Y ≅ ω_X`, from `f ≫ a_Y = a_X` and the composition isomorphism
  `R(f ≫ a_Y)^! ≅ Ra_Y^! ⋙ Rf^!`
  (`ProEtale.CondensedRing.boundedConstructibleUpperShriekComp_padicAlgCl`) at the unit.
- `ProEtale.CondensedRing.absoluteVerdierExchange` and
  `ProEtale.CondensedRing.dualVerdierExchange`: the absolute exchange
  `Rf_* 𝔻_X K ⟶ 𝔻_Y Rf_! K` and the opposite exchange `Θ_K : Rf_! 𝔻_X K ⟶ 𝔻_Y Rf_* K`, built
  with `γ`.

The isomorphism `γ` is the conjugate of the composition isomorphism of lower shrieks
`R(f ≫ a_Y)_! ≅ Rf_! ⋙ Ra_Y_!`
(`ProEtale.CondensedRing.boundedConstructibleLowerShriekComp_padicAlgCl`).

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

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

/-! ### The Verdier exchange morphism -/

section Exchange

variable {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom]
  (f : X ⟶ Y)

/-- The **Verdier exchange morphism** `Φ_{f,K,L} : Rf_* RHom(K, Rf^! L) ⟶ RHom(Rf_! K, L)` on
bounded constructible complexes: the transpose of the pairing
```
Rf_! K ⊗ᴸ Rf_* RHom(K, Rf^! L) ⟶ Rf_! (K ⊗ᴸ Lf^* Rf_* RHom(K, Rf^! L))
  ⟶ Rf_! (K ⊗ᴸ RHom(K, Rf^! L)) ⟶ Rf_! Rf^! L ⟶ L,
```
see `CategoryTheory.Verdier.exchange`. -/
noncomputable def verdierExchange (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (L : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleLowerStar _ ℓ f).obj
        ((ihom K).obj ((boundedConstructibleUpperShriek _ ℓ f).obj L)) ⟶
      (ihom ((boundedConstructibleLowerShriek _ ℓ f).obj K)).obj L :=
  Verdier.exchange (boundedConstructibleUpperStarLowerStarAdjunction _ ℓ f)
    (boundedConstructibleUpperShriekAdjunction _ ℓ f)
    (boundedConstructibleExceptionalProjection ℓ f) K L

/-- **Verdier duality**: the exchange morphism `Φ_{f,K,L}` is an isomorphism, by the derived
projection formula and the Yoneda lemma. -/
theorem isIso_verdierExchange (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (L : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    IsIso (verdierExchange ℓ f K L) := by
  have := isIso_boundedConstructibleExceptionalProjection_app_app ℓ f K
  exact Verdier.isIso_exchange_of_isIso _ _ _ K L

end Exchange

/-! ### The absolute dualizing complex and the double-dual morphism -/

section Dualizing

instance : LocallyOfFiniteType (Over.mk (𝟙 (Spec (.of k)))).hom :=
  inferInstanceAs (LocallyOfFiniteType (𝟙 _))

instance : QuasiCompact (Over.mk (𝟙 (Spec (.of k)))).hom :=
  inferInstanceAs (QuasiCompact (𝟙 _))

instance : IsSeparated (Over.mk (𝟙 (Spec (.of k)))).hom :=
  inferInstanceAs (IsSeparated (𝟙 _))

variable (X : Over (Spec (.of k)))
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]

/-- The **dualizing complex** `ω_X = Ra_X^! ℚ̄_ℓ` of a separated `k`-scheme of finite type `X`, for
its structure morphism `a_X : X ⟶ Spec k`, the morphism `Over.mkIdTerminal.from X` to the
terminal object `Over.mk (𝟙 (Spec k))` of `Over (Spec k)`. -/
noncomputable def dualizingComplex : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧ :=
  (boundedConstructibleUpperShriek _ ℓ (Over.mkIdTerminal.from X)).obj (𝟙_ _)

variable {X}

/-- The **Verdier dual** `𝔻_X K = RHom(K, ω_X)`. -/
noncomputable def verdierDual (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧ :=
  (ihom K).obj (dualizingComplex ℓ X)

/-- The **double-dual morphism** `δ_K : K ⟶ 𝔻_X 𝔻_X K`: the transpose of the evaluation pairing
`𝔻_X K ⊗ᴸ K ⟶ K ⊗ᴸ 𝔻_X K ⟶ ω_X`. -/
noncomputable def verdierBiduality (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    K ⟶ verdierDual ℓ (verdierDual ℓ K) :=
  Verdier.bidualityMap (dualizingComplex ℓ X) K

/-- **Constructible Verdier biduality**: the double-dual morphism `δ_K : K ⟶ 𝔻_X 𝔻_X K` is an
isomorphism for `K` bounded constructible. See the module docstring.

The dualizing complex must be taken relative to `Spec k` (or at least to a regular base): for the
complex `Ra^! ℚ̄_ℓ = ℚ̄_ℓ` relative to `a = 𝟙` on a nodal curve and `K` the skyscraper `ℚ̄_ℓ` at
the node, `𝔻𝔻K` has rank `9`. -/
theorem isIso_verdierBiduality (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    IsIso (verdierBiduality ℓ K) :=
  sorry

end Dualizing

/-! ### The absolute and opposite exchange morphisms -/

section Absolute

variable {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom]
  (f : X ⟶ Y)

/-- The identification `γ : Rf^! ω_Y ≅ ω_X` of the dualizing complexes: the composition
isomorphism `R(f ≫ a_Y)^! ≅ Ra_Y^! ⋙ Rf^!` of
`ProEtale.CondensedRing.boundedConstructibleUpperShriekComp_padicAlgCl` at the unit, followed by
the equality `f ≫ a_Y = a_X` of morphisms to the terminal object. -/
noncomputable def upperShriekDualizingComplexIso :
    (boundedConstructibleUpperShriek _ ℓ f).obj (dualizingComplex ℓ Y) ≅ dualizingComplex ℓ X :=
  ((boundedConstructibleUpperShriekComp_padicAlgCl ℓ f (Over.mkIdTerminal.from Y)).app
      (𝟙_ _)).symm ≪≫
    eqToIso (by simp only [Over.mkIdTerminal.comp_from]; rfl)

/-- The **absolute Verdier exchange morphism** `Rf_* 𝔻_X K ⟶ 𝔻_Y Rf_! K`: the exchange morphism
`Φ_{f,K,ω_Y}` precomposed with the inverse of `γ = upperShriekDualizingComplexIso`. -/
noncomputable def absoluteVerdierExchange (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleLowerStar _ ℓ f).obj (verdierDual ℓ K) ⟶
      verdierDual ℓ ((boundedConstructibleLowerShriek _ ℓ f).obj K) :=
  Verdier.absoluteExchange (boundedConstructibleUpperStarLowerStarAdjunction _ ℓ f)
    (boundedConstructibleUpperShriekAdjunction _ ℓ f)
    (boundedConstructibleExceptionalProjection ℓ f)
    (dualizingComplex ℓ X) (dualizingComplex ℓ Y) (upperShriekDualizingComplexIso ℓ f) K

/-- The **opposite Verdier exchange morphism** `Θ_K : Rf_! 𝔻_X K ⟶ 𝔻_Y Rf_* K`: the double-dual
morphism of `Rf_! 𝔻_X K`, followed by the dual of `Rf_* K ⟶ Rf_* 𝔻_X 𝔻_X K ⟶ 𝔻_Y Rf_! 𝔻_X K`.
The familiar `𝔻_Y Rf_* K ≅ Rf_! 𝔻_X K` is its inverse, when it is invertible. -/
noncomputable def dualVerdierExchange (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleLowerShriek _ ℓ f).obj (verdierDual ℓ K) ⟶
      verdierDual ℓ ((boundedConstructibleLowerStar _ ℓ f).obj K) :=
  Verdier.dualExchange (boundedConstructibleUpperStarLowerStarAdjunction _ ℓ f)
    (boundedConstructibleUpperShriekAdjunction _ ℓ f)
    (boundedConstructibleExceptionalProjection ℓ f)
    (dualizingComplex ℓ X) (dualizingComplex ℓ Y) (upperShriekDualizingComplexIso ℓ f) K

end Absolute

end AlgebraicGeometry.ProEtale.CondensedRing
