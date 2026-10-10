/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Braided
public import WeilConjectures.PoincareDuality.ProjectionFormula
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.PAdicAlgCl.Derived.Hom

/-!

# Verdier duality for `ℚ̄_ℓ`-coefficients on the pro-étale site

Let `ℓ` be a prime and `f : X ⟶ Y` a morphism of schemes admitting a compactification. This
file specializes the abstract constructions of `WeilConjectures.PoincareDuality.Abstract` to
the six functors on the derived categories `D(Mod_{ℚ̄_ℓ,X})` of module objects over `ℚ̄_ℓ`: the
adjunctions `Lf^* ⊣ Rf_*` and `Rf_! ⊣ Rf^!`, the derived internal hom `RHom` and the derived
exceptional projection morphism `PF^!` of `WeilConjectures.PoincareDuality.ProjectionFormula`.

## Main definitions

- `ProEtale.PadicAlgClRing.verdierExchange`: the Verdier exchange morphism
  `Φ_{f,K,L} : Rf_* RHom(K, Rf^! L) ⟶ RHom(Rf_! K, L)`.
- `ProEtale.PadicAlgClRing.dualizingComplex`: for a structure morphism `a : X ⟶ S`, the
  dualizing complex `ω_X = Ra^! ℚ̄_ℓ,S`, and `ProEtale.PadicAlgClRing.verdierDual`: the Verdier
  dual `𝔻_X K = RHom(K, ω_X)`.
- `ProEtale.PadicAlgClRing.verdierBiduality`: the double-dual morphism `δ_K : K ⟶ 𝔻_X 𝔻_X K`.
- `ProEtale.PadicAlgClRing.absoluteVerdierExchange` and
  `ProEtale.PadicAlgClRing.dualVerdierExchange`: for an `S`-morphism `f` and a given
  identification `γ : Rf^! ω_Y ≅ ω_X`, the absolute exchange `Rf_* 𝔻_X K ⟶ 𝔻_Y Rf_! K` and the
  opposite exchange `Θ_K : Rf_! 𝔻_X K ⟶ 𝔻_Y Rf_* K`.

The identification `γ` is taken as an argument: it is an instance of the composition
isomorphism `R(f ≫ a_Y)^! ≅ Ra_Y^! ⋙ Rf^!` for exceptional inverse images, which depends on the
compatibility of the chosen compactifications and is not yet available.

## Main results

- `ProEtale.PadicAlgClRing.isIso_verdierExchange`: **Verdier duality**, the exchange morphism
  is an isomorphism for `K` bounded constructible, deduced from the derived projection formula
  (`isIso_exceptionalProjectionMorphism`) by the Yoneda argument.

## Sorried input

- `ProEtale.PadicAlgClRing.isIso_verdierBiduality`: **constructible biduality**, `δ_K` is an
  isomorphism for `K` bounded constructible (Input 3.3 of the instruction file).

-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory MonoidalClosed

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.PadicAlgClRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime]

/-! ### The Verdier exchange morphism -/

section Exchange

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]

/-- The **Verdier exchange morphism** `Φ_{f,K,L} : Rf_* RHom(K, Rf^! L) ⟶ RHom(Rf_! K, L)` on
module objects over `ℚ̄_ℓ`: the transpose of the pairing
```
Rf_! K ⊗ᴸ Rf_* RHom(K, Rf^! L) ⟶ Rf_! (K ⊗ᴸ Lf^* Rf_* RHom(K, Rf^! L))
  ⟶ Rf_! (K ⊗ᴸ RHom(K, Rf^! L)) ⟶ Rf_! Rf^! L ⟶ L,
```, see `CategoryTheory.Verdier.exchange`. -/
noncomputable def verdierExchange
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (padicAlgClSheaf X ℓ)))
    (L : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (padicAlgClSheaf Y ℓ))) :
    (R((f)_*⟦ℚ̄_ℓ⟧)).obj ((ihom K).obj ((R(f)^!⟦ℚ̄_ℓ⟧).obj L)) ⟶
      (ihom ((R(f)_!⟦ℚ̄_ℓ⟧).obj K)).obj L :=
  Verdier.exchange (derivedUpperStarLowerStarAdjunction ℓ f)
    (rightDerivedUpperShriekAdjunction ℓ f) (exceptionalProjectionMorphism ℓ f) K L

/-- **Verdier duality**: the exchange morphism `Φ_{f,K,L}` is an isomorphism for `K` bounded
constructible, by the derived projection formula and the Yoneda lemma. -/
theorem isIso_verdierExchange
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (padicAlgClSheaf X ℓ)))
    (hK : boundedConstructible (padicAlgClSheaf X ℓ) K)
    (L : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (padicAlgClSheaf Y ℓ))) :
    IsIso (verdierExchange ℓ f K L) :=
  haveI : ∀ B, IsIso (exceptionalProjectionMorphism ℓ f K B) :=
    fun B ↦ isIso_exceptionalProjectionMorphism ℓ f K hK B
  Verdier.isIso_exchange_of_isIso _ _ _ (exceptionalProjectionMorphism_natural_right ℓ f) K L

end Exchange

/-! ### The dualizing complex and the double-dual morphism -/

section Dualizing

variable {X S : Scheme.{u}} (a : X ⟶ S) [HasCompactification a]

/-- The **dualizing complex** `ω_X = Ra^! ℚ̄_ℓ,S` of `X` relative to the structure morphism
`a : X ⟶ S`. -/
noncomputable def dualizingComplex :
    DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (padicAlgClSheaf X ℓ)) :=
  (R(a)^!⟦ℚ̄_ℓ⟧).obj (𝟙_ _)

/-- The **Verdier dual** `𝔻_X K = RHom(K, ω_X)` relative to the structure morphism `a : X ⟶ S`. -/
noncomputable def verdierDual
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (padicAlgClSheaf X ℓ))) :
    DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (padicAlgClSheaf X ℓ)) :=
  (ihom K).obj (dualizingComplex ℓ a)

/-- The **double-dual morphism** `δ_K : K ⟶ 𝔻_X 𝔻_X K`: the transpose of the evaluation pairing
`𝔻_X K ⊗ᴸ K ⟶ K ⊗ᴸ 𝔻_X K ⟶ ω_X`. -/
noncomputable def verdierBiduality
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (padicAlgClSheaf X ℓ))) :
    K ⟶ verdierDual ℓ a (verdierDual ℓ a K) :=
  Verdier.bidualityMap (dualizingComplex ℓ a) K

/-- **Constructible Verdier biduality**: the double-dual morphism `δ_K` is an isomorphism for
`K` bounded constructible. See the module docstring. -/
theorem isIso_verdierBiduality
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (padicAlgClSheaf X ℓ)))
    (hK : boundedConstructible (padicAlgClSheaf X ℓ) K) :
    IsIso (verdierBiduality ℓ a K) :=
  sorry

end Dualizing

/-! ### The absolute and opposite exchange morphisms -/

section Absolute

variable {X Y S : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]
  (aX : X ⟶ S) [HasCompactification aX] (aY : Y ⟶ S) [HasCompactification aY]
  (γ : (R(f)^!⟦ℚ̄_ℓ⟧).obj (dualizingComplex ℓ aY) ≅ dualizingComplex ℓ aX)

/-- The **absolute Verdier exchange morphism** `Rf_* 𝔻_X K ⟶ 𝔻_Y Rf_! K`, given an
identification `γ : Rf^! ω_Y ≅ ω_X`: the exchange morphism `Φ_{f,K,ω_Y}` precomposed with
`γ⁻¹`. -/
noncomputable def absoluteVerdierExchange
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (padicAlgClSheaf X ℓ))) :
    (R((f)_*⟦ℚ̄_ℓ⟧)).obj (verdierDual ℓ aX K) ⟶ verdierDual ℓ aY ((R(f)_!⟦ℚ̄_ℓ⟧).obj K) :=
  Verdier.absoluteExchange (derivedUpperStarLowerStarAdjunction ℓ f)
    (rightDerivedUpperShriekAdjunction ℓ f) (exceptionalProjectionMorphism ℓ f)
    (dualizingComplex ℓ aX) (dualizingComplex ℓ aY) γ K

/-- The **opposite Verdier exchange morphism** `Θ_K : Rf_! 𝔻_X K ⟶ 𝔻_Y Rf_* K`, given an
identification `γ : Rf^! ω_Y ≅ ω_X`: the double-dual morphism of `Rf_! 𝔻_X K`, followed by the
dual of `Rf_* K ⟶ Rf_* 𝔻_X 𝔻_X K ⟶ 𝔻_Y Rf_! 𝔻_X K`. The familiar `𝔻_Y Rf_* K ≅ Rf_! 𝔻_X K` is its
inverse, when it is invertible. -/
noncomputable def dualVerdierExchange
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (padicAlgClSheaf X ℓ))) :
    (R(f)_!⟦ℚ̄_ℓ⟧).obj (verdierDual ℓ aX K) ⟶ verdierDual ℓ aY ((R((f)_*⟦ℚ̄_ℓ⟧)).obj K) :=
  Verdier.dualExchange (derivedUpperStarLowerStarAdjunction ℓ f)
    (rightDerivedUpperShriekAdjunction ℓ f) (exceptionalProjectionMorphism ℓ f)
    (dualizingComplex ℓ aX) (dualizingComplex ℓ aY) γ K

end Absolute

end AlgebraicGeometry.ProEtale.PadicAlgClRing
