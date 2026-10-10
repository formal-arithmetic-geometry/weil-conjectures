/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.PoincareDuality.Verdier
public import WeilConjectures.SmoothPurity.Defs

/-!

# Poincaré duality for `ℚ̄_ℓ`-coefficients on the pro-étale site

Let `ℓ` be a prime and `p : X ⟶ S` a smooth morphism of pure relative dimension `d` admitting a
compactification, with `ℓ` invertible on `S`. Smooth purity
(`ProEtale.PadicAlgClRing.smoothPurityIso`) provides the chosen isomorphism
`pur_p : Rp^! ℚ̄_ℓ,S ≅ ℚ̄_ℓ,X(d)[2d]`, and this file defines from it, through the abstract
constructions of `WeilConjectures.PoincareDuality.Abstract`:

* the **trace** `Tr_p : Rp_! ℚ̄_ℓ,X(d)[2d] ⟶ ℚ̄_ℓ,S`, the composite of `Rp_!(pur_p⁻¹)` and the
  counit of `Rp_! ⊣ Rp^!`;
* the **Poincaré duality morphism** `PD_p : Rp_* ℚ̄_ℓ,X(d)[2d] ⟶ RHom(Rp_! ℚ̄_ℓ,X, ℚ̄_ℓ,S)`, the
  composite of `Rp_*(pur_p⁻¹)`, the identification `Rp^! ℚ̄_ℓ,S ≅ RHom(ℚ̄_ℓ,X, Rp^! ℚ̄_ℓ,S)` and
  the Verdier exchange morphism `Φ_{p,ℚ̄_ℓ,X,ℚ̄_ℓ,S}`;
* the **compact-support cup product**
  `cup_c : Rp_! ℚ̄_ℓ,X ⊗ᴸ Rp_* ℚ̄_ℓ,X(d)[2d] ⟶ Rp_! ℚ̄_ℓ,X(d)[2d]`, from the derived exceptional
  projection morphism and the counit of `Lp^* ⊣ Rp_*`.

All three share the normalization of `pur_p`: the transpose of `PD_p` is exactly `Tr_p ∘ cup_c`
(`ProEtale.PadicAlgClRing.uncurry_poincareMap`), and `PD_p` is an isomorphism by Verdier
duality (`ProEtale.PadicAlgClRing.isIso_poincareMap`), which is **Poincaré duality** in the
form `𝔻_S(Rp_! ℚ̄_ℓ,X) ≅ Rp_* ℚ̄_ℓ,X(d)[2d]`.

## Not treated here

* The passage from the derived statement to the perfect pairing
  `H^i_c(X, ℚ̄_ℓ) × H^{2d-i}(X, ℚ̄_ℓ(d)) ⟶ ℚ̄_ℓ` on cohomology groups over `S = Spec k̄`, which
  requires the perfectness of `Rp_! ℚ̄_ℓ,X` and the comparison of `RΓ(S, RHom(-, ℚ̄_ℓ,S))` with the
  linear dual.
* The Frobenius equivariance, which belongs to the Weil sheaf formalism.
* The compatibility with the compactly supported base change isomorphism and with the
  compactification and composition comparisons, which are commutativity conditions on the maps
  defined here, to be stated once those comparisons are available.

## Sorried input

- `ProEtale.PadicAlgClRing.boundedConstructible_tensorUnit`: the constant coefficient object
  `ℚ̄_ℓ,X` is bounded constructible, which is what Verdier duality is applied to.

-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory MonoidalClosed

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.PadicAlgClRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime]

/-- The constant coefficient object `ℚ̄_ℓ,X`, the tensor unit of `D(Mod_{ℚ̄_ℓ,X})`, is bounded
constructible. -/
lemma boundedConstructible_tensorUnit (X : Scheme.{u}) :
    boundedConstructible (padicAlgClSheaf X ℓ)
      (𝟙_ (DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (padicAlgClSheaf X ℓ)))) :=
  sorry

variable {X S : Scheme.{u}} (p : X ⟶ S) (d : ℕ) [SmoothOfRelativeDimension d p]
  [HasCompactification p] (hℓ : IsUnit (ℓ : Γ(S, ⊤)))

/-- The **trace** `Tr_p : Rp_! ℚ̄_ℓ,X(d)[2d] ⟶ ℚ̄_ℓ,S` of a smooth morphism `p : X ⟶ S` of pure
relative dimension `d`: `Rp_!(pur_p⁻¹)` followed by the counit of `Rp_! ⊣ Rp^!`. -/
noncomputable def trace :
    (R(p)_!⟦ℚ̄_ℓ⟧).obj ((tateTwistDerived X ℓ d)⟦(2 * d : ℤ)⟧) ⟶ 𝟙_ _ :=
  Verdier.trace (rightDerivedUpperShriekAdjunction ℓ p) (smoothPurityIso ℓ p d hℓ)

/-- The **Poincaré duality morphism**
`PD_p : Rp_* ℚ̄_ℓ,X(d)[2d] ⟶ RHom(Rp_! ℚ̄_ℓ,X, ℚ̄_ℓ,S)`: `Rp_*(pur_p⁻¹)`, the identification
`Rp^! ℚ̄_ℓ,S ≅ RHom(ℚ̄_ℓ,X, Rp^! ℚ̄_ℓ,S)`, and the Verdier exchange morphism. -/
noncomputable def poincareMap :
    (R((p)_*⟦ℚ̄_ℓ⟧)).obj ((tateTwistDerived X ℓ d)⟦(2 * d : ℤ)⟧) ⟶
      (ihom ((R(p)_!⟦ℚ̄_ℓ⟧).obj (𝟙_ _))).obj (𝟙_ _) :=
  Verdier.poincareMap (derivedUpperStarLowerStarAdjunction ℓ p)
    (rightDerivedUpperShriekAdjunction ℓ p) (exceptionalProjectionMorphism ℓ p)
    (smoothPurityIso ℓ p d hℓ)

/-- The **compact-support cup product**
`cup_c : Rp_! ℚ̄_ℓ,X ⊗ᴸ Rp_* ℚ̄_ℓ,X(d)[2d] ⟶ Rp_! ℚ̄_ℓ,X(d)[2d]`: the derived exceptional
projection morphism `PF^!`, the counit `Lp^* Rp_* ⟶ 𝟭` and the left unitor. -/
noncomputable def cupProduct :
    (R(p)_!⟦ℚ̄_ℓ⟧).obj (𝟙_ _) ⊗ (R((p)_*⟦ℚ̄_ℓ⟧)).obj ((tateTwistDerived X ℓ d)⟦(2 * d : ℤ)⟧) ⟶
      (R(p)_!⟦ℚ̄_ℓ⟧).obj ((tateTwistDerived X ℓ d)⟦(2 * d : ℤ)⟧) :=
  Verdier.cupProduct (derivedUpperStarLowerStarAdjunction ℓ p) (exceptionalProjectionMorphism ℓ p)

omit [SmoothOfRelativeDimension d p] in
/-- **Poincaré duality is the trace–cup pairing**: the transpose
`Rp_! ℚ̄_ℓ,X ⊗ᴸ Rp_* ℚ̄_ℓ,X(d)[2d] ⟶ ℚ̄_ℓ,S` of the Poincaré duality morphism is the cup product
followed by the trace. -/
theorem uncurry_poincareMap :
    uncurry (poincareMap ℓ p d hℓ) = cupProduct ℓ p d ≫ trace ℓ p d hℓ :=
  Verdier.uncurry_poincareMap _ _ _ _ (exceptionalProjectionMorphism_natural_right ℓ p)

omit [SmoothOfRelativeDimension d p] in
/-- **Poincaré duality**: the Poincaré duality morphism
`PD_p : Rp_* ℚ̄_ℓ,X(d)[2d] ⟶ RHom(Rp_! ℚ̄_ℓ,X, ℚ̄_ℓ,S)` is an isomorphism, by Verdier duality for
the bounded constructible object `ℚ̄_ℓ,X`. -/
theorem isIso_poincareMap : IsIso (poincareMap ℓ p d hℓ) := by
  have := isIso_verdierExchange ℓ p (𝟙_ _) (boundedConstructible_tensorUnit ℓ X) (𝟙_ _)
  unfold poincareMap Verdier.poincareMap
  exact inferInstanceAs (IsIso (_ ≫ verdierExchange ℓ p (𝟙_ _) (𝟙_ _)))

end AlgebraicGeometry.ProEtale.PadicAlgClRing
