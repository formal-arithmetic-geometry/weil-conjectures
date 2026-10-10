/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.PAdicAlgCl.Derived.UpperShriek
public import WeilConjectures.TateTwist.ProEtale

/-!

# Smooth purity for `ℚ̄_ℓ`-coefficients on the pro-étale site

Let `ℓ` be a prime and `f : X ⟶ Y` a smooth morphism of schemes of pure relative dimension `d`
admitting a compactification, with `ℓ` invertible on `Y`. *Smooth purity* (SGA 4, Exposé XVIII,
Théorème 3.2.5, and Bhatt–Scholze, *The pro-étale topology for schemes*, Section 6.8, for
`ℚ̄_ℓ`-coefficients) identifies the exceptional inverse image of the constant coefficient
object with a shifted Tate twist:
```
pur_f : Rf^! ℚ̄_ℓ,Y ≅ ℚ̄_ℓ,X(d)[2d]
```
in the derived category `D(Mod_{ℚ̄_ℓ,X})` of module objects over `ℚ̄_ℓ,X`. Here `Rf^!` is
`AlgebraicGeometry.ProEtale.PadicAlgClRing.rightDerivedUpperShriek` (the right adjoint of
`Rf_!`, built from the chosen compactification of `f`), `ℚ̄_ℓ,Y` is the tensor unit of
`D(Mod_{ℚ̄_ℓ,Y})` and `ℚ̄_ℓ,X(d)` is the Tate twist of `WeilConjectures.TateTwist.ProEtale`.

## Sorried data

`AlgebraicGeometry.ProEtale.PadicAlgClRing.smoothPurityIso` is the purity isomorphism, stated as
a `@[no_expose]` definition with value `sorry`: it is a *chosen* isomorphism, which downstream
constructions (the trace map and Poincaré duality, see
`WeilConjectures/PoincareDuality/Instruction.tex`) use as data, and whose normalization they
inherit.

The isomorphism is not a canonical map whose invertibility could be stated as a proposition
with the tools currently available: classically it is the adjoint of the trace map
`Tr_f : Rf_! ℚ̄_ℓ,X(d)[2d] ⟶ ℚ̄_ℓ,Y` of SGA 4, Exposé XVIII, whose construction (by reduction to
relative curves and the cycle class of the diagonal) is not formalized. Its intended
normalization and compatibilities — with composition of smooth morphisms, with base change,
with étale maps (where `d = 0` and `pur` is the identification `Rf^! = Lf^*`), and the
identification of the induced trace with the classical trace on `H^{2d}_c` of a smooth curve —
are therefore not stated here either.

-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry.ProEtale.PadicAlgClRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {X Y : Scheme.{u}} (f : X ⟶ Y) (d : ℕ)
  [SmoothOfRelativeDimension d f] [HasCompactification f]

/-- **Smooth purity**: for a smooth morphism `f : X ⟶ Y` of pure relative dimension `d` admitting
a compactification, with `ℓ` invertible on `Y`, the exceptional inverse image of the constant
coefficient object is the shifted Tate twist, `Rf^! ℚ̄_ℓ,Y ≅ ℚ̄_ℓ,X(d)[2d]`. This is a chosen
isomorphism: see the module docstring. -/
@[no_expose]
noncomputable def smoothPurityIso (_hℓ : IsUnit (ℓ : Γ(Y, ⊤))) :
    (R(f)^!⟦ℚ̄_ℓ⟧).obj (𝟙_ _) ≅ (tateTwistDerived X ℓ d)⟦(2 * d : ℤ)⟧ :=
  sorry

end AlgebraicGeometry.ProEtale.PadicAlgClRing
