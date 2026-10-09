/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.UpperShriek
public import WeilConjectures.SixFunctors.ProEtale.Derived.Comparison
public import WeilConjectures.SixFunctors.ProEtale.Derived.LowerShriek

/-!
# The constructible exceptional inverse image on pro-étale sites

The exceptional inverse image of the blueprint (`sk-def-sf-operations` (vi)) is *not* a right
adjoint of the pro-étale `Rf_!` on all of `D(Y_proét)`: such a right adjoint need not exist
(`rem:sf-ambient-counterexample`, the structure morphism of an elliptic curve over `F̄_p`), so
`AlgebraicGeometry.ProEtale.rightDerivedUpperShriek`, which assumes one, is only the
conditional ambient functor of the blueprint. The functor the blueprint uses is instead the
étale right adjoint transported along the comparison `ν : X_proét ⟶ X_ét`,

`Rf^! = ν_X^* ∘ f^× ∘ Rν_{Y,*} : D⁺(Y_proét) ⥤ D⁺(X_proét)`,

where `f^×` is the right adjoint of the étale `Rf_!`
(`AlgebraicGeometry.Etale.rightDerivedUpperShriekPlus`), which exists unconditionally. Its
adjunction with `Rf_!` holds on the objects of étale origin (`sk-prop-sf-existence` (c)).

This is the finite-coefficient construction; at the adic stages `𝒪_E`, `E`, `ℚ̄_ℓ` the blueprint
defines `Rf^!` levelwise on normalized systems, which needs reduction functors
`D(−, 𝒪_E) ⥤ D(−, A_{E,n})` and derived limits that are not available here.

## Main definitions

- `AlgebraicGeometry.ProEtale.constructibleUpperShriek`: `ν^* ∘ f^× ∘ Rν_*` on `D⁺`.

## Main statements

- `AlgebraicGeometry.ProEtale.nonempty_adjunction_constructibleUpperShriek`: the adjunction on
  objects of étale origin.
-/

@[expose] public section

universe u' u

open CategoryTheory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace ProEtale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]

/-- Blueprint `sk-def-sf-operations` (vi): The six operations: ambient typing

The *constructible exceptional inverse image* on the bounded below derived categories of
pro-étale sheaves,

`Rf^! = ν_X^* ∘ f^× ∘ Rν_{Y,*} : D⁺(Y_proét) ⥤ D⁺(X_proét)`,

the étale right adjoint `f^×` of `Rf_!` (`AlgebraicGeometry.Etale.rightDerivedUpperShriekPlus`)
transported along the étale/pro-étale comparison. Unlike
`AlgebraicGeometry.ProEtale.rightDerivedUpperShriek` it needs no hypothesis on `f`. -/
noncomputable def constructibleUpperShriek :
    DerivedCategory.Plus (Sheaf (Scheme.ProEt.topology Y) A) ⥤
      DerivedCategory.Plus (Sheaf (Scheme.ProEt.topology X) A) :=
  R+(ν_*(Y)[A]) ⋙ Etale.rightDerivedUpperShriekPlus A f ⋙ D+(ν^*(X)[A])

/-- Blueprint `sk-prop-sf-existence`: Existence of the exceptional right adjoint

*Clause (c), the adjunction on objects of étale origin.* For `G ∈ D⁺(X_ét)` and
`L ∈ D⁺(Y_proét)`,

`Hom_Y(Rf_! ν_X^* G, L) ≅ Hom_X(ν_X^* G, Rf^! L)`,

naturally in both; equivalently, `ν_X^* ⋙ Rf_!` is left adjoint to `Rf^! ⋙ Rν_{X,*}`. The proof
is the chain of the blueprint: the compact-support comparison
`Rf_! ν_X^* ≅ ν_Y^* Rf^{ét}_!`, the adjunction `ν_Y^* ⊣ Rν_{Y,*}`, the étale adjunction
`Rf^{ét}_! ⊣ f^×`, and the full faithfulness of `ν_X^*` on `D⁺`. Every object of
`D^b_{ctf}(X_proét)` is of étale origin, so this is the adjunction on the small categories. -/
theorem nonempty_adjunction_constructibleUpperShriek [MonoidalCategory A]
    [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
    [Abelian.HasFunctorialFlatResolution A] :
    Nonempty (D+(ν^*(X)[A]) ⋙ rightDerivedLowerShriekPlus A f ⊣
      constructibleUpperShriek A f ⋙ R+(ν_*(X)[A])) :=
  sorry

end ProEtale

end AlgebraicGeometry
