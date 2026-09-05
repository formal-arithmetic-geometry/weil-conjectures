/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.QlbarCoefficient.Integral.Defs
public import WeilConjectures.CategoryTheory.DerivedCategory.QlbarCoefficient.Rationalization

/-!
# The finite-coefficient-field derived category `Dᵇ_c(Y, E)`

Let `𝒪` be the valuation ring of a finite extension `E/ℚ_ℓ` and let `ℓ : 𝒪` be the fixed
prime. The `E`-coefficient category is the rationalization of the integral one:

`Dᵇ_c(Y, E) := Dᵇ_c(Y, 𝒪)[1/ℓ]`,

with the same objects and with `Hom` groups the localizations `Hom_𝒪(K, L)[1/ℓ]`. Since
`ℓ` differs from a power of a uniformizer by a unit, `𝒪[1/ℓ] = E`, so this is the passage
from `𝒪`-coefficients to `E`-coefficients — and, unlike the `[1/ϖ_E]` of the reference
notes, it involves no choice of uniformizer.

By `CategoryTheory.Rationalization.linear` the result is `A`-linear for any `A` with
`IsLocalization (Submonoid.powers ℓ) A`; in particular for `A = E` itself, viewed as a
subfield of `ℚ̄_ℓ`, so the `Hom` groups are honest `E`-vector spaces. This is what the
common-stage construction of `WeilConjectures.CategoryTheory.DerivedCategory.
QlbarCoefficient.CommonStage.Linear` takes as input at each finite stage.

## Main definitions

- `AlgebraicGeometry.Scheme.ProEt.FiniteFieldDerivedCategory`: the category
  `Dᵇ_c(Y, E)`.
- `AlgebraicGeometry.Scheme.ProEt.toFiniteFieldDerivedCategory`: the canonical functor
  `Dᵇ_c(Y, 𝒪) ⥤ Dᵇ_c(Y, E)`, the identity on objects.
-/

@[expose] public section

universe uA u

open CategoryTheory Limits

noncomputable section

namespace AlgebraicGeometry.Scheme.ProEt

variable (Y : Scheme.{u}) (O : Type u) [CommRing O] (l : O)

/-- The **finite coefficient field category** `Dᵇ_c(Y, E)`, the rationalization of
`Dᵇ_c(Y, 𝒪)` obtained by inverting `ℓ`. Its objects are those of `Dᵇ_c(Y, 𝒪)` and its
morphisms are the `ℓ`-localizations of the integral ones. -/
def FiniteFieldDerivedCategory : Type _ :=
  Rationalization (Submonoid.powers l) (AdicDerivedCategory Y O l)

instance : Category (FiniteFieldDerivedCategory Y O l) :=
  inferInstanceAs <| Category (Rationalization (Submonoid.powers l) (AdicDerivedCategory Y O l))

instance : Preadditive (FiniteFieldDerivedCategory Y O l) :=
  inferInstanceAs <|
    Preadditive (Rationalization (Submonoid.powers l) (AdicDerivedCategory Y O l))

/-- The `Hom` groups of `Dᵇ_c(Y, E)` are modules over any localization `A` of `𝒪` at the
powers of `ℓ` — in particular over `E = 𝒪[1/ℓ]` itself. -/
instance (A : Type uA) [CommRing A] [Algebra O A] [IsLocalization (Submonoid.powers l) A] :
    Linear A (FiniteFieldDerivedCategory Y O l) :=
  inferInstanceAs <|
    Linear A (Rationalization (Submonoid.powers l) (AdicDerivedCategory Y O l))

/-- The canonical functor `Dᵇ_c(Y, 𝒪) ⥤ Dᵇ_c(Y, E)`, the identity on objects and the
localization map `f ↦ f / 1` on morphisms. -/
def toFiniteFieldDerivedCategory :
    AdicDerivedCategory Y O l ⥤ FiniteFieldDerivedCategory Y O l :=
  Rationalization.toRationalization

instance : (toFiniteFieldDerivedCategory Y O l).Additive :=
  inferInstanceAs <|
    (Rationalization.toRationalization (M := Submonoid.powers l)
      (C := AdicDerivedCategory Y O l)).Additive

end AlgebraicGeometry.Scheme.ProEt
