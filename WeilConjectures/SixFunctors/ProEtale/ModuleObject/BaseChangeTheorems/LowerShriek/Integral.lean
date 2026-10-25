/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.CompactlySupported

/-!

# The proper base change theorem for constructible `𝒪_E`-sheaves

Let `ℓ` be a prime and `E ⊆ ℚ̄_ℓ` a finite subextension of `ℚ_ℓ`, with condensed ring of integers
`𝒪̲_E` (`Profinite.padicIntegersRingObj ℓ E`). This file states the proper base change theorem for
bounded constructible `𝒪_E`-sheaves
(`ProEtale.CondensedRing.isIso_boundedConstructibleBaseChange_of_isProper_padicIntegers`,
blueprint `sk-thm-sfb-proper-base-change`), the integral analogue of
`ProEtale.CondensedRing.isIso_boundedConstructibleBaseChange_of_isProper`. It is `sorry`, as are
its `E` and `ℚ̄_ℓ` versions.

-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime]
  (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E]
  [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E]
  {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]

/-! ### Proper base change -/

section Proper

variable {X Y X' Y' : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom] [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
  [IsSeparated X'.hom] [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]
  {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}

include k in
/-- **The proper base change theorem** for bounded constructible `𝒪_E`-sheaves (blueprint
`sk-thm-sfb-proper-base-change`), `E ⊆ ℚ̄_ℓ` a finite subextension of `ℚ_ℓ`: for a cartesian
square of schemes

```
X' --g'--> X
|          |
f'         f
v          v
Y' --g---> Y
```

with `f` proper, the base-change morphism `BC_sq : Rf_* ⋙ Lg^* ⟶ Lg'^* ⋙ Rf'_*` is an
isomorphism of functors `Dᵇc(X)⟦𝒪̲_E⟧ ⥤ Dᵇc(Y')⟦𝒪̲_E⟧`. This is the integral analogue of
`isIso_boundedConstructibleBaseChange_of_isProper`; it reduces to the étale proper base change
theorem `AlgebraicGeometry.Etale.isIso_baseChange_of_isProper` by writing a constructible
`𝒪_E`-complex as the derived limit of its reductions modulo `ϖⁿ` (Bhatt–Scholze, Section 6.7).
Currently `sorry`, as are its `E` and `ℚ̄_ℓ` versions. -/
theorem isIso_boundedConstructibleBaseChange_of_isProper_padicIntegers [IsProper f.left]
    (sq : IsPullback g' f' f g) :
    IsIso (PadicIntegersRingObj.boundedConstructibleBaseChange
      ℓ E sq.toCommSq) :=
  sorry

end Proper

end AlgebraicGeometry.ProEtale.CondensedRing
