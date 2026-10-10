/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.LowerShriek.MorphismDefs

/-!

# The base change theorem for the lower shriek

Fix a commutative ring `Λ` and a cartesian square of schemes

```
X' --g'--> X
|          |
f'         f
v          v
Y' --g---> Y
```

recorded as `sq : IsPullback g' f' f g`, and a compactification `c : X ⟶[i] Z ⟶[p] Y`
of `f`. This file deduces from the proper base change theorem
(`AlgebraicGeometry.Etale.isIso_baseChange_of_isProper` of
`WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper`) that the compact-support
base-change morphism

`Ex_!^c : Rf_!^c ⋙ Lg^* ⟶ Lg'^* ⋙ Rf'_!^{c'}`

of `WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.LowerShriek.MorphismDefs` is an
isomorphism, where `c' = c.baseChange sq` and `Rf_!^c = Rf_!(c)[A]+` is the derived lower
shriek `Etale.rightDerivedLowerShriekOfCompactificationPlus` associated with `c`. No
properness is assumed on `f` itself: the properness enters only through the structure
morphism `p` of the compactification, which is proper by definition. This is the base
change theorem for the lower shriek `Compactification.lowerShriek`.

Indeed, in the composite defining `Ex_!^c` the extension-by-zero exchange is an
isomorphism by construction, and the direct-image exchange `Ex_*` of the proper square
of the base-changed compactification is an isomorphism by proper base change applied to
the proper morphism `p`, on complexes with torsion cohomology. For the pointwise
statement the extension by zero `i_!` must preserve torsion cohomology, which is a
stalkwise statement recorded separately
(`Etale.DerivedCategory.Plus.torsionHomology_openImmersionLowerShriek`).

## Main statements

- `AlgebraicGeometry.Etale.DerivedCategory.Plus.torsionHomology_openImmersionLowerShriek`:
  extension by zero along an open immersion preserves torsion cohomology.
- `AlgebraicGeometry.Etale.isIso_lowerShriekBaseChange`: the base change theorem for the
  lower shriek, for a bounded below complex with torsion cohomology.
- `AlgebraicGeometry.Etale.isIso_lowerShriekBaseChange_of_isAddTorsion_ring`: for a
  torsion coefficient ring, the compact-support base-change transformation is an
  isomorphism of functors.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Abelian

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

variable (Λ : Type (u + 1)) [CommRing Λ]

/- Sheafification, pointwise left Kan extensions and their left exactness for the small
étale sites of all schemes at once, with coefficients in the ring `Λ`, are provided by
the instances of `WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper`; the
localized derived categories come from `HasDerivedCategory.ofIsGrothendieckAbelian` of
`WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory`. -/

/-- Extension by zero along an open immersion preserves torsion cohomology: since `j_!`
is exact, the cohomology sheaves of `j_! K` are the extensions by zero of the cohomology
sheaves of `K`, and on geometric stalks the extension by zero of a sheaf either keeps
the stalk (over points of `U`) or replaces it by zero (outside `U`), both of which are
torsion. -/
lemma Etale.DerivedCategory.Plus.torsionHomology_openImmersionLowerShriek
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (K : DerivedCategory.Plus (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hK : Etale.DerivedCategory.Plus.torsionHomology Λ U K) :
    Etale.DerivedCategory.Plus.torsionHomology Λ X
      (D+(Etale.openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j).obj K) :=
  sorry

variable {X Y X' Y' : Scheme.{u}}
  {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}

/-- **The base change theorem for the lower shriek**: for a cartesian square of schemes

```
X' --g'--> X
|          |
f'         f
v          v
Y' --g---> Y
```

a compactification `c : X ⟶[i] Z ⟶[p] Y` of `f`, and a bounded below complex
`K ∈ D⁺(X_ét, Λ)` with torsion cohomology, the compact-support base-change morphism

`Ex_!^c(K) : Lg^*(Rf_!^c K) ⟶ Rf'_!^{c'}(Lg'^* K)`

is an isomorphism, where `c' = c.baseChange sq`. No hypothesis is imposed on `f` beyond
the existence of the compactification, nor on `g`: the direct-image exchange in the
defining composite is an isomorphism by proper base change for the proper structure
morphism `p`, applied to `i_! K`, whose cohomology is torsion since extension by zero
preserves torsion cohomology; the extension-by-zero exchange is an isomorphism by
construction. -/
theorem Etale.isIso_lowerShriekBaseChange (c : Compactification f) (sq : IsPullback g' f' f g)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hK : Etale.DerivedCategory.Plus.torsionHomology Λ X K) :
    IsIso ((Etale.lowerShriekBaseChange (ModuleCat.{u + 1} Λ) c sq).app K) := by
  rw [Etale.lowerShriekBaseChange_app]
  have := Etale.isIso_baseChange_of_isProper Λ (c.baseChange_isPullback_g sq) _
    (Etale.DerivedCategory.Plus.torsionHomology_openImmersionLowerShriek Λ c.i K hK)
  infer_instance

/-- **The base change theorem for the lower shriek as an isomorphism of functors**: if
the coefficient ring `Λ` is torsion as an additive group — in particular if `Λ` is
finite, e.g. `Λ = ℤ/ℓⁿℤ` — then for a cartesian square and a compactification `c` of
`f` the compact-support base-change transformation

`Ex_!^c : Rf_!^c ⋙ Lg^* ⟶ Lg'^* ⋙ Rf'_!^{c'}`

on the bounded below derived categories is an isomorphism: every complex automatically
has torsion cohomology. -/
theorem Etale.isIso_lowerShriekBaseChange_of_isAddTorsion_ring (hΛ : IsAddTorsion Λ)
    (c : Compactification f) (sq : IsPullback g' f' f g) :
    IsIso (Etale.lowerShriekBaseChange (ModuleCat.{u + 1} Λ) c sq) :=
  have : ∀ K, IsIso ((Etale.lowerShriekBaseChange (ModuleCat.{u + 1} Λ) c sq).app K) := fun K ↦
    Etale.isIso_lowerShriekBaseChange Λ c sq K
      (Etale.DerivedCategory.Plus.torsionHomology_of_isTorsion Λ X hΛ K)
  NatIso.isIso_of_isIso_app _

end AlgebraicGeometry
