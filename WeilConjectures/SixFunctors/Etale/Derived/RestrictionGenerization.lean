/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.SixFunctors.Etale.Derived.GlobalSectionsRestriction

/-!
# Vanishing of restriction maps by generization

Let `Y` be an irreducible scheme, `z` a closed point of `Y` and `N ∈ D⁺(Y_ét, Λ)` a complex whose
stalks at the geometric points over `z` vanish and whose restriction to `Y - z` has locally
constant cohomology sheaves. Then for every geometric point `s̄` of `Y` not over `z`, the
restriction map `RΓ(Y, N) ⟶ N_s̄` is zero in `D(Λ)`.

Choose a geometric point `η̄` over the generic point of `Y` and specializations of `η̄` to `s̄` and
to a geometric point `z̄` over `z`, i.e. lifts of `η̄` to the strict localizations `Y_(s̄)` and
`Y_(z̄)`. Naturality of restriction gives the commutative square

```
RΓ(Y, N) ──▶ N_s̄
   │          │ ≅
   ▼          ▼
  N_z̄ = 0 ──▶ N_η̄
```

whose right arrow, the specialization map, is an isomorphism because the cohomology sheaves of
`N` are locally constant on the strictly local scheme `Y_(s̄)`, which lies over `Y - z`. Hence the
upper arrow is zero (blueprint `sk-lem-tf-transverse-boundary`, last step).

## Main statements

- `AlgebraicGeometry.Etale.derivedGlobalSectionsRestriction_eq_zero_of_isZero_of_isLocallyConstant`
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Etale

open Scheme

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- **Vanishing of restriction maps by generization** (blueprint `sk-lem-tf-transverse-boundary`,
the generization square): let `Y` be an irreducible scheme, `z` a closed point of `Y` and
`N ∈ D⁺(Y_ét, Λ)` such that `N_z̄ = 0` for the geometric points `z̄` over `z` and the restriction
of `N` to `Y - z` has locally constant cohomology sheaves. Then for every geometric point `s̄`
of `Y` not over `z`, the restriction map `RΓ(Y, N) ⟶ N_s̄` is zero. -/
theorem derivedGlobalSectionsRestriction_eq_zero_of_isZero_of_isLocallyConstant
    {Y : Scheme.{u}} [IrreducibleSpace Y] (z : Y) (hz : IsClosed ({z} : Set Y))
    (N : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hN : ∃ a : ℤ, N.IsGE a)
    (hNz : ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (zbar : Spec (.of Ω) ⟶ Y),
      Set.range zbar = {z} → IsZero ((L((zbar)^*[ModuleCat.{u + 1} Λ])).obj N))
    (hNloc : ∀ n : ℤ, IsLocallyConstantSheaf ((DerivedCategory.homologyFunctor _ n).obj
      ((L((Opens.ι ⟨({z} : Set Y)ᶜ, hz.isOpen_compl⟩)^*[ModuleCat.{u + 1} Λ])).obj N)))
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (sbar : Spec (.of Ω) ⟶ Y)
    (hs : z ∉ Set.range sbar) :
    derivedGlobalSectionsRestriction Λ sbar N = 0 := by
  sorry

end AlgebraicGeometry.Etale
