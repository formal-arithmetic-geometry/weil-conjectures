/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Defs

/-!
# Base change for open immersions of schemes of finite type over a field

Let `K` be a field, `j : U ⟶ X` an open immersion of schemes of finite type over `K` and `Y` a
scheme of finite type over `K`. For the cartesian square

```
  Y ×_K U --h--> Y ×_K X
     |              |
     p              q
     v              v
     U ------j----> X
```

the exchange morphism `q⁻¹ R^i j_* F ⟶ R^i h_* p⁻¹ F` is an isomorphism for every sheaf `F` of
`Λ`-modules on `U_ét`, where `Λ` is killed by an integer `n` invertible in `K` (blueprint
`lem-kun-0f1h`, `AlgebraicGeometry.Etale.isIso_baseChangeHomologyMap_of_isOpenImmersion_of_field`).

## References

- Stacks Project, Lemma 0F1H, <https://stacks.math.columbia.edu/tag/0F1H>
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- Blueprint `lem-kun-0f1h`: base change for open immersions.

Let `K` be a field, `n` an integer invertible in `K` which kills `Λ`, `j : U ⟶ X` an open
immersion of schemes of finite type over `K` and `Y` a scheme of finite type over `K`. Let
`W = X ×_K Y` with projection `q₁ : W ⟶ X`, and let `V = U ×_X W` with projections
`e : V ⟶ U` and `h : V ⟶ W`. Then the exchange morphism
`q₁⁻¹ R^i j_* F ⟶ R^i h_* e⁻¹ F` is an isomorphism for every sheaf `F` of `Λ`-modules on
`U_ét` and every degree `i`. -/
@[stacks 0F1H]
theorem Etale.isIso_baseChangeHomologyMap_of_isOpenImmersion_of_field {K : Type u} [Field K]
    {X U Y W V : Scheme.{u}} (aX : X ⟶ Spec (.of K)) (aY : Y ⟶ Spec (.of K))
    [LocallyOfFiniteType aX] [QuasiCompact aX] [LocallyOfFiniteType aY] [QuasiCompact aY]
    (j : U ⟶ X) [IsOpenImmersion j] (q₁ : W ⟶ X) (q₂ : W ⟶ Y) (hW : IsPullback q₁ q₂ aX aY)
    (e : V ⟶ U) (h : V ⟶ W) (sq : IsPullback e h j q₁) (n : ℕ) (hn : IsUnit (n : K))
    (hΛ : (n : Λ) = 0) (i : ℤ) (F : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    IsIso (Etale.baseChangeHomologyMap Λ sq i F) :=
  sorry

end AlgebraicGeometry
