/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Constructible
public import WeilConjectures.SixFunctors.Etale.Derived.Tensor
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek

/-!
# Exchange and projection transformations for `Rf_!`

The two natural transformations of the six-functor formalism that are attached to `Rf_!`: the
exchange `Ex_!` of a cartesian square and the projection map `PF`, together with the theorems
saying that they are isomorphisms — compact-support base change and the projection formula.

The exchange `Ex_*` for `Rf_*` already exists in this repository, as
`AlgebraicGeometry.Etale.baseChange` and `AlgebraicGeometry.Etale.derivedBaseChangeMapPlus`;
only the `Rf_!` versions are introduced here.

## Implementation notes

`Ex_!` and `PF` are the transformations of the framework chapter's `def:exchange-projection`,
which is not this block's; they are recorded here with `sorry` bodies and a `TODO(unify)`
marker so that the statements of this chapter can refer to them. The theorems below are
phrased as the existence of the corresponding isomorphism of functors, which is what the
purity chapter uses and which does not depend on the placeholder.

## Main definitions

- `AlgebraicGeometry.Etale.derivedLowerShriekExchange`: `Ex_! : Lg^* Rf_! ⟶ Rf'_! Lg'^*`.
- `AlgebraicGeometry.Etale.reduction`: reduction of coefficients `K ↦ K ⊗^L (Λ/J)_X`.

## Main statements

- `AlgebraicGeometry.Etale.nonempty_iso_upperStar_comp_rightDerivedLowerShriek`
- `AlgebraicGeometry.Etale.nonempty_iso_derivedTensor_rightDerivedLowerShriek`
- `AlgebraicGeometry.Etale.nonempty_iso_derivedTensor_rightDerivedLowerShriek_iff_reduction`
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme Etale

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ] {X Y : Scheme.{u}}

section Exchange

variable {X' Y' : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
  [HasCompactification f] [HasCompactification f']

/-- Blueprint `sk-def-sf-exchanges`: Exchange and projection transformations, typed

The exchange transformation `Ex_! : Lg^* Rf_! ⟶ Rf'_! Lg'^*` attached to a cartesian square,
as a natural transformation between functors `D(X_ét, Λ) ⥤ D(Y'_ét, Λ)`.

This is the transformation of the framework chapter, restated here with the source and target
categories of the purity chapter. The third transformation of the subsection, the projection
map `PF_{f,K,L} : Rf_! K ⊗^L L ⟶ Rf_!(K ⊗^L Lf^* L)`, is not named: the purity chapter uses
only the assertion that it is an isomorphism, which is
`AlgebraicGeometry.Etale.nonempty_iso_derivedTensor_rightDerivedLowerShriek`. -/
-- TODO(unify): def:exchange-projection
noncomputable def derivedLowerShriekExchange (_sq : IsPullback g' f' f g) :
    R(f)_![ModuleCat.{u + 1} Λ] ⋙ L((g)^*[ModuleCat.{u + 1} Λ]) ⟶
      L((g')^*[ModuleCat.{u + 1} Λ]) ⋙ R(f')_![ModuleCat.{u + 1} Λ] :=
  sorry

/-- Blueprint `sk-prop-sf-cbc`: Compact-support base change

**Compact-support base change.** For `f : X ⟶ Y` separated of finite type, `g : Y' ⟶ Y`
arbitrary and a cartesian square, the exchange transformation
`Ex_! : Lg^* Rf_! ⟶ Rf'_! Lg'^*` of `sk-def-sf-exchanges` is an isomorphism at every
coefficient stage, naturally in the coefficient complex and coherently for identity and pasted
squares.

The proof is the five-stage argument of the compact-support base change chapter: finite
coefficients on the étale site, degreewise constructibility, the pro-étale finite level for
objects with an étale-origin witness, completed coefficients, and finite extensions of the
coefficient field. -/
theorem nonempty_iso_upperStar_comp_rightDerivedLowerShriek (_sq : IsPullback g' f' f g) :
    Nonempty (R(f)_![ModuleCat.{u + 1} Λ] ⋙ L((g)^*[ModuleCat.{u + 1} Λ]) ≅
      L((g')^*[ModuleCat.{u + 1} Λ]) ⋙ R(f')_![ModuleCat.{u + 1} Λ]) :=
  sorry

end Exchange

section Projection

variable (f : X ⟶ Y) [HasCompactification f]

/-- Blueprint `sk-thm-sf-pf-finite`: Projection formula, finite coefficients

**The projection formula at finite coefficients.** For `Λ` a finite coefficient ring,
`f : X ⟶ Y` separated of finite type, `K` bounded constructible on `X` and `L` bounded
constructible of finite Tor amplitude on `Y`, the projection map

`Rf_! K ⊗^L L ≅ Rf_!(K ⊗^L Lf^* L)`

is an isomorphism, naturally in `K` and `L`. -/
theorem nonempty_iso_derivedTensor_rightDerivedLowerShriek
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (L : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (_hK : Etale.DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) X K)
    (_hL : Etale.DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) Y L) :
    Nonempty (((Etale.derivedTensor (ModuleCat.{u + 1} Λ) Y).obj
          ((R(f)_![ModuleCat.{u + 1} Λ]).obj K)).obj L ≅
      (R(f)_![ModuleCat.{u + 1} Λ]).obj
        (((Etale.derivedTensor (ModuleCat.{u + 1} Λ) X).obj K).obj
          ((L((f)^*[ModuleCat.{u + 1} Λ])).obj L))) :=
  sorry

end Projection

/-- Reduction of coefficients along a quotient of the coefficient ring: the functor
`K ↦ K ⊗^L (Λ/J)_X` on `D(X_ét, Λ)`. For `Λ = A_{E,n}` and `J = ϖ^m` this is the finite
reduction `K ↦ K_m` of the adic formalism. -/
noncomputable def reduction (J : Ideal Λ) (X : Scheme.{u}) :
    _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ⥤
      _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
  (Etale.derivedTensor (ModuleCat.{u + 1} Λ) X).flip.obj
    ((_root_.DerivedCategory.singleFunctor _ 0).obj
      ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
        (ModuleCat.of Λ (Λ ⧸ J))))

/-- Blueprint `sk-prop-sf-pf-reduction`: Projection formula: compatibility with finite
reduction

The square comparing the projection map at `(K, L)` with the projection map at the finite
reductions `(K_m, L_m)`, through the finite-reduction compatibilities of `Rf_!`, `−⊗^L−` and
`Lf^*`, commutes; hence the projection formula holds at `(K, L)` if and only if it holds at
`(K_m, L_m)`. This is what reduces the projection formula at level `n` to the projection
formula at level `m ≤ n`. -/
theorem nonempty_iso_derivedTensor_rightDerivedLowerShriek_iff_reduction (f : X ⟶ Y)
    [HasCompactification f] (J : Ideal Λ)
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (L : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    Nonempty (((Etale.derivedTensor (ModuleCat.{u + 1} Λ) Y).obj
          ((R(f)_![ModuleCat.{u + 1} Λ]).obj K)).obj L ≅
        (R(f)_![ModuleCat.{u + 1} Λ]).obj
          (((Etale.derivedTensor (ModuleCat.{u + 1} Λ) X).obj K).obj
            ((L((f)^*[ModuleCat.{u + 1} Λ])).obj L))) ↔
      Nonempty (((Etale.derivedTensor (ModuleCat.{u + 1} Λ) Y).obj
          ((R(f)_![ModuleCat.{u + 1} Λ]).obj ((reduction Λ J X).obj K))).obj
            ((reduction Λ J Y).obj L) ≅
        (R(f)_![ModuleCat.{u + 1} Λ]).obj
          (((Etale.derivedTensor (ModuleCat.{u + 1} Λ) X).obj ((reduction Λ J X).obj K)).obj
            ((L((f)^*[ModuleCat.{u + 1} Λ])).obj ((reduction Λ J Y).obj L)))) :=
  sorry

end Etale

end AlgebraicGeometry
