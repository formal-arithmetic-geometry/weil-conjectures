/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjection
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.FiniteCoefficients.Defs

/-!
# Étale projection morphisms at a finite coefficient ring

The étale projection morphisms used for the ordinary Künneth formula, for a commutative
coefficient ring `Λ` (for instance `Λ = 𝒪_E/ϖⁿ`): they are the projection maps of the
repository specialised to the coefficients `ModuleCat Λ`.

- `AlgebraicGeometry.Etale.lowerStarProjectionMapModule`:
  `Rf_* K ⊗ᴸ M ⟶ Rf_*(K ⊗ᴸ Lf^* M)`.
- `AlgebraicGeometry.Etale.unboundedLowerShriekCandidate`: `Rf^un_! = Rp_* ∘ D(j_!)`.
- `AlgebraicGeometry.Etale.openProjectionMapModule`:
  `σ_{j,K,N} : j_!(K ⊗ᴸ Lj^* N) ⟶ j_! K ⊗ᴸ N`.
- `AlgebraicGeometry.Etale.compactProjectionMapModule`:
  `PF_{f,K,L} : Rf^un_! K ⊗ᴸ L ⟶ Rf^un_!(K ⊗ᴸ Lf^* L)`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- The étale direct-image projection morphism: for `f : X ⟶ Y`, `K ∈ D(X_ét, Λ)` and
`M ∈ D(Y_ét, Λ)`, the morphism `P_{f,K,M} : Rf_* K ⊗ᴸ M ⟶ Rf_*(K ⊗ᴸ Lf^* M)` corresponding
under `Lf^* ⊣ Rf_*` to the derived monoidal comparison followed by `ε_K ⊗ 1`. -/
noncomputable abbrev lowerStarProjectionMapModule {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (M : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    ((-⊗ᴸ-(Y)[ModuleCat.{u + 1} Λ]).obj ((rightDerivedLowerStarModule Λ f).obj K)).obj M ⟶
      (rightDerivedLowerStarModule Λ f).obj (((-⊗ᴸ-(X)[ModuleCat.{u + 1} Λ]).obj K).obj
        (L((f)^*[ModuleCat.{u + 1} Λ]).obj M)) :=
  ((rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} Λ) f).app K).app M

/-- The unbounded étale compactification candidate: for a compactification `c = (j, p)` of
`f : X ⟶ Y` (`f = j ≫ p`, `j` an open immersion, `p` proper),
`Rf^un_! := Rp_* ∘ D(j_!) : D(X_ét, Λ) ⥤ D(Y_ét, Λ)`. -/
noncomputable abbrev unboundedLowerShriekCandidate {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) :
    DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ⥤
      DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
  Rf_!(c)[ModuleCat.{u + 1} Λ]

/-- The unbounded candidate is `Rp_* ∘ D(j_!)`. -/
lemma unboundedLowerShriekCandidate_eq {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :
    unboundedLowerShriekCandidate Λ c =
      D((c.i)_!open[ModuleCat.{u + 1} Λ]) ⋙ rightDerivedLowerStarModule Λ c.g :=
  rfl

/-- The étale open-extension projection map: for an open immersion `j : U ⟶ X`,
`K ∈ D(U_ét, Λ)` and `N ∈ D(X_ét, Λ)`, the map `σ_{j,K,N} : j_!(K ⊗ᴸ Lj^* N) ⟶ j_! K ⊗ᴸ N`. -/
noncomputable abbrev openProjectionMapModule {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (K : DerivedCategory (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (N : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    D((j)_!open[ModuleCat.{u + 1} Λ]).obj (((-⊗ᴸ-(U)[ModuleCat.{u + 1} Λ]).obj K).obj
        (L((j)^*[ModuleCat.{u + 1} Λ]).obj N)) ⟶
      ((-⊗ᴸ-(X)[ModuleCat.{u + 1} Λ]).obj (D((j)_!open[ModuleCat.{u + 1} Λ]).obj K)).obj N :=
  ((derivedOpenImmersionLowerShriekProjectionMap (ModuleCat.{u + 1} Λ) j).app K).app N

/-- The étale compact-support projection map: for a compactification `c = (j, p)` of `f`,
`K ∈ D(X_ét, Λ)` and `L ∈ D(Y_ét, Λ)`, the map
`PF_{f,K,L} : Rf^un_! K ⊗ᴸ L ⟶ Rf^un_!(K ⊗ᴸ Lf^* L)`, built from the projection map of `p` and
the inverse of the open-extension projection map of `j`. -/
noncomputable abbrev compactProjectionMapModule {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f)
    (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (L : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    ((-⊗ᴸ-(Y)[ModuleCat.{u + 1} Λ]).obj ((unboundedLowerShriekCandidate Λ c).obj K)).obj L ⟶
      (unboundedLowerShriekCandidate Λ c).obj (((-⊗ᴸ-(X)[ModuleCat.{u + 1} Λ]).obj K).obj
        (L((f)^*[ModuleCat.{u + 1} Λ]).obj L)) :=
  ((projectionMapOfCompactification (ModuleCat.{u + 1} Λ) c).app K).app L

end Etale

end AlgebraicGeometry
