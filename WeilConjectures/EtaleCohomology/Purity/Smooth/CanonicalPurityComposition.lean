/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.CanonicalPurityBaseChange
public import WeilConjectures.EtaleCohomology.Purity.Smooth.Trace
public import WeilConjectures.EtaleCohomology.Purity.Smooth.TraceDiagonal.Basic

/-!
# Compatibility of the canonical purity map with composition

For `f : X ⟶ Y` and `g : Y ⟶ Z` smooth separated of pure relative dimensions `d` and `e`, the
canonical purity map of `f ≫ g` (`AlgebraicGeometry.Etale.canonicalSmoothPurityMap`) is the
composite

`L(f ≫ g)^* K(d + e)[2d + 2e] ≅ Lf^*(Lg^* K(e)[2e])(d)[2d] ⟶ Lf^*(Rg^! K)(d)[2d] ⟶ Rf^! Rg^! K`
`  ≅ R(f ≫ g)^! K`

of `Lf^*(γ_g(K))(d)[2d]` and `γ_f(Rg^! K)`, the sources being identified by
`AlgebraicGeometry.Etale.twistShiftCompIso` and the targets by the composition isomorphism of the
exceptional inverse images conjugate to the composition isomorphism of `R_!`
(`AlgebraicGeometry.Etale.rightDerivedLowerShriekCompIso`). This is blueprint
`proposition-compatibility-purity-composition--1` (finite coefficients).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

open Scheme

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] [HasKummerClass Λ]
  [HasKummerClass.IsNormalized Λ]

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (d e : ℕ)
  [SmoothOfRelativeDimension d f] [SmoothOfRelativeDimension e g] [IsSeparated f] [IsSeparated g]
  [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
  [QuasiCompact (f ≫ g)] [HasInvertibleExponent Λ X] [HasInvertibleExponent Λ Y]
  {k : Type u} [Field k] (aY : Y ⟶ Spec (.of k)) [IsSeparated aY] [LocallyOfFiniteType aY]
  (aZ : Z ⟶ Spec (.of k)) [IsSeparated aZ] [LocallyOfFiniteType aZ]

/-- Blueprint `proposition-compatibility-purity-composition--1`: **compatibility of the
canonical purity map with composition**, finite coefficients. For `K ∈ D(Z_ét, Λ)`,

`γ_{f ≫ g}(K) = c_{g,f}⁻¹ ∘ γ_f(Rg^! K) ∘ Lf^*(γ_g(K))(d)[2d]`

after the identification `L(f ≫ g)^* K(d + e)[2d + 2e] ≅ Lf^*(Lg^* K(e)[2e])(d)[2d]`
(`AlgebraicGeometry.Etale.twistShiftCompIso`), where `c_{g,f}⁻¹ : Rf^! Rg^! ≅ R(f ≫ g)^!` is the
composition isomorphism conjugate to `R(f ≫ g)_! ≅ Rf_! ⋙ Rg_!`
(`AlgebraicGeometry.Etale.rightDerivedLowerShriekCompIso`).

TODO: the blueprint proof reduces, by the tensor form of the purity maps, to the compatibility
of the canonical orientations `θ` (the diagonal classes) with composition. -/
theorem canonicalSmoothPurityMap_comp
    (K : _root_.DerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    canonicalSmoothPurityMap Λ (f ≫ g) (d + e) aZ K =
      (twistShiftCompIso Λ f g d e K).hom ≫
        (twistShift Λ X d).map
          ((L((f)^*[ModuleCat.{u + 1} Λ])).map (canonicalSmoothPurityMap Λ g e aZ K)) ≫
        canonicalSmoothPurityMap Λ f d aY ((R(g)^![Λ]).obj K) ≫
        (rightDerivedUpperShriekCompIsoOfLowerShriek Λ f g
          (rightDerivedLowerShriekCompIso Λ f g)).hom.app K := by
  sorry

end AlgebraicGeometry.Etale
