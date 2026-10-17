/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.Orientation
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Comparison

/-!
# The Kummer generator and the orientation sheaf map

Let `π : 𝔾_{m,Y} ⟶ Y` be the multiplicative group, the complement of the zero section of
`𝔸¹_Y`, with coordinate `t`. The Kummer class `κ(t) ∈ H¹(𝔾_{m,Y}, Λ(1))` defines a section of
the sheaf `R¹π_* Λ(1)`, whence the *Kummer generator* `κ_Y : Λ_Y ⟶ R¹π_* Λ(1)`
(`pur9-def-kummer-generator`), and its pro-étale counterpart (`pur9-def-kummer-generator-proet`).
The orientation `pur_s` of the zero section (`AlgebraicGeometry.Etale.affineLineOrientation`)
induces on cohomology sheaves the *orientation sheaf map* `o_Y : Λ_Y ⟶ H²(Rs^! Λ(1))`
(`pur9-def-orientation-sheaf-map`).

## Main definitions

- `AlgebraicGeometry.Etale.multiplicativeGroupProj`: `π : 𝔾_{m,Y} ⟶ Y`.
- `AlgebraicGeometry.Etale.kummerGeneratorDerived`: `Λ_Y ⟶ Rπ_*(Λ(1))[1]`.
- `AlgebraicGeometry.Etale.kummerGenerator`: `κ_Y : Λ_Y ⟶ R¹π_* Λ(1)`.
- `AlgebraicGeometry.Etale.kummerGeneratorProet`: the pro-étale Kummer generator.
- `AlgebraicGeometry.Etale.orientationSheafMap`: `o_Y : Λ_Y ⟶ H²(Rs^! Λ(1))`.
-/

@[expose] public section

universe u

open CategoryTheory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] [HasKummerClass Λ] (Y : Scheme.{u})
  [HasInvertibleExponent Λ Y]

/-- The multiplicative group `𝔾_{m,Y}`: the basic open of the coordinate `t` of `𝔸¹_Y`, the
complement of the zero section. -/
noncomputable abbrev multiplicativeGroupOpen : (𝔸(ULift.{u} (Fin 1); Y)).Opens :=
  (𝔸(ULift.{u} (Fin 1); Y)).basicOpen (AffineSpace.coord Y (ULift.up 0))

/-- The projection `π : 𝔾_{m,Y} ⟶ Y`. -/
noncomputable abbrev multiplicativeGroupProj : (multiplicativeGroupOpen Y).toScheme ⟶ Y :=
  (multiplicativeGroupOpen Y).ι ≫ 𝔸(ULift.{u} (Fin 1); Y) ↘ Y

instance : HasInvertibleExponent Λ (multiplicativeGroupOpen Y).toScheme :=
  .of_hom (multiplicativeGroupProj Y)

/-- The Kummer class `κ(t) ∈ H¹(𝔾_{m,Y}, Λ(1))` of the coordinate, read through the adjunction
`Lπ^* ⊣ Rπ_*` as a morphism `Λ_Y ⟶ Rπ_*(Λ(1))[1]`. -/
noncomputable def kummerGeneratorDerived :
    constantComplex Λ Y ⟶ (R((multiplicativeGroupProj Y)_*[ModuleCat.{u + 1} Λ])).obj
      ((tateObject Λ (multiplicativeGroupOpen Y).toScheme 1)⟦(1 : ℤ)⟧) :=
  (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) (multiplicativeGroupProj Y)).homEquiv
    _ _ ((leftDerivedUpperStarConstantComplexIso Λ (multiplicativeGroupProj Y)).hom ≫
      kummerClass Λ ((𝔸(ULift.{u} (Fin 1); Y)).basicOpenUnit (AffineSpace.coord Y (ULift.up 0))))

/-- Blueprint `pur9-def-kummer-generator`: The Kummer generator over `Y`

`κ_Y : Λ_Y ⟶ R¹π_* Λ(1)` for `π : 𝔾_{m,Y} ⟶ Y`, the morphism of sheaves sending `1` to the
section defined by the Kummer class `κ(t)` of the coordinate: the zeroth cohomology sheaf of
`AlgebraicGeometry.Etale.kummerGeneratorDerived`, through `H⁰((Rπ_* Λ(1))[1]) = R¹π_* Λ(1)`.
Its source `H⁰(Λ_Y)` is the constant sheaf `Λ_Y`. -/
noncomputable def kummerGenerator :
    (_root_.DerivedCategory.homologyFunctor _ 0).obj (constantComplex Λ Y) ⟶
      (_root_.DerivedCategory.homologyFunctor _ 1).obj
        ((R((multiplicativeGroupProj Y)_*[ModuleCat.{u + 1} Λ])).obj
          (tateObject Λ (multiplicativeGroupOpen Y).toScheme 1)) :=
  (_root_.DerivedCategory.homologyFunctor _ 0).map (kummerGeneratorDerived Λ Y ≫
      ((R((multiplicativeGroupProj Y)_*[ModuleCat.{u + 1} Λ])).commShiftIso (1 : ℤ)).hom.app _) ≫
    ((_root_.DerivedCategory.homologyFunctor _ 0).shiftIso 1 0 1 (by norm_num)).hom.app _

/-- Blueprint `pur9-def-kummer-generator-proet`: The pro-étale Kummer generator

The pro-étale Kummer generator: the comparison functor `ν^*` from étale to pro-étale sheaves
applied to the Kummer generator `κ_Y : Λ_Y ⟶ R¹π_* Λ(1)`
(`AlgebraicGeometry.Etale.kummerGenerator`). The blueprint further identifies the target
`ν^* R¹π_{*,ét} Λ(1)` with the pro-étale `R¹π_* Λ(1)` through the direct-image comparison
`λ_π`; that identification is not part of the morphism recorded here. -/
noncomputable def kummerGeneratorProet :
    (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} Λ) Y).obj
        ((_root_.DerivedCategory.homologyFunctor _ 0).obj (constantComplex Λ Y)) ⟶
      (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} Λ) Y).obj
        ((_root_.DerivedCategory.homologyFunctor _ 1).obj
          ((R((multiplicativeGroupProj Y)_*[ModuleCat.{u + 1} Λ])).obj
            (tateObject Λ (multiplicativeGroupOpen Y).toScheme 1))) :=
  (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} Λ) Y).map (kummerGenerator Λ Y)

/-- Blueprint `pur9-def-orientation-sheaf-map`: The orientation sheaf map

`o_Y : Λ_Y ⟶ H²(Rs^! Λ(1)) = H⁰(Rs^! Λ(1)[2])` for the zero section `s : V(t) ⟶ 𝔸¹_Y`: the map
induced on zeroth cohomology sheaves by the orientation
`pur_s = ∂κ(t) : Λ ⟶ Rs^! Λ(1)[2]` (`AlgebraicGeometry.Etale.affineLineOrientation`). The
Kummer boundary `∂κ(t)` is the Kummer class `κ(t)` followed by the boundary `δ` of the supported
localization triangle (`AlgebraicGeometry.Etale.kummerBoundary`), so `o_Y` is the Kummer
generator followed by `H¹(δ)`, as in the blueprint. For a normalized rank-one datum it is an
isomorphism (`AlgebraicGeometry.Etale.isIso_homology_zero_map_affineLineOrientation`). -/
noncomputable def orientationSheafMap :
    (_root_.DerivedCategory.homologyFunctor _ 0).obj (constantComplex Λ
        (𝔸(ULift.{u} (Fin 1); Y).zeroLocusSubscheme {AffineSpace.coord Y (ULift.up 0)})) ⟶
      (_root_.DerivedCategory.homologyFunctor _ 0).obj
        ((R(𝔸(ULift.{u} (Fin 1); Y).zeroLocusSubschemeι
          {AffineSpace.coord Y (ULift.up 0)})^![ModuleCat.{u + 1} Λ]).obj
          ((tateObject Λ 𝔸(ULift.{u} (Fin 1); Y) 1)⟦(2 : ℤ)⟧)) :=
  (_root_.DerivedCategory.homologyFunctor _ 0).map (affineLineOrientation Λ Y)

end Etale

end AlgebraicGeometry
