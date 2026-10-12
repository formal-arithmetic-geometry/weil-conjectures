/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.FreeSheaf

/-!
# Continuity of étale cohomology at cofiltered limits, colimit form

Let `Z` be a scheme, `F` a sheaf of `Λ`-modules on `Z_ét` and `(Xᵢ)` a cofiltered system of
quasi-compact quasi-separated schemes over `Z` with affine transition morphisms and limit `X`.
Then `H^q(X, F|_X) = colimᵢ H^q(Xᵢ, F|_{Xᵢ})` ([Stacks, Tag 09YQ]). This is blueprint
`lemma-weil-pbc-etale-cohomology-continuity`, which belongs to the subsection `sk-prop-h2`; its
proof is not formalised here. Its vanishing form is
`AlgebraicGeometry.Etale.isZero_rightDerived_sectionsFunctor_upperStar_of_isLimit`.

For a scheme `x : X ⟶ Z` over `Z`, the cohomology `H^q(X, F|_X)` is written
`Hom(x^*(Λ_Z[0]), (x^*(F[0]))⟦q⟧)` in the bounded below derived category of `X_ét`, where
`Λ_Z` is the constant sheaf `Λ` on `Z` (the free sheaf on the final object), so that
`x^* Λ_Z = Λ_X`, and the pullback maps are induced by the derived pullbacks
(`AlgebraicGeometry.Etale.overCohomologyMap`).

## Main definitions

- `AlgebraicGeometry.Etale.overCohomology`: `H^q(X, F|_X)` for `X` over `Z`.
- `AlgebraicGeometry.Etale.overCohomologyMap`: the pullback map
  `H^q(Y, F|_Y) ⟶ H^q(X, F|_X)` along a morphism `X ⟶ Y` over `Z`.

## Main statements

- `AlgebraicGeometry.Etale.overCohomologyMap_isColimit_of_isLimit`: continuity of étale
  cohomology at cofiltered limits with affine transition morphisms.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- The étale cohomology `H^q(X, F|_X)` of a scheme `x : X ⟶ Z` over `Z` with coefficients in
the pullback of a sheaf `F` of `Λ`-modules on `Z_ét`, written as
`Hom(x^*(Λ_Z[0]), (x^*(F[0]))⟦q⟧)` in `D⁺(X_ét)`; here `x^*(Λ_Z[0]) ≅ Λ_X[0]` and
`x^*(F[0]) ≅ (F|_X)[0]`. -/
abbrev Etale.overCohomology {Z : Scheme.{u}} (F : Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (q : ℤ) (X : Over Z) :=
  D+((X.hom)^*[ModuleCat.{u + 1} Λ]).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj
      ((Etale.freeSheaf Λ Z).obj (Etale.finalObject Z))) ⟶
    (D+((X.hom)^*[ModuleCat.{u + 1} Λ]).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj F))⟦q⟧

/-- The pullback map `H^q(Y, F|_Y) ⟶ H^q(X, F|_X)` on the étale cohomology of schemes over `Z`
(`AlgebraicGeometry.Etale.overCohomology`) along a morphism `φ : X ⟶ Y` over `Z`: apply the
derived pullback along `φ` and use `x^* ≅ φ^* y^*`. -/
noncomputable def Etale.overCohomologyMap {Z : Scheme.{u}}
    (F : Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℤ) {X Y : Over Z} (φ : X ⟶ Y)
    (α : Etale.overCohomology Λ F q Y) : Etale.overCohomology Λ F q X :=
  (Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) φ.left Y.hom X.hom
      (Over.w φ).symm).hom.app _ ≫
    D+((φ.left)^*[ModuleCat.{u + 1} Λ]).map α ≫
    (D+((φ.left)^*[ModuleCat.{u + 1} Λ]).commShiftIso q).hom.app _ ≫
    ((Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) φ.left Y.hom X.hom
      (Over.w φ).symm).inv.app _)⟦q⟧'

/-- Blueprint `lemma-weil-pbc-etale-cohomology-continuity`: Etale cohomology continuity.

Let `(Dᵢ)` be a cofiltered system of quasi-compact quasi-separated schemes over `Z` with affine
transition maps, with limit `X = c.pt`, and let `F` be a sheaf of `Λ`-modules on `Z_ét`. Then
`colimᵢ H^q(Dᵢ, F|_{Dᵢ}) ≅ H^q(X, F|_X)` through the pullback maps
`AlgebraicGeometry.Etale.overCohomologyMap`; this is stated as the two defining properties of a
filtered colimit: every class on `X` comes from some `Dᵢ`, and a class on `Dᵢ` vanishing on `X`
already vanishes on some `Dⱼ`, `j ⟶ i`. The blueprint assumes `F` torsion; the statement holds
for all sheaves (Stacks `09YQ`). For `q < 0` both sides vanish. -/
@[stacks 09YQ]
theorem Etale.overCohomologyMap_isColimit_of_isLimit {Z : Scheme.{u}}
    (F : Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ)) {I : Type u} [Category.{u} I]
    [IsCofiltered I] (D : I ⥤ Over Z) [∀ i, CompactSpace (D.obj i).left]
    [∀ i, QuasiSeparatedSpace (D.obj i).left] [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f).left]
    (c : Cone D) (hc : IsLimit ((Over.forget Z).mapCone c)) (q : ℤ) :
    (∀ y : Etale.overCohomology Λ F q c.pt, ∃ (i : I) (x : Etale.overCohomology Λ F q (D.obj i)),
      Etale.overCohomologyMap Λ F q (c.π.app i) x = y) ∧
    ∀ (i : I) (x : Etale.overCohomology Λ F q (D.obj i)),
      Etale.overCohomologyMap Λ F q (c.π.app i) x = 0 →
        ∃ (j : I) (f : j ⟶ i), Etale.overCohomologyMap Λ F q (D.map f) x = 0 :=
  sorry

end AlgebraicGeometry
