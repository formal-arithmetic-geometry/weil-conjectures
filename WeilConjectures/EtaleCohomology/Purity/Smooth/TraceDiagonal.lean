/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.TraceDiagonal.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.UpperShriek

/-!
# Trace–diagonal data and the trace–diagonal criterion

Let `f : X ⟶ Y` be a separated, quasi-compact morphism admitting a compactification, let
`Λ` be a finite commutative ring and let `L ∈ D(X_ét, Λ)`. Write `W = X ×_Y X` with projections
`p₁, p₂` and diagonal `Δ`. A *trace–diagonal datum* for `(f, L)` is a pair of morphisms
```
tr_f : Rf_! L ⟶ Λ_Y,        cl_Δ : RΔ_! Λ_X ⟶ Lp₂^* L.
```
It induces the functor `G_L = Lf^*(-) ⊗ᴸ L : D(Y_ét, Λ) ⥤ D(X_ét, Λ)`, a *counit*
`Rf_! G_L ⟶ 𝟭` built from `tr_f` and the projection formula, and a *unit* `𝟭 ⟶ G_L Rf_!` built
from `cl_Δ`, the projection formula for `Δ` and `p₂`, the composition `R(Δ ≫ p₂)_! = R(𝟙)_!`
and proper base change `Lf^* Rf_! ≅ Rp₂_! Lp₁^*` (blueprint `def-pur-td-datum`).

If the two triangular composites are identities, then `Rf_! ⊣ G_L`, so that `G_L` is the
exceptional inverse image: `Rf^! ≅ Lf^*(-) ⊗ᴸ L` and `ω_f = Rf^! Λ_Y ≅ L`
(blueprint `thm-pur-td-criterion`).

## Implementation notes

* Everything is stated on the ambient unbounded derived categories `D(X_ét, Λ)`, where the
  exceptional inverse image `Rf^!` is defined as the right adjoint of `Rf_!`
  (`AlgebraicGeometry.Etale.rightDerivedUpperShriek`); this is the ambient right adjoint the
  blueprint invokes (`cor-sf-ambient-adjoint-discharge`). The criterion is then a statement
  about functors on all of `D(X_ét, Λ)` and `D(Y_ét, Λ)`, and the triangular identities are
  assumed for all objects.
* The derived tensor product has a symmetry only as an existence statement
  (`AlgebraicGeometry.Etale.nonempty_iso_derivedTensor_flip`); the unit and counit use one
  chosen symmetry `AlgebraicGeometry.Etale.derivedTensorFlipIso`, because the projection map
  `Rf_! K ⊗ᴸ M ⟶ Rf_!(K ⊗ᴸ Lf^* M)` puts the pulled-back factor on the right. The criterion
  holds for any choice.
* The unit `Λ_X` is written `AlgebraicGeometry.Etale.derivedTensorUnit`, defined over a general
  coefficient category: for `A = ModuleCat Λ`, the monoidal instance on `D(X_ét)` found by
  instance search is a different term from the one inside `derivedTensor` and its unitors, and
  the kernel does not compare the two in reasonable time (see
  `WeilConjectures.SixFunctors.Etale.Derived.TensorStructure`).

## Main definitions

- `AlgebraicGeometry.Etale.TraceDiagonalDatum`: a trace–diagonal datum.
- `AlgebraicGeometry.Etale.TraceDiagonalDatum.functor`: `G_L = Lf^*(-) ⊗ᴸ L`.
- `AlgebraicGeometry.Etale.TraceDiagonalDatum.counit`, `...unit`: counit and unit.
- `AlgebraicGeometry.Etale.TraceDiagonalDatum.leftTriangle`, `...rightTriangle`: the
  triangular composites.

## Main statements

- `AlgebraicGeometry.Etale.TraceDiagonalDatum.adjunction`: `Rf_! ⊣ G_L`.
- `AlgebraicGeometry.Etale.TraceDiagonalDatum.rightDerivedUpperShriekIso`: `Rf^! ≅ G_L`,
  compatible with the counits, and unique such
  (`AlgebraicGeometry.Etale.TraceDiagonalDatum.rightDerivedUpperShriekIso_unique`).
- `AlgebraicGeometry.Etale.TraceDiagonalDatum.dualizingComplexIso`: `ω_f ≅ L`.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ]

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f] [QuasiCompact f]
  [IsSeparated f]

/-- Blueprint `def-pur-td-datum`: Trace–diagonal datum

For `f : X ⟶ Y` with `W = X ×_Y X`, projections `p₁, p₂` and diagonal `Δ`, and an object
`L ∈ D(X_ét, Λ)` (in the blueprint a ⊗-invertible object of `D^b_{ctf}(X, Λ)`), a
*trace–diagonal datum* for `(f, L)` is a pair
```
tr_f : Rf_! L ⟶ Λ_Y,        cl_Δ : RΔ_! Λ_X ⟶ Lp₂^* L.
```
The induced functor, counit, unit and triangular composites are
`AlgebraicGeometry.Etale.TraceDiagonalDatum.functor`, `...counit`, `...unit`,
`...leftTriangle` and `...rightTriangle`. -/
structure TraceDiagonalDatum (L : DerivedCategoryModule Λ X) where
  /-- The trace `tr_f : Rf_! L ⟶ Λ_Y`. -/
  trace : (R(f)_![ModuleCat.{u + 1} Λ]).obj L ⟶ derivedTensorUnit _ Y
  /-- The diagonal class `cl_Δ : RΔ_! Λ_X ⟶ Lp₂^* L`. -/
  diagonalClass : (R(pullback.diagonal f)_![ModuleCat.{u + 1} Λ]).obj (derivedTensorUnit _ X) ⟶
    (L((pullback.snd f f)^*[ModuleCat.{u + 1} Λ])).obj L

namespace TraceDiagonalDatum

variable {Λ f} {L : DerivedCategoryModule Λ X} (d : TraceDiagonalDatum Λ f L)

/-- Blueprint `def-pur-td-datum`: Trace–diagonal datum

The *induced functor* `G_L = Lf^*(-) ⊗ᴸ L : D(Y_ét, Λ) ⥤ D(X_ét, Λ)`. It depends only on
`L`. -/
@[nolint unusedArguments]
noncomputable def functor (_d : TraceDiagonalDatum Λ f L) :
    DerivedCategoryModule Λ Y ⥤ DerivedCategoryModule Λ X :=
  (L((f)^*[ModuleCat.{u + 1} Λ])) ⋙ derivedTensorRight (ModuleCat.{u + 1} Λ) X L

/-- Blueprint `def-pur-td-datum`: Trace–diagonal datum

The *counit* `ε_K : Rf_! G_L(K) ≅ Rf_! L ⊗ᴸ K ⟶ Λ_Y ⊗ᴸ K ≅ K`: the symmetry, the inverse of the
projection formula, `tr_f ⊗ 𝟙` and the left unitor. -/
noncomputable def counit : d.functor ⋙ (R(f)_![ModuleCat.{u + 1} Λ]) ⟶ 𝟭 _ :=
  (Functor.associator (L((f)^*[ModuleCat.{u + 1} Λ])) (derivedTensorRight _ X L)
      (R(f)_![ModuleCat.{u + 1} Λ])).hom ≫
    Functor.whiskerLeft (L((f)^*[ModuleCat.{u + 1} Λ]))
      (Functor.whiskerRight ((derivedTensorFlipIso _ X).app L).inv
        (R(f)_![ModuleCat.{u + 1} Λ])) ≫
    (projectionIso Λ f L).inv ≫ (derivedTensor (ModuleCat.{u + 1} Λ) Y).map d.trace ≫
    (derivedTensorUnitLeftUnitor (ModuleCat.{u + 1} Λ) Y).hom

/-- Blueprint `def-pur-td-datum`: Trace–diagonal datum

The *unit* `η_A : A ≅ Rp₂_!(RΔ_! Λ_X ⊗ᴸ Lp₁^* A) ⟶ Rp₂_!(Lp₂^* L ⊗ᴸ Lp₁^* A) ≅ G_L(Rf_! A)`:
the first isomorphism is `R(Δ ≫ p₂)_! = R(𝟙)_! ≅ 𝟭` with the projection formula for `Δ`
(`AlgebraicGeometry.Etale.TraceDiagonalDatum.diagonalIso`), the middle map is `cl_Δ ⊗ 𝟙`, and
the last isomorphism is the symmetry, the projection formula for `p₂` and proper base change
`Lf^* Rf_! ≅ Rp₂_! Lp₁^*`. -/
noncomputable def unit : 𝟭 _ ⟶ (R(f)_![ModuleCat.{u + 1} Λ]) ⋙ d.functor :=
  (idIsoDiagonalSnd f).hom ≫
    Functor.whiskerRight (diagonalIso f).hom (R(pullback.snd f f)_![ModuleCat.{u + 1} Λ]) ≫
    Functor.whiskerRight (Functor.whiskerLeft (L((pullback.fst f f)^*[ModuleCat.{u + 1} Λ]))
      ((derivedTensor (ModuleCat.{u + 1} Λ) (pullback f f)).map d.diagonalClass ≫
        ((derivedTensorFlipIso _ (pullback f f)).app _).hom))
      (R(pullback.snd f f)_![ModuleCat.{u + 1} Λ]) ≫
    (sndProjectionIso f L).hom

/-- Blueprint `def-pur-td-datum`: Trace–diagonal datum

The first *triangular composite* `Rf_! A ⟶ Rf_! G_L Rf_! A ⟶ Rf_! A`, that is
`ε_{Rf_! A} ∘ Rf_! η_A`, natural in `A`. -/
noncomputable def leftTriangle :
    R(f)_![ModuleCat.{u + 1} Λ] ⟶ R(f)_![ModuleCat.{u + 1} Λ] :=
  (Functor.leftUnitor _).inv ≫ Functor.whiskerRight d.unit _ ≫ (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft _ d.counit ≫ (Functor.rightUnitor _).hom

/-- Blueprint `def-pur-td-datum`: Trace–diagonal datum

The second *triangular composite* `G_L K ⟶ G_L Rf_! G_L K ⟶ G_L K`, that is
`G_L ε_K ∘ η_{G_L K}`, natural in `K`. -/
noncomputable def rightTriangle : d.functor ⟶ d.functor :=
  (Functor.rightUnitor _).inv ≫ Functor.whiskerLeft _ d.unit ≫ (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight d.counit _ ≫ (Functor.leftUnitor _).hom

/-- The components of the first triangular composite: `ε_{Rf_! A} ∘ Rf_! η_A`. -/
lemma leftTriangle_app (A : DerivedCategoryModule Λ X) :
    d.leftTriangle.app A =
      (R(f)_![ModuleCat.{u + 1} Λ]).map (d.unit.app A) ≫
        d.counit.app ((R(f)_![ModuleCat.{u + 1} Λ]).obj A) := by
  simp [leftTriangle]

/-- The components of the second triangular composite: `G_L ε_K ∘ η_{G_L K}`. -/
lemma rightTriangle_app (K : DerivedCategoryModule Λ Y) :
    d.rightTriangle.app K = d.unit.app (d.functor.obj K) ≫ d.functor.map (d.counit.app K) := by
  simp [rightTriangle]

variable (hl : d.leftTriangle = 𝟙 _) (hr : d.rightTriangle = 𝟙 _)

/-- Blueprint `thm-pur-td-criterion`: Trace–diagonal criterion

If the two triangular composites of a trace–diagonal datum are the identity, then the unit and
counit exhibit `G_L = Lf^*(-) ⊗ᴸ L` as a right adjoint of `Rf_!`: the two assumed equations are
the triangular identities. -/
noncomputable def adjunction : R(f)_![ModuleCat.{u + 1} Λ] ⊣ d.functor :=
  Adjunction.mkOfUnitCounit
    { unit := d.unit
      counit := d.counit
      left_triangle := by
        ext A
        simpa [leftTriangle_app] using NatTrans.congr_app hl A
      right_triangle := by
        ext K
        simpa [rightTriangle_app] using NatTrans.congr_app hr K }

@[simp]
lemma adjunction_unit : (d.adjunction hl hr).unit = d.unit :=
  rfl

@[simp]
lemma adjunction_counit : (d.adjunction hl hr).counit = d.counit :=
  rfl

/-- Blueprint `thm-pur-td-criterion`: Trace–diagonal criterion

If the two triangular composites are the identity, the exceptional inverse image is
`Rf^! ≅ Lf^*(-) ⊗ᴸ L`, by uniqueness of right adjoints. -/
noncomputable def rightDerivedUpperShriekIso :
    R(f)^![ModuleCat.{u + 1} Λ] ≅ d.functor :=
  (rightDerivedUpperShriekAdjunction _ f).rightAdjointUniq (d.adjunction hl hr)

/-- Blueprint `thm-pur-td-criterion`: Trace–diagonal criterion

The isomorphism `Rf^! ≅ G_L` is compatible with the counits: the counit of `Rf_! ⊣ Rf^!` is
`ε ∘ Rf_!(Rf^! ≅ G_L)`. -/
theorem rightDerivedUpperShriekIso_hom_counit (K : DerivedCategoryModule Λ Y) :
    (R(f)_![ModuleCat.{u + 1} Λ]).map ((d.rightDerivedUpperShriekIso hl hr).hom.app K) ≫
      d.counit.app K = (rightDerivedUpperShriekAdjunction _ f).counit.app K :=
  by
  rw [rightDerivedUpperShriekIso, ← adjunction_counit d hl hr,
    Adjunction.rightAdjointUniq_hom_app_counit]

/-- Blueprint `thm-pur-td-criterion`: Trace–diagonal criterion

The isomorphism `Rf^! ≅ G_L` compatible with the counits is unique. -/
theorem rightDerivedUpperShriekIso_unique (e : R(f)^![ModuleCat.{u + 1} Λ] ≅ d.functor)
    (he : ∀ K, (R(f)_![ModuleCat.{u + 1} Λ]).map (e.hom.app K) ≫ d.counit.app K =
      (rightDerivedUpperShriekAdjunction _ f).counit.app K) :
    e = d.rightDerivedUpperShriekIso hl hr := by
  ext K
  apply ((d.adjunction hl hr).homEquiv _ _).symm.injective
  rw [Adjunction.homEquiv_counit, Adjunction.homEquiv_counit, adjunction_counit, he,
    rightDerivedUpperShriekIso_hom_counit]

/-- Blueprint `thm-pur-td-criterion`: Trace–diagonal criterion

If the two triangular composites are the identity, the dualizing complex of `f` is `L`:
`ω_f = Rf^! Λ_Y ≅ Lf^* Λ_Y ⊗ᴸ L ≅ Λ_X ⊗ᴸ L ≅ L`. -/
noncomputable def dualizingComplexIso :
    (R(f)^![ModuleCat.{u + 1} Λ]).obj (derivedTensorUnit _ Y) ≅ L :=
  (d.rightDerivedUpperShriekIso hl hr).app _ ≪≫
    (derivedTensorRight (ModuleCat.{u + 1} Λ) X L).mapIso
      (leftDerivedUpperStarDerivedTensorUnitIso f) ≪≫
    (derivedTensorUnitLeftUnitor (ModuleCat.{u + 1} Λ) X).app L

end TraceDiagonalDatum

end Etale

end AlgebraicGeometry
