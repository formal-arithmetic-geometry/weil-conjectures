/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Exchange
public import WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients

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

## Main definitions

- `AlgebraicGeometry.Etale.TraceDiagonalDatum`: a trace–diagonal datum.
- `AlgebraicGeometry.Etale.TraceDiagonalDatum.functor`: `G_L = Lf^*(-) ⊗ᴸ L`.
- `AlgebraicGeometry.Etale.TraceDiagonalDatum.counit`, `...unit`: counit and unit.
- `AlgebraicGeometry.Etale.TraceDiagonalDatum.leftTriangle`, `...rightTriangle`: the
  triangular composites.

## Main statements

- `AlgebraicGeometry.Etale.TraceDiagonalDatum.adjunction`: `Rf_! ⊣ G_L`.
- `AlgebraicGeometry.Etale.TraceDiagonalDatum.rightDerivedUpperShriekIso`: `Rf^! ≅ G_L`,
  compatible with the counits.
- `AlgebraicGeometry.Etale.TraceDiagonalDatum.nonempty_iso_dualizingComplex`: `ω_f ≅ L`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ]

section Generalities

/-- The derived lower shriek along equal morphisms: `R(f)_! ≅ R(f')_!` for `f = f'`. -/
noncomputable def rightDerivedLowerShriekCongrIso {X Y : Scheme.{u}} {f f' : X ⟶ Y}
    [HasCompactification f] [HasCompactification f'] (h : f = f') :
    R(f)_![ModuleCat.{u + 1} Λ] ≅ R(f')_![ModuleCat.{u + 1} Λ] := by
  subst h
  exact Iso.refl _

variable [Finite Λ]

/-- The composition isomorphism `R(f ≫ g)_! ≅ Rf_! ⋙ Rg_!` on the unbounded derived categories,
for torsion coefficients: the isomorphism of `sk-thm-sf-comp-composition`
(`AlgebraicGeometry.Etale.nonempty_iso_rightDerivedLowerShriek_comp`) as data. -/
noncomputable def rightDerivedLowerShriekCompIso {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S)
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    [QuasiCompact (f ≫ g)] :
    R(f ≫ g)_![ModuleCat.{u + 1} Λ] ≅
      R(f)_![ModuleCat.{u + 1} Λ] ⋙ R(g)_![ModuleCat.{u + 1} Λ] :=
  haveI : QuasiCompact f := .of_comp f g
  (rightDerivedLowerShriekIso Λ ((HasCompactification.compactification g).comp
      ((HasCompactification.compactification (f ≫ g)).ofComp
        (HasCompactification.compactification g)))).symm ≪≫
    (rightDerivedLowerShriekOfCompactificationCompIso Λ (HasCompactification.compactification g)
      ((HasCompactification.compactification (f ≫ g)).ofComp
        (HasCompactification.compactification g))).symm ≪≫
    Functor.isoWhiskerRight (rightDerivedLowerShriekIso Λ
      ((HasCompactification.compactification (f ≫ g)).ofComp
        (HasCompactification.compactification g)).restrict) _

end Generalities

/-- The derived pullback along the identity is the identity, `L(𝟙_X)^* ≅ 𝟭`. -/
noncomputable def leftDerivedUpperStarIdIso (X : Scheme.{u}) :
    L(((𝟙 X))^*[ModuleCat.{u + 1} Λ]) ≅ 𝟭 _ :=
  Functor.leftDerivedFunctorNatIso _ (Etale.upperStarId (ModuleCat.{u + 1} Λ) X) ≪≫
    (𝟭 _).leftDerivedFunctorIsoMapDerivedCategory ≪≫ Functor.mapDerivedCategoryIdIso _

/-- A chosen symmetry `K ⊗ᴸ M ≅ M ⊗ᴸ K` of the derived tensor product on `D(X_ét, Λ)`
(`AlgebraicGeometry.Etale.nonempty_iso_derivedTensor_flip`). -/
noncomputable def derivedTensorFlipIso (X : Scheme.{u}) :
    derivedTensor (ModuleCat.{u + 1} Λ) X ≅ (derivedTensor (ModuleCat.{u + 1} Λ) X).flip :=
  (nonempty_iso_derivedTensor_flip (ModuleCat.{u + 1} Λ) X).some

variable [Finite Λ] {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f] [QuasiCompact f]
  [IsSeparated f]

/-- The diagonal of a separated morphism admits a compactification, being a closed
immersion. -/
instance hasCompactification_diagonal : HasCompactification (pullback.diagonal f) :=
  inferInstance

/-- `Δ ≫ p₂ = 𝟙` admits a compactification. -/
instance hasCompactification_diagonal_snd :
    HasCompactification (pullback.diagonal f ≫ pullback.snd f f) := by
  rw [pullback.diagonal_snd]
  infer_instance

/-- `Δ ≫ p₂ = 𝟙` is quasi-compact. -/
instance quasiCompact_diagonal_snd : QuasiCompact (pullback.diagonal f ≫ pullback.snd f f) := by
  rw [pullback.diagonal_snd]
  infer_instance

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
  trace : (R(f)_![ModuleCat.{u + 1} Λ]).obj L ⟶ 𝟙_ _
  /-- The diagonal class `cl_Δ : RΔ_! Λ_X ⟶ Lp₂^* L`. -/
  diagonalClass : (R(pullback.diagonal f)_![ModuleCat.{u + 1} Λ]).obj (𝟙_ _) ⟶
    (L((pullback.snd f f)^*[ModuleCat.{u + 1} Λ])).obj L

namespace TraceDiagonalDatum

variable {Λ f} {L : DerivedCategoryModule Λ X} (d : TraceDiagonalDatum Λ f L)

/-- Blueprint `def-pur-td-datum`: Trace–diagonal datum

The *induced functor* `G_L = Lf^*(-) ⊗ᴸ L : D(Y_ét, Λ) ⥤ D(X_ét, Λ)`. It depends only on
`L`. -/
@[nolint unusedArguments]
noncomputable def functor (_d : TraceDiagonalDatum Λ f L) :
    DerivedCategoryModule Λ Y ⥤ DerivedCategoryModule Λ X :=
  L((f)^*[ModuleCat.{u + 1} Λ]) ⋙ derivedTensorRight (ModuleCat.{u + 1} Λ) X L

/-- The projection formula `Rf_! L ⊗ᴸ K ≅ Rf_!(L ⊗ᴸ Lf^* K)`, as an isomorphism of functors of
`K`. -/
noncomputable def projectionIso {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]
    (L : DerivedCategoryModule Λ X) :
    (derivedTensor (ModuleCat.{u + 1} Λ) Y).obj ((R(f)_![ModuleCat.{u + 1} Λ]).obj L) ≅
      L((f)^*[ModuleCat.{u + 1} Λ]) ⋙ (derivedTensor (ModuleCat.{u + 1} Λ) X).obj L ⋙
        R(f)_![ModuleCat.{u + 1} Λ] :=
  haveI := isIso_projectionMap_of_finite Λ f
  asIso ((projectionMap (ModuleCat.{u + 1} Λ) f).app L)

/-- The projection formula `Rf_! K ⊗ᴸ M ≅ Rf_!(K ⊗ᴸ Lf^* M)`, as an isomorphism of functors of
`K`. -/
noncomputable def projectionRightIso {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]
    (M : DerivedCategoryModule Λ Y) :
    R(f)_![ModuleCat.{u + 1} Λ] ⋙ derivedTensorRight (ModuleCat.{u + 1} Λ) Y M ≅
      derivedTensorRight (ModuleCat.{u + 1} Λ) X ((L((f)^*[ModuleCat.{u + 1} Λ])).obj M) ⋙
        R(f)_![ModuleCat.{u + 1} Λ] :=
  haveI := isIso_projectionMap_of_finite Λ f
  asIso (((flipFunctor _ _ _).map (projectionMap (ModuleCat.{u + 1} Λ) f)).app M)

/-- Blueprint `def-pur-td-datum`: Trace–diagonal datum

The *counit* `ε_K : Rf_! G_L(K) ≅ Rf_! L ⊗ᴸ K ⟶ Λ_Y ⊗ᴸ K ≅ K`: the symmetry, the inverse of the
projection formula, `tr_f ⊗ 𝟙` and the left unitor. -/
noncomputable def counit : d.functor ⋙ R(f)_![ModuleCat.{u + 1} Λ] ⟶ 𝟭 _ :=
  (Functor.associator L((f)^*[ModuleCat.{u + 1} Λ]) (derivedTensorRight _ X L)
      R(f)_![ModuleCat.{u + 1} Λ]).hom ≫
    Functor.whiskerLeft L((f)^*[ModuleCat.{u + 1} Λ])
      (Functor.whiskerRight ((derivedTensorFlipIso Λ X).app L).inv R(f)_![ModuleCat.{u + 1} Λ]) ≫
    (projectionIso f L).inv ≫ (derivedTensor (ModuleCat.{u + 1} Λ) Y).map d.trace ≫
    (derivedTensorLeftUnitorNatIso (ModuleCat.{u + 1} Λ) Y).hom

/-- The isomorphism `LΔ^* ⋙ RΔ_! ≅ RΔ_! Λ_X ⊗ᴸ -`: the left unitor and the projection formula
for `Δ`. -/
noncomputable def diagonalProjectionIso :
    L((pullback.diagonal f)^*[ModuleCat.{u + 1} Λ]) ⋙ R(pullback.diagonal f)_![ModuleCat.{u + 1} Λ] ≅
      (derivedTensor (ModuleCat.{u + 1} Λ) (pullback f f)).obj
        ((R(pullback.diagonal f)_![ModuleCat.{u + 1} Λ]).obj (𝟙_ _)) :=
  Functor.isoWhiskerLeft L((pullback.diagonal f)^*[ModuleCat.{u + 1} Λ])
      ((Functor.leftUnitor R(pullback.diagonal f)_![ModuleCat.{u + 1} Λ]).symm ≪≫
        Functor.isoWhiskerRight (derivedTensorLeftUnitorNatIso (ModuleCat.{u + 1} Λ) X).symm
          R(pullback.diagonal f)_![ModuleCat.{u + 1} Λ]) ≪≫
    (projectionIso (pullback.diagonal f) (𝟙_ _)).symm

/-- The isomorphism `RΔ_! A ≅ RΔ_! Λ_X ⊗ᴸ Lp₁^* A`: the projection formula for `Δ`, the left
unitor and `L(Δ ≫ p₁)^* = L(𝟙)^* ≅ 𝟭`. -/
noncomputable def diagonalIso :
    R(pullback.diagonal f)_![ModuleCat.{u + 1} Λ] ≅
      L((pullback.fst f f)^*[ModuleCat.{u + 1} Λ]) ⋙
        (derivedTensor (ModuleCat.{u + 1} Λ) (pullback f f)).obj
          ((R(pullback.diagonal f)_![ModuleCat.{u + 1} Λ]).obj (𝟙_ _)) :=
  (Functor.leftUnitor _).symm ≪≫
    Functor.isoWhiskerRight (leftDerivedUpperStarIdIso Λ X).symm _ ≪≫
    Functor.isoWhiskerRight (leftDerivedUpperStarComp _ (pullback.diagonal f) (pullback.fst f f)
      (𝟙 X) (pullback.diagonal_fst f).symm) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft L((pullback.fst f f)^*[ModuleCat.{u + 1} Λ]) (diagonalProjectionIso f)

/-- The isomorphism `𝟭 ≅ R(𝟙)_! = R(Δ ≫ p₂)_! ≅ RΔ_! ⋙ Rp₂_!`. -/
noncomputable def idIsoDiagonalSnd :
    𝟭 (DerivedCategoryModule Λ X) ≅
      R(pullback.diagonal f)_![ModuleCat.{u + 1} Λ] ⋙ R(pullback.snd f f)_![ModuleCat.{u + 1} Λ] :=
  (rightDerivedLowerShriekIdIso (ModuleCat.{u + 1} Λ) X).symm ≪≫
    rightDerivedLowerShriekCongrIso Λ (pullback.diagonal_snd f).symm ≪≫
    rightDerivedLowerShriekCompIso Λ (pullback.diagonal f) (pullback.snd f f)

/-- Proper base change `Rf_! ⋙ Lf^* ≅ Lp₁^* ⋙ Rp₂_!` for the cartesian square of `W = X ×_Y X`. -/
noncomputable def baseChangeIso :
    R(f)_![ModuleCat.{u + 1} Λ] ⋙ L((f)^*[ModuleCat.{u + 1} Λ]) ≅
      L((pullback.fst f f)^*[ModuleCat.{u + 1} Λ]) ⋙ R(pullback.snd f f)_![ModuleCat.{u + 1} Λ] :=
  haveI := isIso_rightDerivedLowerShriekBaseChangeMap Λ (IsPullback.of_hasPullback f f)
  asIso (rightDerivedLowerShriekBaseChangeMap Λ (IsPullback.of_hasPullback f f))

/-- The isomorphism `Rp₂_!(Lp₁^* A ⊗ᴸ Lp₂^* L) ≅ Rp₂_!(Lp₁^* A) ⊗ᴸ L ≅ Lf^* Rf_! A ⊗ᴸ L`: the
projection formula for `p₂` and proper base change. -/
noncomputable def sndProjectionIso (L : DerivedCategoryModule Λ X) :
    (L((pullback.fst f f)^*[ModuleCat.{u + 1} Λ]) ⋙
        derivedTensorRight _ (pullback f f) ((L((pullback.snd f f)^*[ModuleCat.{u + 1} Λ])).obj L))
          ⋙ R(pullback.snd f f)_![ModuleCat.{u + 1} Λ] ≅
      R(f)_![ModuleCat.{u + 1} Λ] ⋙ (L((f)^*[ModuleCat.{u + 1} Λ]) ⋙
        derivedTensorRight (ModuleCat.{u + 1} Λ) X L) :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft L((pullback.fst f f)^*[ModuleCat.{u + 1} Λ])
      (projectionRightIso (pullback.snd f f) L).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (baseChangeIso f).symm (derivedTensorRight (ModuleCat.{u + 1} Λ) X L) ≪≫
    Functor.associator _ _ _

/-- Blueprint `def-pur-td-datum`: Trace–diagonal datum

The *unit* `η_A : A ≅ Rp₂_!(RΔ_! Λ_X ⊗ᴸ Lp₁^* A) ⟶ Rp₂_!(Lp₂^* L ⊗ᴸ Lp₁^* A) ≅ G_L(Rf_! A)`:
the first isomorphism is `R(Δ ≫ p₂)_! = R(𝟙)_! ≅ 𝟭` with the projection formula for `Δ`
(`AlgebraicGeometry.Etale.TraceDiagonalDatum.diagonalIso`), the middle map is `cl_Δ ⊗ 𝟙`, and
the last isomorphism is the symmetry, the projection formula for `p₂` and proper base change
`Lf^* Rf_! ≅ Rp₂_! Lp₁^*`. -/
noncomputable def unit : 𝟭 _ ⟶ R(f)_![ModuleCat.{u + 1} Λ] ⋙ d.functor :=
  (idIsoDiagonalSnd f).hom ≫
    Functor.whiskerRight (diagonalIso f).hom R(pullback.snd f f)_![ModuleCat.{u + 1} Λ] ≫
    Functor.whiskerRight (Functor.whiskerLeft L((pullback.fst f f)^*[ModuleCat.{u + 1} Λ])
      ((derivedTensor (ModuleCat.{u + 1} Λ) (pullback f f)).map d.diagonalClass ≫
        ((derivedTensorFlipIso Λ (pullback f f)).app _).hom))
      R(pullback.snd f f)_![ModuleCat.{u + 1} Λ] ≫
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
        have := NatTrans.congr_app hl A
        simpa [leftTriangle] using this
      right_triangle := by
        ext K
        have := NatTrans.congr_app hr K
        simpa [rightTriangle] using this }

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
  NatTrans.congr_app (Adjunction.rightAdjointUniq_hom_counit _ _) K

/-- Blueprint `thm-pur-td-criterion`: Trace–diagonal criterion

The isomorphism `Rf^! ≅ G_L` compatible with the counits is unique. -/
theorem rightDerivedUpperShriekIso_unique (e : R(f)^![ModuleCat.{u + 1} Λ] ≅ d.functor)
    (he : ∀ K, (R(f)_![ModuleCat.{u + 1} Λ]).map (e.hom.app K) ≫ d.counit.app K =
      (rightDerivedUpperShriekAdjunction _ f).counit.app K) :
    e = d.rightDerivedUpperShriekIso hl hr := by
  ext K
  apply ((d.adjunction hl hr).homEquiv _ _).symm.injective
  rw [Adjunction.homEquiv_counit, Adjunction.homEquiv_counit]
  change _ ≫ d.counit.app K = _ ≫ d.counit.app K
  rw [he, rightDerivedUpperShriekIso_hom_counit]

/-- Blueprint `thm-pur-td-criterion`: Trace–diagonal criterion

If the two triangular composites are the identity, the dualizing complex of `f` is `L`:
`ω_f = Rf^! Λ_Y ≅ Lf^* Λ_Y ⊗ᴸ L ≅ Λ_X ⊗ᴸ L ≅ L`. -/
noncomputable def dualizingComplexIso :
    (R(f)^![ModuleCat.{u + 1} Λ]).obj (𝟙_ _) ≅ L :=
  (d.rightDerivedUpperShriekIso hl hr).app _ ≪≫
    (derivedTensorRight (ModuleCat.{u + 1} Λ) X L).mapIso (leftDerivedUpperStarUnitIso _ f) ≪≫
    derivedTensorLeftUnitor (ModuleCat.{u + 1} Λ) X L

end TraceDiagonalDatum

end Etale

end AlgebraicGeometry
