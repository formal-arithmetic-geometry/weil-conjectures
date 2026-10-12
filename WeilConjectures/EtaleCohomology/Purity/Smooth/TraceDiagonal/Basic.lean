/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
public import WeilConjectures.SixFunctors.Etale.Derived.Exchange
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekToLowerStar
public import WeilConjectures.SixFunctors.Etale.Derived.TensorStructure
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarIdCoherence

/-!
# Isomorphisms for the trace–diagonal criterion

Isomorphisms of functors on the unbounded derived categories `D(X_ét, Λ)` of étale sheaves of
`Λ`-modules, `Λ` a finite ring, which build the unit and counit of a trace–diagonal datum
(`WeilConjectures.EtaleCohomology.Purity.Smooth.TraceDiagonal`): the projection formula
`Rf_! L ⊗ᴸ K ≅ Rf_!(L ⊗ᴸ Lf^* K)` as an isomorphism of functors, the composition isomorphism
`R(f ≫ g)_! ≅ Rf_! ⋙ Rg_!` as data, `R(𝟙)_! ≅ 𝟭`, and, for a separated `f : X ⟶ Y` with
`W = X ×_Y X`, the isomorphisms `RΔ_! ≅ RΔ_! Λ_X ⊗ᴸ Lp₁^*(-)`, `𝟭 ≅ RΔ_! ⋙ Rp₂_!` and proper
base change `Rf_! ⋙ Lf^* ≅ Lp₁^* ⋙ Rp₂_!`.

## Implementation notes

The unit `Λ_X` is written `AlgebraicGeometry.Etale.derivedTensorUnit`, defined over a general
coefficient category: for `A = ModuleCat Λ`, the monoidal instance on `D(X_ét)` found by
instance search is a different term from the one inside `derivedTensor` and its unitors, and
the kernel does not compare the two in reasonable time (see
`WeilConjectures.SixFunctors.Etale.Derived.TensorStructure`).
-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

section General

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] (X : Scheme.{u})

/-- The unit `Λ_X = 𝟙_` of the derived tensor product on `D(X_ét)`. It is stated over a general
coefficient category `A`, so that its specialisation to `A = ModuleCat Λ` is the unit appearing
in `AlgebraicGeometry.Etale.derivedTensorLeftUnitorNatIso` and
`AlgebraicGeometry.Etale.leftDerivedUpperStarUnitIso`. -/
noncomputable def derivedTensorUnit : DerivedCategory (Sheaf X.smallEtaleTopology A) :=
  𝟙_ _

/-- The left unitor `Λ_X ⊗ᴸ - ≅ 𝟭`, with the unit written `derivedTensorUnit`. -/
noncomputable def derivedTensorUnitLeftUnitor :
    (derivedTensor A X).obj (derivedTensorUnit A X) ≅
      𝟭 (DerivedCategory (Sheaf X.smallEtaleTopology A)) :=
  derivedTensorLeftUnitorNatIso A X

/-- A chosen symmetry `K ⊗ᴸ M ≅ M ⊗ᴸ K` of the derived tensor product on `D(X_ét)`
(`AlgebraicGeometry.Etale.nonempty_iso_derivedTensor_flip`). -/
noncomputable def derivedTensorFlipIso :
    derivedTensor A X ≅ (derivedTensor A X).flip :=
  (nonempty_iso_derivedTensor_flip A X).some

/-- The derived lower shriek along the identity is the identity, `R(𝟙_X)_! ≅ R(𝟙_X)_* ≅ 𝟭`: the
identity is proper (`AlgebraicGeometry.Etale.rightDerivedLowerShriekIsoRightDerivedLowerStar`)
and `(𝟙_X)_* ≅ 𝟭`. This is the isomorphism `AlgebraicGeometry.Etale.rightDerivedLowerShriekIdIso`
of `WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality`, rebuilt here to avoid the large
import closure of that file. -/
noncomputable def rightDerivedLowerShriekIdIsoOfLowerStar :
    R(𝟙 X)_![A] ≅ 𝟭 _ :=
  rightDerivedLowerShriekIsoRightDerivedLowerStar A (𝟙 X) ≪≫
    Functor.rightDerivedFunctorNatIso (lowerStarId A X) ≪≫
    (𝟭 _).rightDerivedFunctorIsoMapDerivedCategory ≪≫ Functor.mapDerivedCategoryIdIso _

variable {A X} in
/-- The derived pullback preserves the unit, `Lg^* Λ_Y ≅ Λ_Z`, with the unit written
`derivedTensorUnit`. -/
noncomputable def leftDerivedUpperStarDerivedTensorUnitIso {Z Y : Scheme.{u}} (g : Z ⟶ Y)
    [(g)^*[A].PreservesFlat] :
    (L((g)^*[A])).obj (derivedTensorUnit A Y) ≅ derivedTensorUnit A Z :=
  leftDerivedUpperStarUnitIso A g

end General

variable (Λ : Type (u + 1)) [CommRing Λ]

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

/-- The projection formula `Rf_! L ⊗ᴸ K ≅ Rf_!(L ⊗ᴸ Lf^* K)`, as an isomorphism of functors of
`K`, for torsion coefficients. -/
noncomputable def projectionIso {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]
    (L : DerivedCategoryModule Λ X) :
    (derivedTensor (ModuleCat.{u + 1} Λ) Y).obj ((R(f)_![ModuleCat.{u + 1} Λ]).obj L) ≅
      (L((f)^*[ModuleCat.{u + 1} Λ])) ⋙ (derivedTensor (ModuleCat.{u + 1} Λ) X).obj L ⋙
        (R(f)_![ModuleCat.{u + 1} Λ]) :=
  haveI := isIso_projectionMap_of_finite Λ f
  asIso ((projectionMap (ModuleCat.{u + 1} Λ) f).app L)

/-- The projection formula `Rf_! K ⊗ᴸ M ≅ Rf_!(K ⊗ᴸ Lf^* M)`, as an isomorphism of functors of
`K`, for torsion coefficients. -/
noncomputable def projectionRightIso {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]
    (M : DerivedCategoryModule Λ Y) :
    (R(f)_![ModuleCat.{u + 1} Λ]) ⋙ derivedTensorRight (ModuleCat.{u + 1} Λ) Y M ≅
      derivedTensorRight (ModuleCat.{u + 1} Λ) X ((L((f)^*[ModuleCat.{u + 1} Λ])).obj M) ⋙
        (R(f)_![ModuleCat.{u + 1} Λ]) :=
  haveI := isIso_projectionMap_of_finite Λ f
  asIso (((flipFunctor _ _ _).map (projectionMap (ModuleCat.{u + 1} Λ) f)).app M)

/-- The projection formula for the unit: `Lf^* ⋙ Rf_! ≅ Rf_! Λ_X ⊗ᴸ -`, the left unitor
followed by the inverse of the projection formula
`AlgebraicGeometry.Etale.projectionIso`. -/
noncomputable def projectionUnitIso {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f] :
    (L((f)^*[ModuleCat.{u + 1} Λ])) ⋙ (R(f)_![ModuleCat.{u + 1} Λ]) ≅
      (derivedTensor (ModuleCat.{u + 1} Λ) Y).obj
        ((R(f)_![ModuleCat.{u + 1} Λ]).obj (derivedTensorUnit _ X)) :=
  Functor.isoWhiskerLeft (L((f)^*[ModuleCat.{u + 1} Λ]))
      (Functor.isoWhiskerRight (derivedTensorUnitLeftUnitor (ModuleCat.{u + 1} Λ) X).symm
        (R(f)_![ModuleCat.{u + 1} Λ])) ≪≫
    (projectionIso Λ f (derivedTensorUnit _ X)).symm

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f] [QuasiCompact f]
  [IsSeparated f]

/-- `Δ ≫ p₂ = 𝟙` admits a compactification. -/
instance hasCompactification_diagonal_snd :
    HasCompactification (pullback.diagonal f ≫ pullback.snd f f) := by
  rw [pullback.diagonal_snd]
  infer_instance

/-- `Δ ≫ p₂ = 𝟙` is quasi-compact. -/
instance quasiCompact_diagonal_snd : QuasiCompact (pullback.diagonal f ≫ pullback.snd f f) := by
  rw [pullback.diagonal_snd]
  infer_instance
namespace TraceDiagonalDatum

variable {Λ}

/-- The isomorphism `𝟭 ≅ Lp₁^* ⋙ LΔ^*`, from `Δ ≫ p₁ = 𝟙`. -/
noncomputable def diagonalSectionIso :
    𝟭 (DerivedCategoryModule Λ X) ≅
      (L((pullback.fst f f)^*[ModuleCat.{u + 1} Λ])) ⋙
        (L((pullback.diagonal f)^*[ModuleCat.{u + 1} Λ])) :=
  (leftDerivedUpperStarCompSectionIso _ (pullback.diagonal f) (pullback.fst f f)
    (pullback.diagonal_fst f)).symm

/-- The isomorphism `RΔ_! ≅ Lp₁^* ⋙ LΔ^* ⋙ RΔ_!`, from `Δ ≫ p₁ = 𝟙`. -/
noncomputable def diagonalLowerShriekSectionIso :
    R(pullback.diagonal f)_![ModuleCat.{u + 1} Λ] ≅
      (L((pullback.fst f f)^*[ModuleCat.{u + 1} Λ])) ⋙
        (L((pullback.diagonal f)^*[ModuleCat.{u + 1} Λ])) ⋙
          (R(pullback.diagonal f)_![ModuleCat.{u + 1} Λ]) :=
  (Functor.leftUnitor (R(pullback.diagonal f)_![ModuleCat.{u + 1} Λ])).symm ≪≫
    Functor.isoWhiskerRight (diagonalSectionIso f)
      (R(pullback.diagonal f)_![ModuleCat.{u + 1} Λ]) ≪≫
    Functor.associator (L((pullback.fst f f)^*[ModuleCat.{u + 1} Λ]))
      (L((pullback.diagonal f)^*[ModuleCat.{u + 1} Λ]))
      (R(pullback.diagonal f)_![ModuleCat.{u + 1} Λ])

/-- The isomorphism `RΔ_! A ≅ RΔ_! Λ_X ⊗ᴸ Lp₁^* A`: `L(Δ ≫ p₁)^* = L(𝟙)^* ≅ 𝟭` and the
projection formula for `Δ` (`AlgebraicGeometry.Etale.projectionUnitIso`). -/
noncomputable def diagonalIso :
    R(pullback.diagonal f)_![ModuleCat.{u + 1} Λ] ≅
      (L((pullback.fst f f)^*[ModuleCat.{u + 1} Λ])) ⋙
        (derivedTensor (ModuleCat.{u + 1} Λ) (pullback f f)).obj
          ((R(pullback.diagonal f)_![ModuleCat.{u + 1} Λ]).obj (derivedTensorUnit _ X)) :=
  diagonalLowerShriekSectionIso f ≪≫
    Functor.isoWhiskerLeft (L((pullback.fst f f)^*[ModuleCat.{u + 1} Λ]))
      (projectionUnitIso Λ (pullback.diagonal f))

/-- The isomorphism `𝟭 ≅ R(𝟙)_! = R(Δ ≫ p₂)_! ≅ RΔ_! ⋙ Rp₂_!`. -/
noncomputable def idIsoDiagonalSnd :
    𝟭 (DerivedCategoryModule Λ X) ≅
      (R(pullback.diagonal f)_![ModuleCat.{u + 1} Λ]) ⋙
        (R(pullback.snd f f)_![ModuleCat.{u + 1} Λ]) :=
  (rightDerivedLowerShriekIdIsoOfLowerStar (ModuleCat.{u + 1} Λ) X).symm ≪≫
    rightDerivedLowerShriekCongrIso Λ (pullback.diagonal_snd f).symm ≪≫
    rightDerivedLowerShriekCompIso Λ (pullback.diagonal f) (pullback.snd f f)

/-- Proper base change `Rf_! ⋙ Lf^* ≅ Lp₁^* ⋙ Rp₂_!` for the cartesian square of
`W = X ×_Y X`. -/
noncomputable def baseChangeIso :
    (R(f)_![ModuleCat.{u + 1} Λ]) ⋙ (L((f)^*[ModuleCat.{u + 1} Λ])) ≅
      (L((pullback.fst f f)^*[ModuleCat.{u + 1} Λ])) ⋙
        (R(pullback.snd f f)_![ModuleCat.{u + 1} Λ]) :=
  haveI := isIso_rightDerivedLowerShriekBaseChangeMap Λ (IsPullback.of_hasPullback f f)
  asIso (rightDerivedLowerShriekBaseChangeMap Λ (IsPullback.of_hasPullback f f))

/-- The isomorphism `Rp₂_!(Lp₁^* A ⊗ᴸ Lp₂^* L) ≅ Rp₂_!(Lp₁^* A) ⊗ᴸ L ≅ Lf^* Rf_! A ⊗ᴸ L`: the
projection formula for `p₂` and proper base change. -/
noncomputable def sndProjectionIso (L : DerivedCategoryModule Λ X) :
    ((L((pullback.fst f f)^*[ModuleCat.{u + 1} Λ])) ⋙
        derivedTensorRight _ (pullback f f) ((L((pullback.snd f f)^*[ModuleCat.{u + 1} Λ])).obj L))
          ⋙ (R(pullback.snd f f)_![ModuleCat.{u + 1} Λ]) ≅
      (R(f)_![ModuleCat.{u + 1} Λ]) ⋙ ((L((f)^*[ModuleCat.{u + 1} Λ])) ⋙
        derivedTensorRight (ModuleCat.{u + 1} Λ) X L) :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (L((pullback.fst f f)^*[ModuleCat.{u + 1} Λ]))
      (projectionRightIso Λ (pullback.snd f f) L).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (baseChangeIso f).symm
      (derivedTensorRight (ModuleCat.{u + 1} Λ) X L) ≪≫
    Functor.associator _ _ _
end TraceDiagonalDatum

end Etale

end AlgebraicGeometry
