/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.MateTransportCompatible
public import WeilConjectures.SixFunctors.Etale.Derived.CoefficientChangeLowerStarDualizable
public import WeilConjectures.SixFunctors.Etale.Derived.ExtendScalarsHom
public import WeilConjectures.SixFunctors.Etale.Derived.ExtendScalarsLowerStar
public import WeilConjectures.SixFunctors.Etale.Derived.ExtendScalarsRestrictScalarsMate
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekTensorRightMate

/-!
# Derived extension of scalars along a dualizable algebra commutes with `Rf^!`

Let `S` be an `R`-algebra such that the constant complex `S_Y` of `R`-modules is dualizable in
`D(Y_ét, R)`, write `Ψ = - ⊗ᴸ_R S` for derived extension of scalars of étale sheaves, and let
`f : X ⟶ Y` be a morphism with a compactification such that `Rf_!` has right adjoints `Rf^!` over
`R` and over `S`. Then `Ψ` commutes with `Rf_!`
(`AlgebraicGeometry.Etale.rightDerivedLowerShriekExtendScalarsIso`) and the base change map
`Ψ (Rf^! L) ⟶ Rf^! (Ψ L)`, the mate of this commutation, is an isomorphism
(`AlgebraicGeometry.Etale.isIso_rightDerivedUpperShriekExtendScalarsMap_app`).

## Proof

Restricted back to `R`, `Ψ` is the tensor product with `S` (through
`AlgebraicGeometry.Etale.leftDerivedSheafExtendScalarsProjection`), and the base change map is
identified (`CategoryTheory.Adjunction.isIso_mateEquiv_app_of_isIso_mateEquiv_app`) with the
mate `Rf^! L ⊗ᴸ S_X ⟶ Rf^!(L ⊗ᴸ S_Y)` of the inverse of the projection map of `Rf_!` at `S_Y`,
an isomorphism at a dualizable object
(`AlgebraicGeometry.Etale.isIso_mateEquiv_app_inv_rightDerivedLowerShriekDerivedTensorRightMap`).
The identification requires the commutation of `Ψ` with `Rf_! = Rg_* ∘ i_!` to be compatible with
the projection map (`CategoryTheory.Adjunction.TransportCompatible`). This compatibility is proved
for the derived pullback in
`AlgebraicGeometry.Etale.leftDerivedSheafExtendScalarsProjection_transpose_upperStar`, and passes
to its right adjoint `Rg_*` and to the left adjoint `i_!` of `Li^*` through mates.

## Main results

- `AlgebraicGeometry.Etale.rightDerivedLowerShriekExtendScalarsIso`: `Ψ ⋙ Rf_! ≅ Rf_! ⋙ Ψ`.
- `AlgebraicGeometry.Etale.rightDerivedUpperShriekExtendScalarsMap`: the base change map
  `Ψ (Rf^! L) ⟶ Rf^! (Ψ L)`.
- `AlgebraicGeometry.Etale.isIso_rightDerivedUpperShriekExtendScalarsMap_app`: it is an
  isomorphism.
- `AlgebraicGeometry.Etale.arrowIsoRightDerivedUpperShriekCounit`,
  `AlgebraicGeometry.Etale.arrowIsoRightDerivedUpperShriekUnit`: `Ψ` of the counit and of the unit
  of `Rf_! ⊣ Rf^!` are, as arrows, the counit and the unit over `S`.
- `AlgebraicGeometry.Etale.isIso_rightDerivedUpperShriekExtendScalarsMapOfRingHom_app` and
  its siblings: the same for a ring homomorphism `φ : Λ →+* Λ'` with `Λ'_Y` dualizable.
- `isIso_rightDerivedUpperShriekExtendScalarsMapOfRingHom_app_quotient_span_pow`,
  `nonempty_iso_rightDerivedUpperShriek_extendScalars_quotient_span_pow`:
  reduction modulo a power of a nonzerodivisor commutes with `Rf^!`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

-- Use the monoidal structure of the derived tensor product of étale sheaves, see
-- `WeilConjectures.SixFunctors.Etale.Derived.ExtendScalarsDerived`.
attribute [local instance high] SymmetricCategory.toBraidedCategory
attribute [local instance 20000] AlgebraicGeometry.Etale.sheafBraidedCategory
-- Write the ring structure of the coefficient rings (for instance `Λ ⧸ (ϖ)ⁿ`) as the one underlying
-- their commutative ring structure, as in `WeilConjectures.SixFunctors.CoefficientReduction`.
attribute [local instance 2000] CommRing.toRing

namespace AlgebraicGeometry.Etale

open Scheme

variable (R S : Type (u + 1)) [CommRing R] [CommRing S] [Algebra R S]

set_option hygiene false in
/-- Derived extension of scalars on `X`. -/
local notation "Ψ[" X "]" => L(sheafExtendScalars (algebraMap R S) X)

set_option hygiene false in
/-- The adjunction between derived extension and restriction of scalars on `X`. -/
local notation "𝓐[" X "]" => leftDerivedEtaleSheafExtendScalarsAdjunction (algebraMap R S) X

set_option hygiene false in
/-- The complex `S_X` of `R`-modules. -/
local notation "𝓝[" X "]" => derivedSingle (sheafRestrictScalarsUnit R S X)

section Projection

variable (X : Scheme.{u})

/-- The identification `K ⊗ᴸ S_X ⟶ Res (Ψ K)` of derived extension of scalars restricted back to
`R` with the derived tensor product with `S_X`
(`AlgebraicGeometry.Etale.leftDerivedSheafExtendScalarsProjection`). -/
noncomputable def derivedTensorRightExtendScalarsProjection :
    derivedTensorRight (ModuleCat.{u + 1} R) X 𝓝[X] ⟶
      Ψ[X] ⋙ Sheaf.derivedRestrictScalars X.smallEtaleTopology (algebraMap R S) :=
  (leftDerivedTensorRightIso (sheafRestrictScalarsUnit R S X)).inv ≫
    leftDerivedSheafExtendScalarsProjection R S X

instance : IsIso (derivedTensorRightExtendScalarsProjection R S X) := by
  dsimp only [derivedTensorRightExtendScalarsProjection]
  infer_instance

end Projection

section UpperStar

variable {Y Z : Scheme.{u}} (g : Z ⟶ Y)

/-- The identification `Lg^* S_Y ≅ S_Z`. -/
noncomputable abbrev leftDerivedUpperStarDerivedSingleRestrictScalarsUnitIso :
    L((g)^*[ModuleCat.{u + 1} R]).obj 𝓝[Y] ≅ 𝓝[Z] :=
  asIso (leftDerivedUpperStarDerivedSingleMap g (upperStarSheafRestrictScalarsUnitMap R S g))

/-- **Transport compatibility for the derived pullback.** The commutation `Lg^* Ψ ≅ Ψ Lg^*` and
the tensor comparison `Lg^*(K ⊗ᴸ S_Y) ≅ Lg^* K ⊗ᴸ S_Z` are transport compatible. -/
theorem transportCompatible_leftDerivedUpperStar :
    Adjunction.TransportCompatible 𝓐[Y] 𝓐[Z] (derivedTensorRightExtendScalarsProjection R S Y)
      (derivedTensorRightExtendScalarsProjection R S Z) L((g)^*[ModuleCat.{u + 1} R])
      L((g)^*[ModuleCat.{u + 1} S])
      (leftDerivedUpperStarEtaleSheafExtendScalarsIso (algebraMap R S) g).hom
      (leftDerivedUpperStarDerivedTensorRightIso _ g
        (leftDerivedUpperStarDerivedSingleRestrictScalarsUnitIso R S g)).hom := by
  have h₀ : Adjunction.TransportCompatible 𝓐[Y] 𝓐[Z] (leftDerivedSheafExtendScalarsProjection R S Y)
      (leftDerivedSheafExtendScalarsProjection R S Z) L((g)^*[ModuleCat.{u + 1} R])
      L((g)^*[ModuleCat.{u + 1} S])
      (leftDerivedUpperStarEtaleSheafExtendScalarsIso (algebraMap R S) g).hom
      (leftDerivedTensorRestrictScalarsUnitUpperStarMap R S g) :=
    leftDerivedSheafExtendScalarsProjection_transpose_upperStar R S g
  refine h₀.of_hom
    (leftDerivedTensorRightIso (sheafRestrictScalarsUnit R S Y)).inv
    (leftDerivedTensorRightIso (sheafRestrictScalarsUnit R S Z)).inv fun K ↦
      leftDerivedUpperStarDerivedTensorRightIso_hom_app_comp_leftDerivedTensorRightIso_inv _ g _ K

/-- **Transport compatibility for the derived direct image.** If they are invertible, the inverse
of the base change map `Ψ (Rg_* M) ⟶ Rg_* (Ψ M)` and the inverse of the comparison
`Rg_* M ⊗ᴸ S_Y ⟶ Rg_*(M ⊗ᴸ S_Z)` are transport compatible. -/
theorem transportCompatible_rightDerivedLowerStar
    [IsIso (rightDerivedLowerStarExtendScalarsMap (algebraMap R S) g)]
    [IsIso (rightDerivedLowerStarDerivedTensorRightMap _ g
      (leftDerivedUpperStarDerivedSingleRestrictScalarsUnitIso R S g).hom)] :
    Adjunction.TransportCompatible 𝓐[Z] 𝓐[Y] (derivedTensorRightExtendScalarsProjection R S Z)
      (derivedTensorRightExtendScalarsProjection R S Y) R((g)_*[ModuleCat.{u + 1} R])
      R((g)_*[ModuleCat.{u + 1} S])
      (inv (rightDerivedLowerStarExtendScalarsMap (algebraMap R S) g))
      (inv (rightDerivedLowerStarDerivedTensorRightMap _ g
        (leftDerivedUpperStarDerivedSingleRestrictScalarsUnitIso R S g).hom)) :=
  (transportCompatible_leftDerivedUpperStar R S g).rightAdjoint_of_eq
    (derivedUpperStarLowerStarAdjunction _ g) (derivedUpperStarLowerStarAdjunction _ g)
    (β := rightDerivedLowerStarExtendScalarsMap (algebraMap R S) g) rfl
    (mateEquiv_leftDerivedUpperStarDerivedTensorRightIso_hom _ g _)

end UpperStar

section OpenImmersion

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- The commutation `Ψ ⋙ D(j_!) ≅ D(j_!) ⋙ Ψ` of derived extension of scalars with the extension
by zero along an open immersion, as a natural transformation: the left adjoint mate of the
commutation `Lj^* Ψ ≅ Ψ Lj^*`. -/
noncomputable def openImmersionLowerShriekExtendScalarsMap :
    Ψ[U] ⋙ D((j)_!open[ModuleCat.{u + 1} S]) ⟶ D((j)_!open[ModuleCat.{u + 1} R]) ⋙ Ψ[X] :=
  (mateEquiv (openImmersionLowerShriekLeftDerivedUpperStarAdjunction _ j)
    (openImmersionLowerShriekLeftDerivedUpperStarAdjunction _ j)).symm
    (leftDerivedUpperStarEtaleSheafExtendScalarsIso (algebraMap R S) j).inv

instance : IsIso (openImmersionLowerShriekExtendScalarsMap R S j) := by
  have : IsIso (mateEquiv 𝓐[X] 𝓐[U]
      (leftDerivedUpperStarEtaleSheafExtendScalarsIso (algebraMap R S) j).inv) := by
    rw [mateEquiv_leftDerivedUpperStarEtaleSheafExtendScalarsIso_inv]
    infer_instance
  exact Adjunction.isIso_mateEquiv_symm_of_isIso_mateEquiv _ _ 𝓐[U] 𝓐[X] _

/-- **Transport compatibility for the extension by zero.** The commutation of `Ψ` with `D(j_!)`
and the left adjoint mate of the comparison `Lj^*(K ⊗ᴸ S_X) ≅ Lj^* K ⊗ᴸ S_U` are transport
compatible. -/
theorem transportCompatible_openImmersionLowerShriek :
    Adjunction.TransportCompatible 𝓐[U] 𝓐[X] (derivedTensorRightExtendScalarsProjection R S U)
      (derivedTensorRightExtendScalarsProjection R S X) D((j)_!open[ModuleCat.{u + 1} R])
      D((j)_!open[ModuleCat.{u + 1} S]) (openImmersionLowerShriekExtendScalarsMap R S j)
      ((mateEquiv (openImmersionLowerShriekLeftDerivedUpperStarAdjunction _ j)
        (openImmersionLowerShriekLeftDerivedUpperStarAdjunction _ j)).symm
        (leftDerivedUpperStarDerivedTensorRightIso _ j
          (leftDerivedUpperStarDerivedSingleRestrictScalarsUnitIso R S j)).inv) :=
  (transportCompatible_leftDerivedUpperStar R S j).leftAdjoint_iso _ _

end OpenImmersion

section LowerShriek

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]

/-- The identification `Lf^* S_Y ≅ S_X`, through the chosen compactification of `f`. -/
noncomputable abbrev leftDerivedUpperStarRestrictScalarsUnitIso :
    L((f)^*[ModuleCat.{u + 1} R]).obj 𝓝[Y] ≅ 𝓝[X] :=
  compactificationUpperStarIso _ (HasCompactification.compactification f)
    (leftDerivedUpperStarDerivedSingleRestrictScalarsUnitIso R S _)
    (leftDerivedUpperStarDerivedSingleRestrictScalarsUnitIso R S _)

/-- The **base change map** `Ψ (Rf_! K) ⟶ Rf_!(Ψ K)` of derived extension of scalars along the
compact-support direct image: for the chosen compactification `(i, g)` of `f`, the base change
map `Ψ (Rg_* M) ⟶ Rg_*(Ψ M)` (`AlgebraicGeometry.Etale.rightDerivedLowerStarExtendScalarsMap`)
followed by `Rg_*` of the commutation of `Ψ` with `D(i_!)`. -/
noncomputable def rightDerivedLowerShriekExtendScalarsMap :
    R(f)_![ModuleCat.{u + 1} R] ⋙ Ψ[Y] ⟶ Ψ[X] ⋙ R(f)_![ModuleCat.{u + 1} S] :=
  (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft D(((HasCompactification.compactification f).i)_!open[ModuleCat.{u + 1} R])
      (rightDerivedLowerStarExtendScalarsMap (algebraMap R S)
        (HasCompactification.compactification f).g) ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight
      (inv (openImmersionLowerShriekExtendScalarsMap R S
        (HasCompactification.compactification f).i))
      R(((HasCompactification.compactification f).g)_*[ModuleCat.{u + 1} S]) ≫
    (Functor.associator _ _ _).hom

lemma rightDerivedLowerShriekExtendScalarsMap_app
    (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R))) :
    (rightDerivedLowerShriekExtendScalarsMap R S f).app K =
      (rightDerivedLowerStarExtendScalarsMap (algebraMap R S)
        (HasCompactification.compactification f).g).app
        (D(((HasCompactification.compactification f).i)_!open[ModuleCat.{u + 1} R]).obj K) ≫
      R(((HasCompactification.compactification f).g)_*[ModuleCat.{u + 1} S]).map
        (inv ((openImmersionLowerShriekExtendScalarsMap R S
          (HasCompactification.compactification f).i).app K)) := by
  simp only [rightDerivedLowerShriekExtendScalarsMap, NatTrans.comp_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    NatIso.isIso_inv_app, Category.comp_id, Category.id_comp]
  exact Category.id_comp _

variable {R S} in
/-- If `S_Y` is dualizable, derived extension of scalars commutes with `Rg_*` for every `g` with
target `Y`. -/
lemma isIso_rightDerivedLowerStarExtendScalarsMap_of_isDualizable' {Z : Scheme.{u}} (g : Z ⟶ Y)
    (hS : IsDualizable 𝓝[Y]) :
    IsIso (rightDerivedLowerStarExtendScalarsMap (algebraMap R S) g) :=
  @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ fun M ↦
    isIso_mateEquiv_leftDerivedUpperStarEtaleSheafExtendScalarsIso_app_of_isDualizable R S g
      (hS.of_iso (derivedSingleSheafRestrictScalarsUnitIso R S Y)) M

/-- If `S_Y` is dualizable, the base change map `Ψ (Rf_! K) ⟶ Rf_!(Ψ K)` is an isomorphism. -/
lemma isIso_rightDerivedLowerShriekExtendScalarsMap (hS : IsDualizable 𝓝[Y]) :
    IsIso (rightDerivedLowerShriekExtendScalarsMap R S f) := by
  have := isIso_rightDerivedLowerStarExtendScalarsMap_of_isDualizable'
    (HasCompactification.compactification f).g hS
  rw [rightDerivedLowerShriekExtendScalarsMap]
  infer_instance

/-- **Derived extension of scalars commutes with `Rf_!`**: for `S_Y` dualizable, the inverse
`Ψ ⋙ Rf_! ≅ Rf_! ⋙ Ψ` of the base change map
`AlgebraicGeometry.Etale.rightDerivedLowerShriekExtendScalarsMap`. -/
noncomputable def rightDerivedLowerShriekExtendScalarsIso (hS : IsDualizable 𝓝[Y]) :
    Ψ[X] ⋙ R(f)_![ModuleCat.{u + 1} S] ≅ R(f)_![ModuleCat.{u + 1} R] ⋙ Ψ[Y] :=
  have := isIso_rightDerivedLowerShriekExtendScalarsMap R S f hS
  (asIso (rightDerivedLowerShriekExtendScalarsMap R S f)).symm

/-- The **base change map** `Ψ (Rf^! L) ⟶ Rf^!(Ψ L)` of derived extension of scalars along the
exceptional inverse image: the mate of the commutation
`AlgebraicGeometry.Etale.rightDerivedLowerShriekExtendScalarsIso` of `Ψ` with `Rf_!` along the
adjunctions `Rf_! ⊣ Rf^!`. -/
noncomputable def rightDerivedUpperShriekExtendScalarsMap (hS : IsDualizable 𝓝[Y])
    [(R(f)_![ModuleCat.{u + 1} R]).IsLeftAdjoint] [(R(f)_![ModuleCat.{u + 1} S]).IsLeftAdjoint] :
    (R(f)_![ModuleCat.{u + 1} R]).rightAdjoint ⋙ Ψ[X] ⟶
      Ψ[Y] ⋙ (R(f)_![ModuleCat.{u + 1} S]).rightAdjoint :=
  mateEquiv (Adjunction.ofIsLeftAdjoint (R(f)_![ModuleCat.{u + 1} R]))
    (Adjunction.ofIsLeftAdjoint (R(f)_![ModuleCat.{u + 1} S]))
    (rightDerivedLowerShriekExtendScalarsIso R S f hS).hom

/-- **Derived extension of scalars along a dualizable algebra commutes with `Rf^!`.** If the
constant complex `S_Y` of `R`-modules is dualizable, the base change map
`Ψ (Rf^! L) ⟶ Rf^!(Ψ L)` is an isomorphism for every `L`. -/
theorem isIso_rightDerivedUpperShriekExtendScalarsMap_app (hS : IsDualizable 𝓝[Y])
    [(R(f)_![ModuleCat.{u + 1} R]).IsLeftAdjoint] [(R(f)_![ModuleCat.{u + 1} S]).IsLeftAdjoint]
    (L : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R))) :
    IsIso ((rightDerivedUpperShriekExtendScalarsMap R S f hS).app L) := by
  let c := HasCompactification.compactification f
  have := isIso_rightDerivedLowerShriekExtendScalarsMap R S f hS
  have := isIso_rightDerivedLowerStarExtendScalarsMap_of_isDualizable' c.g hS
  have := isIso_rightDerivedLowerStarDerivedTensorRightMap_of_isDualizable _ c.g
    (leftDerivedUpperStarDerivedSingleRestrictScalarsUnitIso R S c.g) hS
  have := isIso_rightDerivedLowerShriekDerivedTensorRightMap_of_isDualizable _ c
    (leftDerivedUpperStarRestrictScalarsUnitIso R S f) hS
  have hcomp : Adjunction.TransportCompatible 𝓐[X] 𝓐[Y]
      (derivedTensorRightExtendScalarsProjection R S X)
      (derivedTensorRightExtendScalarsProjection R S Y) R(f)_![ModuleCat.{u + 1} R]
      R(f)_![ModuleCat.{u + 1} S] (rightDerivedLowerShriekExtendScalarsIso R S f hS).hom
      (inv (rightDerivedLowerShriekDerivedTensorRightMap _ c
        (leftDerivedUpperStarRestrictScalarsUnitIso R S f).hom)) := by
    refine (transportCompatible_openImmersionLowerShriek R S c.i).comp
      (transportCompatible_rightDerivedLowerStar R S c.g) (fun K ↦ ?_) (fun K ↦ ?_)
    · simp only [rightDerivedLowerShriekExtendScalarsIso, Iso.symm_hom, asIso_inv,
        NatIso.isIso_inv_app]
      apply IsIso.inv_eq_of_hom_inv_id
      rw [rightDerivedLowerShriekExtendScalarsMap_app]
      simp
      rfl
    · rw [NatIso.isIso_inv_app, NatIso.isIso_inv_app]
      apply IsIso.inv_eq_of_hom_inv_id
      rw [← Category.assoc, rightDerivedLowerShriekDerivedTensorRightMap_app_comp_map]
      exact IsIso.hom_inv_id _
  have := isIso_mateEquiv_app_inv_rightDerivedLowerShriekDerivedTensorRightMap _ c
    (Adjunction.ofIsLeftAdjoint (R(f)_![ModuleCat.{u + 1} R]))
    (leftDerivedUpperStarRestrictScalarsUnitIso R S f) hS L
  exact Adjunction.isIso_mateEquiv_app_of_isIso_mateEquiv_app _ _ 𝓐[X] 𝓐[Y] _
    (derivedTensorRightExtendScalarsProjection R S X)
    (derivedTensorRightExtendScalarsProjection R S Y) _
    (fun K ↦ Adjunction.map_comp_mateEquiv_app_comp_map_of_transpose _ _ _ _ _ _ K (hcomp K)) L

/-- The derived extension of scalars of the counit `Rf_! Rf^! L ⟶ L` of `Rf_! ⊣ Rf^!` is, as an
arrow, the counit at `Ψ L` over `S`, if `S_Y` is dualizable. -/
noncomputable def arrowIsoRightDerivedUpperShriekCounit (hS : IsDualizable 𝓝[Y])
    [(R(f)_![ModuleCat.{u + 1} R]).IsLeftAdjoint] [(R(f)_![ModuleCat.{u + 1} S]).IsLeftAdjoint]
    (L : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R))) :
    Arrow.mk (Ψ[Y].map ((Adjunction.ofIsLeftAdjoint (R(f)_![ModuleCat.{u + 1} R])).counit.app L)) ≅
      Arrow.mk ((Adjunction.ofIsLeftAdjoint (R(f)_![ModuleCat.{u + 1} S])).counit.app
        (Ψ[Y].obj L)) :=
  have := isIso_rightDerivedUpperShriekExtendScalarsMap_app R S f hS L
  Arrow.isoMk
    ((rightDerivedLowerShriekExtendScalarsIso R S f hS).symm.app _ ≪≫
      (R(f)_![ModuleCat.{u + 1} S]).mapIso
        (asIso ((rightDerivedUpperShriekExtendScalarsMap R S f hS).app L)))
    (Iso.refl _) (by
      have h := mateEquiv_counit (Adjunction.ofIsLeftAdjoint (R(f)_![ModuleCat.{u + 1} R]))
        (Adjunction.ofIsLeftAdjoint (R(f)_![ModuleCat.{u + 1} S]))
        (rightDerivedLowerShriekExtendScalarsIso R S f hS).hom L
      dsimp at h ⊢
      rw [Category.comp_id, Category.assoc, rightDerivedUpperShriekExtendScalarsMap, h,
        Iso.inv_hom_id_app_assoc])

/-- The derived extension of scalars of the unit `K ⟶ Rf^! Rf_! K` of `Rf_! ⊣ Rf^!` is, as an
arrow, the unit at `Ψ K` over `S`, if `S_Y` is dualizable. -/
noncomputable def arrowIsoRightDerivedUpperShriekUnit (hS : IsDualizable 𝓝[Y])
    [(R(f)_![ModuleCat.{u + 1} R]).IsLeftAdjoint] [(R(f)_![ModuleCat.{u + 1} S]).IsLeftAdjoint]
    (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R))) :
    Arrow.mk (Ψ[X].map ((Adjunction.ofIsLeftAdjoint (R(f)_![ModuleCat.{u + 1} R])).unit.app K)) ≅
      Arrow.mk ((Adjunction.ofIsLeftAdjoint (R(f)_![ModuleCat.{u + 1} S])).unit.app
        (Ψ[X].obj K)) :=
  have := isIso_rightDerivedUpperShriekExtendScalarsMap_app R S f hS
    ((R(f)_![ModuleCat.{u + 1} R]).obj K)
  Arrow.isoMk (Iso.refl _)
    (asIso ((rightDerivedUpperShriekExtendScalarsMap R S f hS).app _) ≪≫
      (R(f)_![ModuleCat.{u + 1} S]).rightAdjoint.mapIso
        ((rightDerivedLowerShriekExtendScalarsIso R S f hS).symm.app K)) (by
      have h := unit_mateEquiv (Adjunction.ofIsLeftAdjoint (R(f)_![ModuleCat.{u + 1} R]))
        (Adjunction.ofIsLeftAdjoint (R(f)_![ModuleCat.{u + 1} S]))
        (rightDerivedLowerShriekExtendScalarsIso R S f hS).hom K
      dsimp at h ⊢
      rw [Category.id_comp, rightDerivedUpperShriekExtendScalarsMap, reassoc_of% h]
      simp [← Functor.map_comp])

end LowerShriek

section RingHom

variable {Λ Λ' : Type (u + 1)} [CommRing Λ] [CommRing Λ'] (φ : Λ →+* Λ') {X Y : Scheme.{u}}
  (f : X ⟶ Y) [HasCompactification f]

/-- **Derived extension of scalars along `φ : Λ →+* Λ'` commutes with `Rf_!`**, if the constant
complex `Λ'_Y` of `Λ`-modules is dualizable: the isomorphism
`AlgebraicGeometry.Etale.rightDerivedLowerShriekExtendScalarsIso` for the `Λ`-algebra structure
of `Λ'` given by `φ`. -/
noncomputable def rightDerivedLowerShriekExtendScalarsIsoOfRingHom
    (hΛ' : IsDualizable (constantSingle (ModuleCat.{u + 1} Λ) Y
      ((ModuleCat.restrictScalars.{u + 1} φ).obj (𝟙_ (ModuleCat.{u + 1} Λ'))))) :
    L(sheafExtendScalars φ X) ⋙ R(f)_![ModuleCat.{u + 1} Λ'] ≅
      R(f)_![ModuleCat.{u + 1} Λ] ⋙ L(sheafExtendScalars φ Y) :=
  letI := φ.toAlgebra
  rightDerivedLowerShriekExtendScalarsIso Λ Λ' f
    (hΛ'.of_iso (derivedSingleSheafRestrictScalarsUnitIso Λ Λ' Y).symm)

/-- The **base change map** `Ψ (Rf^! L) ⟶ Rf^!(Ψ L)` of derived extension of scalars along
`φ : Λ →+* Λ'`: the mate of
`AlgebraicGeometry.Etale.rightDerivedLowerShriekExtendScalarsIsoOfRingHom` along the adjunctions
`Rf_! ⊣ Rf^!`. -/
noncomputable def rightDerivedUpperShriekExtendScalarsMapOfRingHom
    (hΛ' : IsDualizable (constantSingle (ModuleCat.{u + 1} Λ) Y
      ((ModuleCat.restrictScalars.{u + 1} φ).obj (𝟙_ (ModuleCat.{u + 1} Λ')))))
    [(R(f)_![ModuleCat.{u + 1} Λ]).IsLeftAdjoint] [(R(f)_![ModuleCat.{u + 1} Λ']).IsLeftAdjoint] :
    (R(f)_![ModuleCat.{u + 1} Λ]).rightAdjoint ⋙ L(sheafExtendScalars φ X) ⟶
      L(sheafExtendScalars φ Y) ⋙ (R(f)_![ModuleCat.{u + 1} Λ']).rightAdjoint :=
  mateEquiv (Adjunction.ofIsLeftAdjoint (R(f)_![ModuleCat.{u + 1} Λ]))
    (Adjunction.ofIsLeftAdjoint (R(f)_![ModuleCat.{u + 1} Λ']))
    (rightDerivedLowerShriekExtendScalarsIsoOfRingHom φ f hΛ').hom

/-- **Derived extension of scalars along `φ : Λ →+* Λ'` commutes with `Rf^!`**, if the constant
complex `Λ'_Y` of `Λ`-modules is dualizable. -/
theorem isIso_rightDerivedUpperShriekExtendScalarsMapOfRingHom_app
    (hΛ' : IsDualizable (constantSingle (ModuleCat.{u + 1} Λ) Y
      ((ModuleCat.restrictScalars.{u + 1} φ).obj (𝟙_ (ModuleCat.{u + 1} Λ')))))
    [(R(f)_![ModuleCat.{u + 1} Λ]).IsLeftAdjoint] [(R(f)_![ModuleCat.{u + 1} Λ']).IsLeftAdjoint]
    (L : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    IsIso ((rightDerivedUpperShriekExtendScalarsMapOfRingHom φ f hΛ').app L) :=
  letI := φ.toAlgebra
  isIso_rightDerivedUpperShriekExtendScalarsMap_app Λ Λ' f _ L

/-- The derived extension of scalars along `φ` of the counit `Rf_! Rf^! L ⟶ L` is, as an arrow,
the counit at `Ψ L` over `Λ'`, if `Λ'_Y` is dualizable. -/
noncomputable def arrowIsoRightDerivedUpperShriekCounitOfRingHom
    (hΛ' : IsDualizable (constantSingle (ModuleCat.{u + 1} Λ) Y
      ((ModuleCat.restrictScalars.{u + 1} φ).obj (𝟙_ (ModuleCat.{u + 1} Λ')))))
    [(R(f)_![ModuleCat.{u + 1} Λ]).IsLeftAdjoint] [(R(f)_![ModuleCat.{u + 1} Λ']).IsLeftAdjoint]
    (L : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    Arrow.mk (L(sheafExtendScalars φ Y).map
        ((Adjunction.ofIsLeftAdjoint (R(f)_![ModuleCat.{u + 1} Λ])).counit.app L)) ≅
      Arrow.mk ((Adjunction.ofIsLeftAdjoint (R(f)_![ModuleCat.{u + 1} Λ'])).counit.app
        (L(sheafExtendScalars φ Y).obj L)) :=
  letI := φ.toAlgebra
  arrowIsoRightDerivedUpperShriekCounit Λ Λ' f
    (hΛ'.of_iso (derivedSingleSheafRestrictScalarsUnitIso Λ Λ' Y).symm) L

/-- The derived extension of scalars along `φ` of the unit `K ⟶ Rf^! Rf_! K` is, as an arrow,
the unit at `Ψ K` over `Λ'`, if `Λ'_Y` is dualizable. -/
noncomputable def arrowIsoRightDerivedUpperShriekUnitOfRingHom
    (hΛ' : IsDualizable (constantSingle (ModuleCat.{u + 1} Λ) Y
      ((ModuleCat.restrictScalars.{u + 1} φ).obj (𝟙_ (ModuleCat.{u + 1} Λ')))))
    [(R(f)_![ModuleCat.{u + 1} Λ]).IsLeftAdjoint] [(R(f)_![ModuleCat.{u + 1} Λ']).IsLeftAdjoint]
    (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    Arrow.mk (L(sheafExtendScalars φ X).map
        ((Adjunction.ofIsLeftAdjoint (R(f)_![ModuleCat.{u + 1} Λ])).unit.app K)) ≅
      Arrow.mk ((Adjunction.ofIsLeftAdjoint (R(f)_![ModuleCat.{u + 1} Λ'])).unit.app
        (L(sheafExtendScalars φ X).obj K)) :=
  letI := φ.toAlgebra
  arrowIsoRightDerivedUpperShriekUnit Λ Λ' f
    (hΛ'.of_iso (derivedSingleSheafRestrictScalarsUnitIso Λ Λ' Y).symm) K

end RingHom

section Quotient

variable {Λ : Type (u + 1)} [CommRing Λ] {ϖ : Λ} {X Y : Scheme.{u}}

/-- **Reduction modulo a power of a nonzerodivisor commutes with `Rf^!`**: for a nonzerodivisor
`ϖ` of `Λ` and `n : ℕ`, the base change map `Rf^! L ⊗ᴸ_Λ Λ/ϖⁿ ⟶ Rf^!(L ⊗ᴸ_Λ Λ/ϖⁿ)` is an
isomorphism for every `L`. -/
theorem isIso_rightDerivedUpperShriekExtendScalarsMapOfRingHom_app_quotient_span_pow
    (hϖ : ϖ ∈ nonZeroDivisors Λ) (n : ℕ) (f : X ⟶ Y) [HasCompactification f]
    [(R(f)_![ModuleCat.{u + 1} Λ]).IsLeftAdjoint]
    [(R(f)_![ModuleCat.{u + 1} (Λ ⧸ Ideal.span {ϖ} ^ n)]).IsLeftAdjoint]
    (L : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    IsIso ((rightDerivedUpperShriekExtendScalarsMapOfRingHom
      (Ideal.Quotient.mk (Ideal.span {ϖ} ^ n)) f
      (isDualizable_constantSingle_restrictScalars_quotient_span_pow Y hϖ n)).app L) :=
  isIso_rightDerivedUpperShriekExtendScalarsMapOfRingHom_app _ f _ L

/-- Reduction modulo a power of a nonzerodivisor commutes with `Rf^!`, as an isomorphism
`Rf^! L ⊗ᴸ_Λ Λ/ϖⁿ ≅ Rf^!(L ⊗ᴸ_Λ Λ/ϖⁿ)`. -/
theorem nonempty_iso_rightDerivedUpperShriek_extendScalars_quotient_span_pow
    (hϖ : ϖ ∈ nonZeroDivisors Λ) (n : ℕ) (f : X ⟶ Y) [HasCompactification f]
    [(R(f)_![ModuleCat.{u + 1} Λ]).IsLeftAdjoint]
    [(R(f)_![ModuleCat.{u + 1} (Λ ⧸ Ideal.span {ϖ} ^ n)]).IsLeftAdjoint]
    (L : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    Nonempty ((L(sheafExtendScalars (Ideal.Quotient.mk (Ideal.span {ϖ} ^ n)) X)).obj
        ((R(f)_![ModuleCat.{u + 1} Λ]).rightAdjoint.obj L) ≅
      (R(f)_![ModuleCat.{u + 1} (Λ ⧸ Ideal.span {ϖ} ^ n)]).rightAdjoint.obj
        ((L(sheafExtendScalars (Ideal.Quotient.mk (Ideal.span {ϖ} ^ n)) Y)).obj L)) :=
  have := isIso_rightDerivedUpperShriekExtendScalarsMapOfRingHom_app_quotient_span_pow hϖ n f L
  ⟨asIso ((rightDerivedUpperShriekExtendScalarsMapOfRingHom
    (Ideal.Quotient.mk (Ideal.span {ϖ} ^ n)) f
    (isDualizable_constantSingle_restrictScalars_quotient_span_pow Y hϖ n)).app L)⟩

end Quotient

end AlgebraicGeometry.Etale
