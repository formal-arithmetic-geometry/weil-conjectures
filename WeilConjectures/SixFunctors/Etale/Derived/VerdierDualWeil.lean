/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.WeilEquivariance
public import WeilConjectures.SixFunctors.Etale.Derived.Dualizing
public import WeilConjectures.SixFunctors.Etale.Derived.Exchange
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarId
public import WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius

/-!
# Weil equivariance of duality and of the exceptional adjunction

Let `g : X ≅ X` be an automorphism of a scheme (in the `ℓ`-adic formalism, the geometric
Frobenius of `X = X₀ ×_{k₀} k̄`), lying over `h : S ⟶ S` along `a : X ⟶ S` (cartesian square
`g ≫ a = a ≫ h`). This file transports Weil data through the exceptional inverse image and the
Verdier dual, and proves that the structure maps are equivariant
(blueprint `cor-coef-verdier-weil-equivariance`).

* The *exceptional base change* `Lg'^* Rf^! ⟶ Rf'^! Lg^*` of a cartesian square is the mate of
  the inverse of the compact-support base change isomorphism `Ex_! : Lg^* Rf_! ≅ Rf'_! Lg'^*`
  (`AlgebraicGeometry.Etale.upperShriekBaseChangeMap`). It transports a Weil datum on `K` to one
  on `Rf^! K` (`AlgebraicGeometry.Etale.upperShriekMateWeilDatum`), and the unit and counit of
  `Rf_! ⊣ Rf^!` are equivariant.
* The *dualizing Weil datum* on `ω_X = Ra^! Λ_S` is the transport of the canonical datum on
  `Λ_S` (`AlgebraicGeometry.Etale.dualizingComplexWeilDatum`).
* The *dual Weil datum* on `𝔻_X K = RHom(K, ω_X)` of a strict Weil datum `φ : Lg^* K ≅ K` is
  ```
  Lg^* 𝔻 K ≅ RHom(Lg^* K, Lg^* ω) ──RHom(φ⁻¹, φ_ω)──▶ 𝔻 K
  ```
  (`AlgebraicGeometry.Etale.verdierDualWeilDatum`), the first map being the internal-hom
  comparison of the monoidal autoequivalence `Lg^*`. Evaluation `K ⊗ᴸ 𝔻 K ⟶ ω` is equivariant,
  and so is the adjoint `M ⟶ 𝔻 K` of any equivariant pairing `K ⊗ᴸ M ⟶ ω`.

## Main definitions

- `AlgebraicGeometry.Etale.leftDerivedUpperStarEquivalence`: `Lg^*` for an automorphism `g`.
- `AlgebraicGeometry.Etale.upperShriekBaseChangeMap`: the exceptional base change.
- `AlgebraicGeometry.Etale.upperShriekMateWeilDatum`,
  `AlgebraicGeometry.Etale.dualizingComplexWeilDatum`,
  `AlgebraicGeometry.Etale.verdierDualWeilDatum` (`cor-coef-verdier-weil-equivariance`).

## Main statements

- `AlgebraicGeometry.Etale.isWeilMorphism_counit_upperShriekMateWeilDatum`,
  `AlgebraicGeometry.Etale.isWeilMorphism_unit_upperShriekMateWeilDatum`,
  `AlgebraicGeometry.Etale.isWeilEquivariant_verdierDual_evaluation`,
  `AlgebraicGeometry.Etale.isWeilEquivariant_verdierDual_curry`
  (`cor-coef-verdier-weil-equivariance`).

## Implementation notes

The statements hold for any finite coefficient ring `Λ` on the small étale site; they only use
the compact-support base change isomorphism, the adjunction `Rf_! ⊣ Rf^!`, the monoidality of
`Lg^*` and the closed structure, and no integral lattice of the Weil structure. The biduality
`K ⟶ 𝔻 𝔻 K` is the adjoint of the evaluation composed with the symmetry, so its equivariance
additionally needs the compatibility of the monoidal structure of `Lg^*` with the symmetry, which
is not formalised.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Opposite

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ]

section Equivalence

variable {X : Scheme.{u}} (g : X ≅ X)

/-- The derived pullback `Lg^*` along an automorphism `g` is an autoequivalence of `D(X_ét, Λ)`,
with inverse `L(g⁻¹)^*`. -/
noncomputable def leftDerivedUpperStarEquivalence :
    DerivedCategoryModule Λ X ≌ DerivedCategoryModule Λ X :=
  CategoryTheory.Equivalence.mk L((g.hom)^*[ModuleCat.{u + 1} Λ]) L((g.inv)^*[ModuleCat.{u + 1} Λ])
    ((leftDerivedUpperStarId _ X).symm ≪≫ leftDerivedUpperStarComp _ g.inv g.hom (𝟙 X) (by simp))
    ((leftDerivedUpperStarComp _ g.hom g.inv (𝟙 X) (by simp)).symm ≪≫ leftDerivedUpperStarId _ X)

instance isEquivalence_leftDerivedUpperStar :
    (L((g.hom)^*[ModuleCat.{u + 1} Λ])).IsEquivalence :=
  inferInstanceAs (leftDerivedUpperStarEquivalence Λ g).functor.IsEquivalence

end Equivalence

section Exchange

variable [Finite Λ] {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y}
  {g : Y' ⟶ Y} [HasCompactification f] [HasCompactification f'] [QuasiCompact f']

/-- The *exceptional base change* `Lg'^* Rf^! ⟶ Rf'^! Lg^*` of a cartesian square
```
  X' --g'--> X
  |          |
  f'         f
  v          v
  Y' --g---> Y
```
the mate, along `Rf_! ⊣ Rf^!` and `Rf'_! ⊣ Rf'^!`, of the inverse of the compact-support base
change isomorphism `Ex_! : Lg^* Rf_! ≅ Rf'_! Lg'^*`
(`AlgebraicGeometry.Etale.isIso_rightDerivedLowerShriekBaseChangeMap`). -/
noncomputable def upperShriekBaseChangeMap (sq : IsPullback g' f' f g) :
    R(f)^![ModuleCat.{u + 1} Λ] ⋙ L((g')^*[ModuleCat.{u + 1} Λ]) ⟶
      L((g)^*[ModuleCat.{u + 1} Λ]) ⋙ R(f')^![ModuleCat.{u + 1} Λ] :=
  have := isIso_rightDerivedLowerShriekBaseChangeMap Λ sq
  Adjunction.rightAdjointExchange (rightDerivedUpperShriekAdjunction _ f)
    (rightDerivedUpperShriekAdjunction _ f') (asIso (rightDerivedLowerShriekBaseChangeMap Λ sq))

end Exchange

section Weil

variable [Finite Λ] {X Y : Scheme.{u}} {f : X ⟶ Y} [HasCompactification f] [QuasiCompact f]
  {gX : X ⟶ X} {gY : Y ⟶ Y}

variable {Λ} in
/-- Blueprint `cor-coef-verdier-weil-equivariance`: the Weil datum on `Rf^! K` transported from a
datum `φ : Lg_Y^* K ⟶ K` through the exceptional base change of the cartesian square
`g_X ≫ f = f ≫ g_Y`,
```
Lg_X^* Rf^! K ──exceptional base change──▶ Rf^! Lg_Y^* K ──Rf^! φ──▶ Rf^! K.
```
-/
noncomputable def upperShriekMateWeilDatum (sq : IsPullback gX f f gY)
    {K : DerivedCategoryModule Λ Y} (φ : (L((gY)^*[ModuleCat.{u + 1} Λ])).obj K ⟶ K) :
    (L((gX)^*[ModuleCat.{u + 1} Λ])).obj ((R(f)^![ModuleCat.{u + 1} Λ]).obj K) ⟶
      (R(f)^![ModuleCat.{u + 1} Λ]).obj K :=
  (upperShriekBaseChangeMap Λ sq).app K ≫ (R(f)^![ModuleCat.{u + 1} Λ]).map φ

/-- Blueprint `cor-coef-verdier-weil-equivariance`: **the exceptional counit is Weil
equivariant**. For a Weil datum `φ` on `K`, the counit `Rf_! Rf^! K ⟶ K` is a morphism of Weil
objects from the compact-support transport of the exceptional datum on `Rf^! K`
(`AlgebraicGeometry.Etale.upperShriekMateWeilDatum`) to `φ`. -/
theorem isWeilMorphism_counit_upperShriekMateWeilDatum (sq : IsPullback gX f f gY)
    {K : DerivedCategoryModule Λ Y} (φ : (L((gY)^*[ModuleCat.{u + 1} Λ])).obj K ⟶ K) :
    IsWeilMorphism gY (lowerShriekWeilDatum sq (upperShriekMateWeilDatum sq φ)) φ
      ((rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} Λ) f).counit.app K) :=
  have := isIso_rightDerivedLowerShriekBaseChangeMap Λ sq
  Adjunction.isWeilEquivariant_counit (rightDerivedUpperShriekAdjunction _ f)
    (asIso (rightDerivedLowerShriekBaseChangeMap Λ sq)) φ

/-- Blueprint `cor-coef-verdier-weil-equivariance`: **the exceptional unit is Weil
equivariant**. For a Weil datum `φ` on `M`, the unit `M ⟶ Rf^! Rf_! M` is a morphism of Weil
objects from `φ` to the exceptional datum of the compact-support transport of `φ`. -/
theorem isWeilMorphism_unit_upperShriekMateWeilDatum (sq : IsPullback gX f f gY)
    {M : DerivedCategoryModule Λ X} (φ : (L((gX)^*[ModuleCat.{u + 1} Λ])).obj M ⟶ M) :
    IsWeilMorphism gX φ (upperShriekMateWeilDatum sq (lowerShriekWeilDatum sq φ))
      ((rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} Λ) f).unit.app M) :=
  have := isIso_rightDerivedLowerShriekBaseChangeMap Λ sq
  Adjunction.isWeilEquivariant_unit (rightDerivedUpperShriekAdjunction _ f)
    (asIso (rightDerivedLowerShriekBaseChangeMap Λ sq)) φ

end Weil

section Duality

variable [Finite Λ] {X S : Scheme.{u}} {a : X ⟶ S} [HasCompactification a] [QuasiCompact a]
  {h : S ⟶ S}

variable {Λ} in
/-- Blueprint `cor-coef-verdier-weil-equivariance`: the *dualizing Weil datum*
`Lg^* ω_X ⟶ ω_X` on the dualizing complex `ω_X = Ra^! Λ_S`, the exceptional transport
(`AlgebraicGeometry.Etale.upperShriekMateWeilDatum`) of the canonical datum
`Lh^* Λ_S ≅ Λ_S`. -/
noncomputable def dualizingComplexWeilDatum {g : X ⟶ X} (sq : IsPullback g a a h) :
    (L((g)^*[ModuleCat.{u + 1} Λ])).obj (dualizingComplex (ModuleCat.{u + 1} Λ) a) ⟶
      dualizingComplex (ModuleCat.{u + 1} Λ) a :=
  upperShriekMateWeilDatum sq (leftDerivedUpperStarUnitIso _ h).hom

variable (g : X ≅ X)

attribute [local instance] leftDerivedUpperStarMonoidal

variable {Λ} in
/-- Blueprint `cor-coef-verdier-weil-equivariance`: the *dual Weil datum* on the Verdier dual
`𝔻_X K = RHom(K, ω_X)` of a strict Weil datum `φ : Lg^* K ≅ K`,
```
Lg^* 𝔻 K ≅ RHom(Lg^* K, Lg^* ω) ──RHom(Lg^* K, φ_ω)──▶ RHom(Lg^* K, ω) ──RHom(φ⁻¹, ω)──▶ 𝔻 K,
```
the first map being the internal-hom comparison for the monoidal autoequivalence `Lg^*` and
`φ_ω` the dualizing Weil datum (`AlgebraicGeometry.Etale.dualizingComplexWeilDatum`). Only `φ`
and its inverse enter; no integral lattice is used. -/
noncomputable def verdierDualWeilDatum (sq : IsPullback g.hom a a h)
    {K : DerivedCategoryModule Λ X} (φ : (L((g.hom)^*[ModuleCat.{u + 1} Λ])).obj K ≅ K) :
    (L((g.hom)^*[ModuleCat.{u + 1} Λ])).obj
        ((verdierDual (ModuleCat.{u + 1} Λ) a).obj (op K)) ⟶
      (verdierDual (ModuleCat.{u + 1} Λ) a).obj (op K) :=
  MonoidalClosed.dualWeilDatum L((g.hom)^*[ModuleCat.{u + 1} Λ]) φ (dualizingComplexWeilDatum sq)

/-- Blueprint `cor-coef-verdier-weil-equivariance`: **evaluation is Weil equivariant**. For a
strict Weil datum `φ` on `K`, the evaluation `K ⊗ᴸ 𝔻_X K ⟶ ω_X` is equivariant for the tensor
product of `φ` with the dual datum (`AlgebraicGeometry.Etale.verdierDualWeilDatum`) and the
dualizing datum. -/
theorem isWeilEquivariant_verdierDual_evaluation (sq : IsPullback g.hom a a h)
    {K : DerivedCategoryModule Λ X} (φ : (L((g.hom)^*[ModuleCat.{u + 1} Λ])).obj K ≅ K) :
    IsWeilEquivariant L((g.hom)^*[ModuleCat.{u + 1} Λ])
      (MonoidalClosed.tensorWeilDatum _ φ.hom (verdierDualWeilDatum g sq φ))
      (dualizingComplexWeilDatum sq)
      ((ihom.ev K).app (dualizingComplex (ModuleCat.{u + 1} Λ) a)) :=
  MonoidalClosed.isWeilEquivariant_ev _ φ _

/-- Blueprint `cor-coef-verdier-weil-equivariance`: **the transpose of an equivariant pairing is
equivariant**. For a strict Weil datum `φ` on `K`, a Weil datum `ψ` on `M` and a pairing
`b : K ⊗ᴸ M ⟶ ω_X` equivariant for `φ ⊗ ψ` and the dualizing datum, the tensor–hom transpose
`M ⟶ 𝔻_X K` is a morphism of Weil objects to the dual datum. -/
theorem isWeilEquivariant_verdierDual_curry (sq : IsPullback g.hom a a h)
    {K M : DerivedCategoryModule Λ X} (φ : (L((g.hom)^*[ModuleCat.{u + 1} Λ])).obj K ≅ K)
    (ψ : (L((g.hom)^*[ModuleCat.{u + 1} Λ])).obj M ⟶ M)
    {b : K ⊗ M ⟶ dualizingComplex (ModuleCat.{u + 1} Λ) a}
    (hb : IsWeilEquivariant L((g.hom)^*[ModuleCat.{u + 1} Λ])
      (MonoidalClosed.tensorWeilDatum _ φ.hom ψ) (dualizingComplexWeilDatum sq) b) :
    IsWeilEquivariant L((g.hom)^*[ModuleCat.{u + 1} Λ]) ψ (verdierDualWeilDatum g sq φ)
      (MonoidalClosed.curry b) :=
  MonoidalClosed.isWeilEquivariant_curry _ φ ψ _ hb

end Duality

end Etale

end AlgebraicGeometry
