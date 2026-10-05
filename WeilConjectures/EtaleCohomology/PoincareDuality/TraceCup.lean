/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Regular
public import WeilConjectures.EtaleCohomology.PoincareDuality.Degreewise
public import WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion
public import WeilConjectures.Mathlib.LinearAlgebra.BilinearMap

/-!
# The trace map and the trace–cup pairing

The *trace* of a Tate orientation `γ : Λ_X(d)[2d] ≅ Ra^! Λ_Y` is the map

`tr_X : H^{2d}_c(X, Λ) ⟶ Λ(-d)`,

the untwisted form of the counit of `Ra_! ⊣ Ra^!` read through `γ`. For proper `X` the
compactly supported and the ordinary cohomology agree, and the derived Poincaré pairing for
`K = Λ_X` takes the classical shape of a *trace–cup pairing*

`⟨x, y⟩_i = tr_X(x ⌣ y) : H^i(X, Λ) × H^{2d-i}(X, Λ) ⟶ Λ(-d)`.

Classes follow `CategoryTheory.cohomologyClasses`: `H^i(X, M)` is the module of classes
`Λ_Y ⟶ (Ra_* M)[i]`, `H^i_c(X, M)` that of classes `Λ_Y ⟶ (Ra_! M)[i]`, and a class of `Λ(-d)`
is a morphism `Λ_Y ⟶ Λ_Y(-d)`. The cup product is taken on `X`, on the adjoint classes
`Λ_X ⟶ Λ_X[i]` (`AlgebraicGeometry.Etale.lowerStarClassEquiv`).

## Main definitions

- `AlgebraicGeometry.Etale.traceMapTensorTateObject`: a class `c ∈ H^{2d}_c(X, Λ)` sent to
  `Λ_Y(d) ⟶ Λ_Y`.
- `AlgebraicGeometry.Etale.traceMap`: the trace `tr_X : H^{2d}_c(X, Λ) ⟶ Λ(-d)`.
- `AlgebraicGeometry.Etale.twistedTraceMap`: its twist `tr_X(d) : H^{2d}_c(X, Λ(d)) ⟶ Λ`.
- `AlgebraicGeometry.Etale.tateDualUnitClass`: the unit class in `H^0(X, Λ(d)^∨(d))`.
- `AlgebraicGeometry.Etale.traceCupPairing`: the trace–cup pairing `⟨-,-⟩_i`, for proper `X`.
- `AlgebraicGeometry.Etale.rationalPointClass`: the class in `H^{2d}(X, Λ(d))` of a `k`-point.

## Main statements

- `AlgebraicGeometry.Etale.bijective_traceMap` (`sk-cor-trace`): the trace isomorphism.
- `AlgebraicGeometry.Etale.twistedTraceMap_eq_degreewisePoincarePairing`: the twisted trace is
  the degreewise pairing at `i = 2d` against the unit class, for `K = Λ_X(d)`.
- `AlgebraicGeometry.Etale.traceCupPairing_eq_untwistedDegreewisePoincarePairing`: the
  trace–cup pairing is the line-valued degreewise pairing for `K = Λ_X`, and
  `AlgebraicGeometry.Etale.bijective_traceCupPairing`: it is perfect over a field.
- `AlgebraicGeometry.Etale.isUnit_twistedTraceMap_rationalPointClass`: the twisted trace of the
  class of a `k`-point is a unit.

## Implementation notes

The statements are for `ModuleCat Λ` with a finite coefficient ring `Λ`, the stage `A_{E,n}`
of the blueprint. The orientation `γ` is arbitrary: the repository does not yet define the
blueprint's normalized orientation, for which the twisted trace of the class of a point is `1`.
What holds for every `γ` is that this value is a unit, which is what is stated here.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Opposite

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

section Trace

variable (Λ : Type (u + 1)) [CommRing Λ] [HasTateTwist Λ] {X Y : Scheme.{u}} (a : X ⟶ Y)
  [HasCompactification a] {d : ℕ}

/-- The trace of a class `c ∈ H^{2d}_c(X, Λ)`, as a morphism `Λ_Y(d) ⟶ Λ_Y`:
```
          λ⁻¹                    c ⊗ᴸ 1                                  ≅
Λ_Y(d) ─────▶ Λ_Y ⊗ᴸ Λ_Y(d) ─────────▶ (Ra_! Λ_X)[2d] ⊗ᴸ Λ_Y(d) ─────▶ (Ra_! Λ_X ⊗ᴸ Λ_Y(d))[2d]
       projection map                             ≅
     ─────────────────▶ (Ra_!(Λ_X ⊗ᴸ La^* Λ_Y(d)))[2d] ─────▶ (Ra_! Λ_X(d))[2d]
            ≅                      Tr_γ
     ─────────▶ Ra_!(Λ_X(d)[2d]) ─────────▶ Λ_Y
```
through the projection map of `Ra_!`, `La^* Λ_Y(d) ≅ Λ_X(d)` and the smooth trace of `γ`. It
is `Λ`-linear, being built from composition and the `Λ`-linear functor `- ⊗ᴸ Λ_Y(d)`. -/
noncomputable def traceMapTensorTateObject (γ : TateOrientation Λ a d) :
    cohomologyClasses ((R(a)_![ModuleCat.{u + 1} Λ]).obj (constantComplex Λ X)) (2 * d : ℤ) →ₗ[Λ]
      (tateObject Λ Y d ⟶ 𝟙_ _) :=
  Linear.leftComp Λ _ (derivedTensorLeftUnitor _ Y _).inv ∘ₗ
    Linear.rightComp Λ _
      ((((derivedTensor _ Y).flip.obj (tateObject Λ Y d)).commShiftIso (2 * d : ℤ)).hom.app _ ≫
        (((projectionMap _ a).app (constantComplex Λ X)).app (tateObject Λ Y d) ≫
          (R(a)_![ModuleCat.{u + 1} Λ]).map (((derivedTensor _ X).obj _).map
            (leftDerivedUpperStarTateObjectIso a d).hom ≫
              (derivedTensorLeftUnitor _ X _).hom))⟦(2 * d : ℤ)⟧' ≫
        ((R(a)_![ModuleCat.{u + 1} Λ]).commShiftIso (2 * d : ℤ)).inv.app _ ≫ γ.smoothTrace) ∘ₗ
      ((derivedTensor _ Y).flip.obj (tateObject Λ Y d)).mapLinearMap Λ

/-- Blueprint `sk-def-trace-cup`: Trace and trace–cup pairing.

The *trace* `tr^{(-d)}_X : H^{2d}_c(X, Λ) ⟶ Λ(-d)` of a Tate orientation `γ`: a class
`c : Λ_Y ⟶ (Ra_! Λ_X)[2d]` is sent to `Λ_Y(d) ⟶ Λ_Y`
(`AlgebraicGeometry.Etale.traceMapTensorTateObject`) and untwisted into a class
`Λ_Y ⟶ Λ_Y(-d)` (`AlgebraicGeometry.Etale.untwistTateObject`).

For `X` proper over `Y = Spec k` the source is `H^{2d}(X, Λ)`, and this is the trace of the
blueprint; it is defined for any `a` admitting a compactification. -/
noncomputable def traceMap (γ : TateOrientation Λ a d) :
    cohomologyClasses ((R(a)_![ModuleCat.{u + 1} Λ]).obj (constantComplex Λ X)) (2 * d : ℤ) →ₗ[Λ]
      (𝟙_ _ ⟶ tateObject Λ Y (-d)) :=
  untwistTateObject Λ Y d ∘ₗ traceMapTensorTateObject Λ a γ

/-- Blueprint `sk-cor-trace`: The trace isomorphism.

The *twisted trace* `tr^{(-d)}_X(d) : H^{2d}_c(X, Λ(d)) ⟶ Λ` of a Tate orientation `γ`, for a
connected `Y`: a class `Λ_Y ⟶ (Ra_!(Λ_X(d)))[2d]` composed with the smooth trace of `γ`,
```
          c                               ≅                        Tr_γ
Λ_Y ─────────▶ (Ra_!(Λ_X(d)))[2d] ─────────▶ Ra_!(Λ_X(d)[2d]) ─────────▶ Λ_Y
```
read in `Λ` through `AlgebraicGeometry.Etale.coefficientAlgEquiv`. -/
noncomputable def twistedTraceMap [ConnectedSpace Y] (γ : TateOrientation Λ a d) :
    cohomologyClasses ((R(a)_![ModuleCat.{u + 1} Λ]).obj (tateObject Λ X d)) (2 * d : ℤ) →ₗ[Λ]
      Λ :=
  (coefficientAlgEquiv Λ Y).symm.toLinearMap ∘ₗ
    Linear.rightComp Λ _
      (((R(a)_![ModuleCat.{u + 1} Λ]).commShiftIso (2 * d : ℤ)).inv.app _ ≫ γ.smoothTrace)

variable (X) in
/-- The *unit class* `u ∈ H^0(X, Λ(d)^∨(d))`, the class `Λ_X ⟶ Λ_X(d)^∨ ⊗ᴸ Λ_X(d)`
```
       ≅                         ≅                            φ ⊗ᴸ 1
Λ_X ─────▶ Λ_X(-d + d) ─────▶ Λ_X(-d) ⊗ᴸ Λ_X(d) ─────────▶ Λ_X(d)^∨ ⊗ᴸ Λ_X(d)
```
where `φ : Λ_X(-d) ⟶ Λ_X(d)^∨` is the adjoint of the multiplication
`Λ_X(d) ⊗ᴸ Λ_X(-d) ≅ Λ_X(d + -d) ≅ Λ_X` of the Tate twist datum. -/
noncomputable def tateDualUnitClass (d : ℕ) :
    constantComplex Λ X ⟶ twistedDual Λ d (tateObject Λ X d) :=
  (HasTateTwist.twistObjectZeroIso X).inv ≫ eqToHom (by rw [neg_add_cancel]) ≫
    (HasTateTwist.twistObjectAddIso X (-d) d).inv ≫
      ((derivedTensor _ X).map ((derivedTensorHomAdjunction _ (tateObject Λ X d)).homEquiv _ _
        ((HasTateTwist.twistObjectAddIso X d (-d)).hom ≫ eqToHom (by rw [add_neg_cancel]) ≫
          (HasTateTwist.twistObjectZeroIso X).hom))).app (tateObject Λ X d)

/-- Blueprint `sk-def-trace-cup`: Trace and trace–cup pairing.

The *trace–cup pairing* of a proper `X`,

`⟨x, y⟩_i = tr^{(-d)}_X(x ⌣ y) : H^i(X, Λ) × H^j(X, Λ) ⟶ Λ(-d)`, `i + j = 2d`:
```
                             (H ≅ H(X)) × (H ≅ H(X))                          ⌣
H^i(X, Λ) × H^j(X, Λ) ─────────────────────────────▶ H^i(X) × H^j(X) ─────▶ H^{2d}(X)
      H(X) ≅ H                      H ≅ H_c                       tr_X
    ─────────────▶ H^{2d}(X, Λ) ─────────────▶ H^{2d}_c(X, Λ) ─────────▶ Λ(-d)
```
the classes `x`, `y` (classes `Λ_Y ⟶ (Ra_* Λ_X)[i]`) being read on `X`, as classes
`Λ_X ⟶ Λ_X[i]`, through `AlgebraicGeometry.Etale.lowerStarClassEquiv`, multiplied by
`AlgebraicGeometry.Etale.unitCupProduct`, and the product read back on `Y` and in `H_c` through
`Ra_* ≅ Ra_!`. -/
noncomputable def traceCupPairing [IsProper a] (γ : TateOrientation Λ a d) (i j : ℤ)
    (hij : i + j = 2 * d) :
    cohomologyClasses ((R((a)_*[ModuleCat.{u + 1} Λ])).obj (constantComplex Λ X)) i →ₗ[Λ]
      cohomologyClasses ((R((a)_*[ModuleCat.{u + 1} Λ])).obj (constantComplex Λ X)) j →ₗ[Λ]
        (𝟙_ _ ⟶ tateObject Λ Y (-d)) :=
  let e := leftDerivedUpperStarConstantComplexIso Λ a
  ((unitCupProduct (ModuleCat.{u + 1} Λ) Λ X i j).compl₁₂
      (lowerStarClassEquiv _ Λ a e _ i).symm.toLinearMap
      (lowerStarClassEquiv _ Λ a e _ j).symm.toLinearMap).compr₂
    (traceMap Λ a γ ∘ₗ (lowerStarClassEquivLowerShriek _ Λ a _ _).toLinearMap ∘ₗ
      (lowerStarClassEquiv _ Λ a e _ _).toLinearMap ∘ₗ
        (Linear.homCongr Λ (Iso.refl _) (eqToIso (by rw [hij]; rfl))).toLinearMap)

end Trace

section Statements

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] [HasTateTwist Λ] {X : Scheme.{u}}
  {k : Type u} [Field k] [IsSepClosed k] [HasInvertibleExponent Λ (Spec (.of k))]
  (a : X ⟶ Spec (.of k)) [HasCompactification a] [QuasiCompact a] {d : ℕ}
  (γ : TateOrientation Λ a d)

/-- Blueprint `sk-cor-trace`: The trace isomorphism.

For `X` smooth and connected of pure dimension `d` over a separably closed field `k`, the trace
`tr^{(-d)}_X : H^{2d}_c(X, Λ) ⟶ Λ(-d)` is an isomorphism; no properness is needed.

Over a field `Λ` this is degreewise duality at `i = 2d` for `K = Λ_X(d)`
(`AlgebraicGeometry.Etale.twistedTraceMap_eq_degreewisePoincarePairing`) together with
`H^0(X, Λ) = Λ` for connected `X`. Over a finite ring `Λ` degreewise duality fails in general,
and the statement rests on the vanishing of `H^q_c(X, Λ)` above `q = 2d`. -/
theorem bijective_traceMap [SmoothOfRelativeDimension d a] [ConnectedSpace X] :
    Function.Bijective (traceMap Λ a γ) :=
  sorry

/-- Blueprint `sk-cor-trace`: The trace isomorphism.

**The twisted trace is degreewise duality at `i = 2d`.** For `K = Λ_X(d)`, the degreewise
Poincaré pairing `⟨x, u⟩` of `x ∈ H^{2d}_c(X, Λ(d))` with the unit class
`u ∈ H^0(X, Λ(d)^∨(d))` (`AlgebraicGeometry.Etale.tateDualUnitClass`, read on `Spec k` through
`AlgebraicGeometry.Etale.lowerStarClassEquiv`) is the twisted trace of `x`:
```
                                  x ⊗ᴸ u                                       β_K
Λ ≅ Λ ⊗ᴸ Λ ─────────▶ (Ra_! Λ_X(d))[2d] ⊗ᴸ (Ra_*(Λ_X(d)^∨(d)))[0] ─────────────▶ Λ
 ‖                                                                              ‖
 ‖                 x                                     ≅                    Tr_γ ‖
Λ ─────────▶ (Ra_! Λ_X(d))[2d] ─────────▶ Ra_!(Λ_X(d)[2d]) ─────────────────────▶ Λ
```
The evaluation of `Λ_X(d)` against the unit class is the identity of `Λ_X(d)`, so that the
mixed-support cup product with `u` is the identity of `Ra_! Λ_X(d)`. -/
theorem twistedTraceMap_eq_degreewisePoincarePairing
    (x : cohomologyClasses ((R(a)_![ModuleCat.{u + 1} Λ]).obj (tateObject Λ X d)) (2 * d : ℤ)) :
    twistedTraceMap Λ a γ x =
      degreewisePoincarePairing Λ a γ (tateObject Λ X d) (2 * d) 0 (add_zero _) x
        (lowerStarClassEquiv _ Λ a (leftDerivedUpperStarConstantComplexIso Λ a) _ 0
          ((cohomologyClassesZeroEquiv Λ _ 0 rfl).symm (tateDualUnitClass Λ X d))) :=
  sorry

/-- Blueprint `sk-def-trace-cup`: Trace and trace–cup pairing.

**The trace–cup pairing is the line-valued degreewise pairing for `K = Λ_X`.** For proper `X`,
the trace–cup pairing is `AlgebraicGeometry.Etale.untwistedDegreewisePoincarePairing` for
`K = Λ_X`, read through `H^i(X, Λ) ≅ H^i_c(X, Λ)`
(`AlgebraicGeometry.Etale.lowerStarClassEquivLowerShriek`) and `Λ_X ≅ Λ_X^∨`
(`AlgebraicGeometry.Etale.DerivedCategory.unitIsoCoefficientDualUnit`):
```
                       (H ≅ H_c) × (Λ_X ≅ Λ_X^∨)                                untwisted β
H^i(X, Λ) × H^j(X, Λ) ─────────────────────────▶ H^i_c(X, Λ) × H^j(X, Λ_X^∨) ─────────────▶ Λ(-d)
```
-/
theorem traceCupPairing_eq_untwistedDegreewisePoincarePairing [IsProper a] (i j : ℤ)
    (hij : i + j = 2 * d) :
    traceCupPairing Λ a γ i j hij =
      (untwistedDegreewisePoincarePairing Λ a γ (constantComplex Λ X) i j hij).compl₁₂
        (lowerStarClassEquivLowerShriek _ Λ a _ i).toLinearMap
        (Linear.homCongr Λ (Iso.refl _) ((shiftFunctor _ j).mapIso
          ((R((a)_*[ModuleCat.{u + 1} Λ])).mapIso
            (DerivedCategory.unitIsoCoefficientDualUnit _ X)))).toLinearMap :=
  sorry

/-- Blueprint `sk-def-trace-cup`: Trace and trace–cup pairing.

**The trace–cup pairing is perfect.** For proper `X` and a finite field `Λ` of coefficients,
both adjoints of the trace–cup pairing, into the `Λ`-linear maps to the line `Λ(-d)`, are
bijective: it is the line-valued degreewise pairing for `K = Λ_X`
(`AlgebraicGeometry.Etale.traceCupPairing_eq_untwistedDegreewisePoincarePairing`), which is
perfect (`AlgebraicGeometry.Etale.bijective_untwistedDegreewisePoincarePairing`). -/
theorem bijective_traceCupPairing [IsProper a] (hΛ : IsField Λ) (i j : ℤ)
    (hij : i + j = 2 * d) :
    Function.Bijective (traceCupPairing Λ a γ i j hij) ∧
      Function.Bijective (traceCupPairing Λ a γ i j hij).flip := by
  obtain ⟨h₁, h₂⟩ := bijective_untwistedDegreewisePoincarePairing Λ a γ
    (DerivedCategory.boundedConstructibleFiniteTor_constantComplex Λ X) isDualizable_unit hΛ i j
    hij
  rw [traceCupPairing_eq_untwistedDegreewisePoincarePairing]
  exact ⟨LinearMap.bijective_compl₁₂ _ _ _ h₁, LinearMap.bijective_flip_compl₁₂ _ _ _ h₂⟩

end Statements

section RationalPoint

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] [HasKummerClass Λ]
  [HasKummerClass.IsNormalized Λ] {X : Scheme.{u}} {k : Type u} [Field k] [IsAlgClosed k]
  [HasInvertibleExponent Λ (Spec (.of k))] (d : ℕ) (a : X ⟶ Spec (.of k))
  [SmoothOfRelativeDimension d a] (x : Spec (.of k) ⟶ X) [HasCompactification x]

/-- The *class of a `k`-point* `x` of `X` smooth of pure dimension `d`, in
`H^{2d}(X, Λ(d)) = Hom(Λ_X, Λ_X(d)[2d])`: the fundamental class
`[x ⊂ X] ∈ H^{2d}_x(X, Λ(d))` of `sk-thm-regular` (`AlgebraicGeometry.Etale.fundamentalClass`),
with supports forgotten through the counit of `Rx_! ⊣ Rx^!`,
```
       [x ⊂ X]                                 counit
Λ_X ─────────▶ Rx_! Rx^!(Λ_X(d)[2d]) ─────────▶ Λ_X(d)[2d]
```
A `k`-point of a smooth `X` is a regular immersion of codimension `d`
(`AlgebraicGeometry.isRegularImmersion_of_smoothOfRelativeDimension`), and `Spec k` is regular
(`AlgebraicGeometry.isRegularLocalRing_stalk_spec`). -/
noncomputable def rationalPointClass (hx : x ≫ a = 𝟙 _) :
    constantComplex Λ X ⟶ (tateObject Λ X d)⟦(2 * d : ℤ)⟧ :=
  haveI := HasInvertibleExponent.of_hom (Λ := Λ) a
  haveI := SmoothOfRelativeDimension.smooth d a
  haveI := isRegularImmersion_of_smoothOfRelativeDimension d a x hx
  fundamentalClass Λ d x a isRegularLocalRing_stalk_spec ≫
    (rightDerivedUpperShriekAdjunction _ x).counit.app _

/-- Blueprint `sk-cor-trace`: The trace isomorphism.

**Normalisation by the fundamental class.** For `X` proper and smooth of pure dimension `d`
over an algebraically closed field and a `k`-point `x` of `X`, the twisted trace
`tr^{(-d)}_X(d)` of the class of `x` (`AlgebraicGeometry.Etale.rationalPointClass`), read in
`H^{2d}_c(X, Λ(d))` through `Ra_* ≅ Ra_!`, is a unit of `Λ`, for every Tate orientation `γ`.

For the normalized orientation of the blueprint it is `1`; replacing `γ` by `u • γ` for a unit
`u ∈ Λˣ` multiplies it by `u⁻¹`. The normalized orientation is not yet defined in the
repository, so the normalisation itself is not stated. -/
theorem isUnit_twistedTraceMap_rationalPointClass [HasCompactification a] [IsProper a]
    (γ : TateOrientation Λ a d) (hx : x ≫ a = 𝟙 _) :
    IsUnit (twistedTraceMap Λ a γ (lowerStarClassEquivLowerShriek _ Λ a _ _
      (lowerStarClassEquiv _ Λ a (leftDerivedUpperStarConstantComplexIso Λ a) _ _
        (rationalPointClass Λ d a x hx)))) :=
  sorry

end RationalPoint

end Etale

end AlgebraicGeometry
