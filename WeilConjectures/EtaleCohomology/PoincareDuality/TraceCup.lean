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

Classes are elements of `CategoryTheory.ShiftedHom`: `H^i(X, M)` is the module of classes
`Λ_Y ⟶ (Ra_* M)[i]`, `H^i_c(X, M)` that of classes `Λ_Y ⟶ (Ra_! M)[i]`, and a class of `Λ(-d)`
is a morphism `Λ_Y ⟶ Λ_Y(-d)`. The cup product is taken on `X`, on the adjoint classes
`Λ_X ⟶ Λ_X[i]` (`AlgebraicGeometry.Etale.lowerStarClassEquiv`).

## Main definitions

- `AlgebraicGeometry.Etale.traceMap`: the trace `tr_X : H^{2d}_c(X, Λ) ⟶ Λ(-d)`.
- `AlgebraicGeometry.Etale.twistedTraceMap`: its twist `tr_X(d) : H^{2d}_c(X, Λ(d)) ⟶ Λ`.
- `AlgebraicGeometry.Etale.traceCupPairing`: the trace–cup pairing `⟨-,-⟩_i`, for proper `X`.
- `AlgebraicGeometry.Etale.rationalPointClass`: the class in `H^{2d}(X, Λ(d))` of a `k`-point.

## Main statements

- `AlgebraicGeometry.Etale.bijective_twistedTraceMap`, `AlgebraicGeometry.Etale.bijective_traceMap`
  (`sk-cor-trace`): the trace isomorphism, the second deduced from the first through
  `AlgebraicGeometry.Etale.exists_traceMap_eq`, which relates the two traces.
- `AlgebraicGeometry.Etale.traceCupPairing_eq_untwistedDegreewisePoincarePairing`: the
  trace–cup pairing is the line-valued degreewise pairing for `K = Λ_X`, and
  `AlgebraicGeometry.Etale.bijective_traceCupPairing`,
  `AlgebraicGeometry.Etale.bijective_traceCupPairing_flip`: it is perfect over a field.
- `AlgebraicGeometry.Etale.isUnit_twistedTraceMap_rationalPointClass`: the twisted trace of the
  class of a `k`-point is a unit.

## Implementation notes

The statements are for `ModuleCat Λ` with a finite coefficient ring `Λ`, the stage `A_{E,n}`
of the blueprint. The orientation `γ` is arbitrary: the repository does not yet define the
blueprint's normalized orientation, for which the twisted trace of the class of a point is `1`.
What holds for every `γ` is that this value is a unit, which is what is stated here.

TODO: once the normalized orientation of the purity chapter is defined, state the
normalisation `tr(cl(x)) = 1` for it.

The class of a `k`-point lives in ordinary cohomology, so its trace statement assumes `X`
proper. Its compactly supported version needs the composition isomorphism
`R(x ≫ a)_! ≅ Ra_! ∘ Rx_!` of the étale lower shriek, which is not yet available as a
morphism in the repository.
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

/-- Blueprint `sk-def-trace-cup`: Trace and trace–cup pairing.

The *trace* `tr^{(-d)}_X : H^{2d}_c(X, Λ) ⟶ Λ(-d)` of a Tate orientation `γ`: a class
`c : Λ_Y ⟶ (Ra_! Λ_X)[2d]` is sent to the morphism
```
          λ⁻¹                    c ⊗ᴸ 1                                  ≅
Λ_Y(d) ─────▶ Λ_Y ⊗ᴸ Λ_Y(d) ─────────▶ (Ra_! Λ_X)[2d] ⊗ᴸ Λ_Y(d) ─────▶ (Ra_! Λ_X ⊗ᴸ Λ_Y(d))[2d]
       projection map                             ≅
     ─────────────────▶ (Ra_!(Λ_X ⊗ᴸ La^* Λ_Y(d)))[2d] ─────▶ (Ra_! Λ_X(d))[2d]
            ≅                      Tr_γ
     ─────────▶ Ra_!(Λ_X(d)[2d]) ─────────▶ Λ_Y
```
through the projection map of `Ra_!`, `La^* Λ_Y(d) ≅ Λ_X(d)` and the smooth trace of `γ`, and
this morphism `Λ_Y(d) ⟶ Λ_Y` is untwisted into a class `Λ_Y ⟶ Λ_Y(-d)`
(`AlgebraicGeometry.Etale.untwistTateObject`). It is `Λ`-linear, being built from composition
and the `Λ`-linear functor `- ⊗ᴸ Λ_Y(d)`.

For `X` proper over `Y = Spec k` the source is `H^{2d}(X, Λ)`, and this is the trace of the
blueprint; it is defined for any `a` admitting a compactification. -/
noncomputable def traceMap (γ : TateOrientation Λ a d) :
    ShiftedHom (𝟙_ _) ((R(a)_![ModuleCat.{u + 1} Λ]).obj (constantComplex Λ X)) (2 * d : ℤ) →ₗ[Λ]
      (𝟙_ _ ⟶ tateObject Λ Y (-d)) :=
  untwistTateObject Λ Y d ∘ₗ Linear.leftComp Λ _ (derivedTensorLeftUnitor _ Y _).inv ∘ₗ
    Linear.rightComp Λ _
      ((((derivedTensor _ Y).flip.obj (tateObject Λ Y d)).commShiftIso (2 * d : ℤ)).hom.app _ ≫
        (((projectionMap _ a).app (constantComplex Λ X)).app (tateObject Λ Y d) ≫
          (R(a)_![ModuleCat.{u + 1} Λ]).map (((derivedTensor _ X).obj _).map
            (leftDerivedUpperStarTateObjectIso a d).hom ≫
              (derivedTensorLeftUnitor _ X _).hom))⟦(2 * d : ℤ)⟧' ≫
        ((R(a)_![ModuleCat.{u + 1} Λ]).commShiftIso (2 * d : ℤ)).inv.app _ ≫ γ.smoothTrace) ∘ₗ
      ((derivedTensor _ Y).flip.obj (tateObject Λ Y d)).mapLinearMap Λ

lemma traceMap_apply (γ : TateOrientation Λ a d)
    (c : ShiftedHom (𝟙_ _) ((R(a)_![ModuleCat.{u + 1} Λ]).obj (constantComplex Λ X))
      (2 * d : ℤ)) :
    traceMap Λ a γ c = untwistTateObject Λ Y d ((derivedTensorLeftUnitor _ Y _).inv ≫
      ((derivedTensor _ Y).flip.obj (tateObject Λ Y d)).map c ≫
        (((derivedTensor _ Y).flip.obj (tateObject Λ Y d)).commShiftIso (2 * d : ℤ)).hom.app _ ≫
          (((projectionMap _ a).app (constantComplex Λ X)).app (tateObject Λ Y d) ≫
            (R(a)_![ModuleCat.{u + 1} Λ]).map (((derivedTensor _ X).obj _).map
              (leftDerivedUpperStarTateObjectIso a d).hom ≫
                (derivedTensorLeftUnitor _ X _).hom))⟦(2 * d : ℤ)⟧' ≫
          ((R(a)_![ModuleCat.{u + 1} Λ]).commShiftIso (2 * d : ℤ)).inv.app _ ≫ γ.smoothTrace) :=
  rfl

/-- Blueprint `sk-cor-trace`: The trace isomorphism.

The *twisted trace* `tr^{(-d)}_X(d) : H^{2d}_c(X, Λ(d)) ⟶ Λ` of a Tate orientation `γ`, for a
connected `Y`: a class `Λ_Y ⟶ (Ra_!(Λ_X(d)))[2d]` composed with the smooth trace of `γ`,
```
          c                               ≅                        Tr_γ
Λ_Y ─────────▶ (Ra_!(Λ_X(d)))[2d] ─────────▶ Ra_!(Λ_X(d)[2d]) ─────────▶ Λ_Y
```
read in `Λ` through `AlgebraicGeometry.Etale.coefficientAlgEquiv`. -/
noncomputable def twistedTraceMap [ConnectedSpace Y] (γ : TateOrientation Λ a d) :
    ShiftedHom (𝟙_ _) ((R(a)_![ModuleCat.{u + 1} Λ]).obj (tateObject Λ X d)) (2 * d : ℤ) →ₗ[Λ]
      Λ :=
  (coefficientAlgEquiv Λ Y).symm.toLinearMap ∘ₗ
    Linear.rightComp Λ _
      (((R(a)_![ModuleCat.{u + 1} Λ]).commShiftIso (2 * d : ℤ)).inv.app _ ≫ γ.smoothTrace)

lemma twistedTraceMap_apply [ConnectedSpace Y] (γ : TateOrientation Λ a d)
    (c : ShiftedHom (𝟙_ _) ((R(a)_![ModuleCat.{u + 1} Λ]).obj (tateObject Λ X d)) (2 * d : ℤ)) :
    twistedTraceMap Λ a γ c = (coefficientAlgEquiv Λ Y).symm
      (c ≫ ((R(a)_![ModuleCat.{u + 1} Λ]).commShiftIso (2 * d : ℤ)).inv.app _ ≫ γ.smoothTrace) :=
  rfl

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
    ShiftedHom (𝟙_ _) ((R((a)_*[ModuleCat.{u + 1} Λ])).obj (constantComplex Λ X)) i →ₗ[Λ]
      ShiftedHom (𝟙_ _) ((R((a)_*[ModuleCat.{u + 1} Λ])).obj (constantComplex Λ X)) j →ₗ[Λ]
        (𝟙_ _ ⟶ tateObject Λ Y (-d)) :=
  ((unitCupProduct (ModuleCat.{u + 1} Λ) Λ X i j (2 * d) hij).compl₁₂
      (lowerStarClassEquiv _ Λ a (leftDerivedUpperStarConstantComplexIso Λ a) _ i).symm.toLinearMap
      (lowerStarClassEquiv _ Λ a (leftDerivedUpperStarConstantComplexIso Λ a) _ j).symm.toLinearMap
    ).compr₂ (traceMap Λ a γ ∘ₗ (lowerStarClassEquivLowerShriek _ Λ a _ _).toLinearMap ∘ₗ
      (lowerStarClassEquiv _ Λ a (leftDerivedUpperStarConstantComplexIso Λ a) _ _).toLinearMap)

set_option maxRecDepth 10000 in
lemma traceCupPairing_apply [IsProper a] (γ : TateOrientation Λ a d) (i j : ℤ)
    (hij : i + j = 2 * d)
    (x : ShiftedHom (𝟙_ _) ((R((a)_*[ModuleCat.{u + 1} Λ])).obj (constantComplex Λ X)) i)
    (y : ShiftedHom (𝟙_ _) ((R((a)_*[ModuleCat.{u + 1} Λ])).obj (constantComplex Λ X)) j) :
    traceCupPairing Λ a γ i j hij x y = traceMap Λ a γ (lowerStarClassEquivLowerShriek _ Λ a _ _
      (lowerStarClassEquiv _ Λ a (leftDerivedUpperStarConstantComplexIso Λ a) (𝟙_ _) _
        (unitCupProduct (ModuleCat.{u + 1} Λ) Λ X i j (2 * d) hij
          ((lowerStarClassEquiv _ Λ a (leftDerivedUpperStarConstantComplexIso Λ a) _ i).symm x)
          ((lowerStarClassEquiv _ Λ a (leftDerivedUpperStarConstantComplexIso Λ a) _ j).symm
            y)))) :=
  rfl

end Trace

section Statements

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] [HasTateTwist Λ] {X : Scheme.{u}}
  {k : Type u} [Field k] [IsSepClosed k] [HasInvertibleExponent Λ (Spec (.of k))]
  (a : X ⟶ Spec (.of k)) [HasCompactification a] [QuasiCompact a] {d : ℕ}
  (γ : TateOrientation Λ a d)

/-- Blueprint `sk-cor-trace`: The trace isomorphism.

**The two traces agree** (blueprint, *Degree of the pairing*). Over a separably closed field,
the trace `tr_X : H^{2d}_c(X, Λ) ⟶ Λ(-d)` is the twisted trace `tr_X(d)` read through linear
isomorphisms `f` and `e`:
```
                    f                               tr_X(d)          e
H^{2d}_c(X, Λ) ──────────▶ H^{2d}_c(X, Λ(d)) ──────────▶ Λ ──────────▶ Λ(-d)
```
-/
theorem exists_traceMap_eq :
    ∃ (f : ShiftedHom (𝟙_ _) ((R(a)_![ModuleCat.{u + 1} Λ]).obj (constantComplex Λ X))
        (2 * d : ℤ) ≃ₗ[Λ]
          ShiftedHom (𝟙_ _) ((R(a)_![ModuleCat.{u + 1} Λ]).obj (tateObject Λ X d)) (2 * d : ℤ))
      (e : Λ ≃ₗ[Λ] (𝟙_ _ ⟶ tateObject Λ (Spec (.of k)) (-d))),
      traceMap Λ a γ = e.toLinearMap ∘ₗ twistedTraceMap Λ a γ ∘ₗ f.toLinearMap :=
  -- Proof sketch: since `k` is separably closed, the Tate object `Λ(d)` on `Spec k` is
  -- trivial; choose `t : Λ ≅ Λ(d)`. By the projection formula
  -- `Ra_! Λ_X(d) ≅ Ra_! Λ_X ⊗ᴸ Λ(d)`, so `t` gives `f`, and `e` is
  -- `r ↦ untwistTateObject (r • t⁻¹)`. The two traces are then the same composite through
  -- the smooth trace of `γ`, before and after inserting the twist.
  sorry

/-- Blueprint `sk-cor-trace`: The trace isomorphism.

For `X` smooth and connected of pure dimension `d` over a separably closed field `k`, the
twisted trace `tr^{(-d)}_X(d) : H^{2d}_c(X, Λ(d)) ⟶ Λ` is an isomorphism; no properness is
needed. -/
theorem bijective_twistedTraceMap [SmoothOfRelativeDimension d a] [ConnectedSpace X] :
    Function.Bijective (twistedTraceMap Λ a γ) :=
  -- Proof sketch (SGA 4 XVIII 2.9): `H^q_c(X, M) = 0` for `q > 2d` and every sheaf `M`, so
  -- `Ra_! Λ_X(d)[2d]` has amplitude `≤ 0`, and `H^{2d}_c(X, Λ(d)) = H^0(Ra_! Ra^! Λ)` through
  -- `γ`. The twisted trace is `H^0` of the counit `Ra_! Ra^! Λ ⟶ Λ`, which is an isomorphism
  -- on `H^0` for `X` connected: by adjunction its source is `Hom(Λ_X, Λ_X) = Λ`.
  sorry

/-- Blueprint `sk-cor-trace`: The trace isomorphism.

For `X` smooth and connected of pure dimension `d` over a separably closed field `k`, the trace
`tr^{(-d)}_X : H^{2d}_c(X, Λ) ⟶ Λ(-d)` is an isomorphism; no properness is needed. -/
theorem bijective_traceMap [SmoothOfRelativeDimension d a] [ConnectedSpace X] :
    Function.Bijective (traceMap Λ a γ) := by
  obtain ⟨f, e, h⟩ := exists_traceMap_eq Λ a γ
  rw [h]
  exact e.bijective.comp ((bijective_twistedTraceMap Λ a γ).comp f.bijective)

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
the adjoint `H^i(X, Λ) → Hom(H^j(X, Λ), Λ(-d))` of the trace–cup pairing is bijective. -/
theorem bijective_traceCupPairing [IsProper a] (hΛ : IsField Λ) (i j : ℤ)
    (hij : i + j = 2 * d) :
    Function.Bijective (traceCupPairing Λ a γ i j hij) := by
  rw [traceCupPairing_eq_untwistedDegreewisePoincarePairing]
  exact LinearMap.bijective_compl₁₂_of_equiv _ _ _
    (bijective_untwistedDegreewisePoincarePairing Λ a γ
      (DerivedCategory.boundedConstructibleFiniteTor_constantComplex Λ X) isDualizable_unit hΛ i j
      hij)

/-- Blueprint `sk-def-trace-cup`: Trace and trace–cup pairing.

**The trace–cup pairing is perfect.** For proper `X` and a finite field `Λ` of coefficients,
the adjoint `H^j(X, Λ) → Hom(H^i(X, Λ), Λ(-d))` of the trace–cup pairing is bijective. -/
theorem bijective_traceCupPairing_flip [IsProper a] (hΛ : IsField Λ) (i j : ℤ)
    (hij : i + j = 2 * d) :
    Function.Bijective (traceCupPairing Λ a γ i j hij).flip := by
  rw [traceCupPairing_eq_untwistedDegreewisePoincarePairing]
  exact LinearMap.bijective_flip_compl₁₂_of_equiv _ _ _
    (bijective_untwistedDegreewisePoincarePairing_flip Λ a γ
      (DerivedCategory.boundedConstructibleFiniteTor_constantComplex Λ X) isDualizable_unit hΛ i j
      hij)

end Statements

section RationalPoint

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] [HasKummerClass Λ]
  [HasKummerClass.IsNormalized Λ] {X : Scheme.{u}} {k : Type u} [Field k] [IsSepClosed k]
  [PerfectField k] [HasInvertibleExponent Λ (Spec (.of k))] [HasInvertibleExponent Λ X] (d : ℕ)
  (a : X ⟶ Spec (.of k)) [HasCompactification a] (x : Spec (.of k) ⟶ X)

/-- The *class of a `k`-point* `x` of a smooth `X`, regularly immersed of codimension `d`, in
`H^{2d}(X, Λ(d)) = Hom(Λ_X, Λ_X(d)[2d])`: the fundamental class
`[x ⊂ X] ∈ H^{2d}_x(X, Λ(d))` of `sk-thm-regular` (`AlgebraicGeometry.Etale.fundamentalClass`),
with supports forgotten through the counit of `Rx_! ⊣ Rx^!`,
```
       [x ⊂ X]                                 counit
Λ_X ─────────▶ Rx_! Rx^!(Λ_X(d)[2d]) ─────────▶ Λ_X(d)[2d]
```
`Spec k` is regular (`AlgebraicGeometry.instIsRegularSpecOfField`). A `k`-point of `X` smooth
of relative dimension `d` is a regular immersion of codimension `d`
(`AlgebraicGeometry.isRegularImmersion_of_comp_eq_id_of_smoothOfRelativeDimension`). -/
noncomputable def rationalPointClass [Smooth a] [IsRegularImmersion d x] :
    constantComplex Λ X ⟶ (tateObject Λ X d)⟦(2 * d : ℤ)⟧ :=
  fundamentalClass Λ d x a (fun _ ↦ inferInstance) ≫
    (rightDerivedUpperShriekAdjunction _ x).counit.app _

/-- Blueprint `sk-cor-trace`: The trace isomorphism.

**Normalisation by the fundamental class.** For `X` proper and smooth of pure dimension `d`
over a separably closed field and a `k`-point `x` of `X`, the twisted trace `tr^{(-d)}_X(d)` of
the class of `x` (`AlgebraicGeometry.Etale.rationalPointClass`) is a unit of `Λ`, for every
Tate orientation `γ`. The class is read in `H^{2d}_c(X, Λ(d))` through `H(X) ≅ H` and
`H ≅ H_c`:
```
     [x]                          ≅                           ≅                            tr(d)
Λ_X ────▶ Λ_X(d)[2d]  ↦  (Λ_k ⟶ (Ra_* Λ_X(d))[2d]) ────▶ (Λ_k ⟶ (Ra_! Λ_X(d))[2d]) ────▶ Λ
```
For the normalized orientation of the blueprint it is `1`; replacing `γ` by `u • γ` for a unit
`u ∈ Λˣ` multiplies it by `u⁻¹`. The normalized orientation is not yet defined in the
repository, so the normalisation itself is not stated. -/
theorem isUnit_twistedTraceMap_rationalPointClass [SmoothOfRelativeDimension d a] [IsProper a]
    (γ : TateOrientation Λ a d) (hx : x ≫ a = 𝟙 _) :
    haveI := SmoothOfRelativeDimension.smooth d a
    haveI := isRegularImmersion_of_comp_eq_id_of_smoothOfRelativeDimension d a x hx
    IsUnit (twistedTraceMap Λ a γ (lowerStarClassEquivLowerShriek _ Λ a _ _
      (lowerStarClassEquiv _ Λ a (leftDerivedUpperStarConstantComplexIso Λ a) _ _
        (rationalPointClass Λ d a x)))) :=
  sorry

end RationalPoint

end Etale

end AlgebraicGeometry
