/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.PoincareDuality.Degreewise
public import WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion

/-!
# The trace map and the trace–cup pairing

For proper `X` the compactly supported and the ordinary cohomology agree, and the derived
Poincaré pairing takes the classical shape of a *trace–cup pairing*

`⟨x, y⟩_i = tr_X(x ⌣ y) : H^i(X, Λ) × H^{2d-i}(X, Λ) ⟶ Λ(-d)`,

where `tr_X : H^{2d}(X, Λ) ⟶ Λ(-d)` is the untwisted form of the counit of
`Ra_! ⊣ Ra^!` read through the orientation `γ : Λ_X(d)[2d] ≅ Ra^! Λ_s`.

Classes follow `AlgebraicGeometry.Etale.DerivedCategory.cohomologyClasses`: `H^i(X, M)` is the
module of classes `Λ_s ⟶ (Ra_* M)[i]` in `D(s_ét, Λ)`, `H^i_c(X, M)` that of classes
`Λ_s ⟶ (Ra_! M)[i]`, and a class of `Λ(-d)` is a morphism `Λ_s ⟶ Λ_s(-d)`. The cup product
is taken on `X`, on the adjoint classes `Λ_X ⟶ Λ_X[i]`, through the diagonal
`Λ_X ≅ Λ_X ⊗ᴸ Λ_X`.

## Implementation notes

The statements are for `ModuleCat Λ` with a finite coefficient ring `Λ`, the stage `A_{E,n}`
of the blueprint (see `sk-thm-transport` for the other stages). The normalisation by the
fundamental class is stated for a `k`-point with the Kummer datum
`AlgebraicGeometry.Etale.HasKummerClass` that `AlgebraicGeometry.Etale.fundamentalClass`
needs. The `Λ`-linearity of `Ra_*` is stated, not proved
(`AlgebraicGeometry.Etale.linear_rightDerivedLowerStar`); it is what makes the
identification `AlgebraicGeometry.Etale.lowerStarClassEquiv` of classes on `X` and on `s`
linear.

## Main definitions

- `AlgebraicGeometry.Etale.cupProduct`: the cup product of classes of `Λ_X`.
- `AlgebraicGeometry.Etale.lowerStarClassEquiv`: classes `Λ_X ⟶ M[i]` on `X` are classes
  `Λ_s ⟶ (Ra_* M)[i]` on `s`.
- `AlgebraicGeometry.Etale.traceMap`: the trace `tr_X : H^{2d}_c(X, Λ) ⟶ Λ(-d)`.
- `AlgebraicGeometry.Etale.twistedTraceMap`: its twist `tr_X(d) : H^{2d}_c(X, Λ(d)) ⟶ Λ`.
- `AlgebraicGeometry.Etale.traceCupPairing`: the trace–cup pairing `⟨-,-⟩_i`, for proper `X`.

## Main statements

- `AlgebraicGeometry.Etale.bijective_traceMap`: the trace isomorphism (`sk-cor-trace`).
- `AlgebraicGeometry.Etale.degreewisePoincarePairing_eq_twistedTraceMap`: the trace is the
  duality at `i = 0` for `K = Λ_X`.
- `AlgebraicGeometry.Etale.twistedTraceMap_fundamentalClass`: the twisted trace sends the class
  of a `k`-point to `1`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Opposite

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

section Cup

variable (Λ : Type (u + 1)) [CommRing Λ] [HasTateTwist Λ] (X : Scheme.{u})

/-- Blueprint `sk-def-trace-cup`: Trace and trace–cup pairing.

The *cup product* `H^i(X, Λ) × H^j(X, Λ) ⟶ H^{i+j}(X, Λ)` of classes `x : Λ_X ⟶ Λ_X[i]` and
`y : Λ_X ⟶ Λ_X[j]` in `D(X_ét, Λ)`:

`Λ_X ≅ Λ_X ⊗ᴸ Λ_X ⟶ Λ_X[i] ⊗ᴸ Λ_X[j] ≅ (Λ_X ⊗ᴸ Λ_X)[i + j] ≅ Λ_X[i + j]`,

the diagonal `Λ_X ≅ Λ_X ⊗ᴸ Λ_X` being the inverse of the left unitor, as for the cup product
with supports `AlgebraicGeometry.Etale.cupWithSupports`. By the unit law
`HasTateTwist.twistObjectAddIso_zero_left` it is the diagonal
`AlgebraicGeometry.Etale.constantComplexDiagonal` of the Kummer block, which is stated under
the stronger hypothesis `HasKummerClass`. -/
noncomputable def cupProduct (i j : ℤ) :
    DerivedCategory.cohomologyClasses (constantComplex Λ X) i →ₗ[Λ]
      DerivedCategory.cohomologyClasses (constantComplex Λ X) j →ₗ[Λ]
        DerivedCategory.cohomologyClasses (constantComplex Λ X) (i + j) :=
  LinearMap.mk₂ Λ (fun x y ↦ (derivedTensorLeftUnitor _ X _).inv ≫
      ((derivedTensor _ X).flip.obj (constantComplex Λ X)).map x ≫
        ((derivedTensor _ X).obj _).map y ≫ (derivedTensorShiftIso _ _ _ i j).hom ≫
          ((derivedTensorLeftUnitor _ X _).hom)⟦i + j⟧')
    (fun x x' y ↦ by simp only [Functor.map_add, Preadditive.add_comp, Preadditive.comp_add])
    (fun r x y ↦ by simp only [Functor.map_smul, Linear.smul_comp, Linear.comp_smul])
    (fun x y y' ↦ by simp only [Functor.map_add, Preadditive.add_comp, Preadditive.comp_add])
    (fun r x y ↦ by simp only [Functor.map_smul, Linear.smul_comp, Linear.comp_smul])

end Cup

section Classes

variable (Λ : Type (u + 1)) [CommRing Λ] {X Y : Scheme.{u}}

/-- The derived direct image `Ra_*` is `Λ`-linear. -/
instance linear_rightDerivedLowerStar (a : X ⟶ Y) :
    (R((a)_*[ModuleCat.{u + 1} Λ])).Linear Λ :=
  sorry

variable [HasTateTwist Λ]

/-- Classes on `X` are classes on `Y` of the direct image: for `a : X ⟶ Y` and
`M ∈ D(X_ét, Λ)`, the classes `Λ_X ⟶ M[n]` correspond to the classes `Λ_Y ⟶ (Ra_* M)[n]`,
through `La^* Λ_Y ≅ Λ_X`, the adjunction `La^* ⊣ Ra_*` and `Ra_*(M[n]) ≅ (Ra_* M)[n]`. For
`a : X ⟶ Spec k` this identifies `Hom(Λ_X, M[n])` with `H^n(X, M)`. -/
noncomputable def lowerStarClassEquiv (a : X ⟶ Y)
    (M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) (n : ℤ) :
    DerivedCategory.cohomologyClasses M n ≃ₗ[Λ]
      DerivedCategory.cohomologyClasses ((R((a)_*[ModuleCat.{u + 1} Λ])).obj M) n where
  toFun f := (derivedUpperStarLowerStarAdjunction _ a).homEquiv (constantComplex Λ Y) _
      ((leftDerivedUpperStarConstantComplexIso Λ a).hom ≫ f) ≫
    ((R((a)_*[ModuleCat.{u + 1} Λ])).commShiftIso n).hom.app M
  invFun g := (leftDerivedUpperStarConstantComplexIso Λ a).inv ≫
    ((derivedUpperStarLowerStarAdjunction _ a).homEquiv (constantComplex Λ Y) _).symm
      (g ≫ ((R((a)_*[ModuleCat.{u + 1} Λ])).commShiftIso n).inv.app M)
  left_inv f := by simp
  right_inv g := by simp
  map_add' f g := by
    simp only [Preadditive.comp_add, Adjunction.homEquiv_unit, Functor.map_add,
      Preadditive.add_comp]
  map_smul' r f := by
    simp only [Linear.comp_smul, Adjunction.homEquiv_unit, Functor.map_smul,
      Linear.smul_comp, RingHom.id_apply]

end Classes

section Trace

variable (Λ : Type (u + 1)) [CommRing Λ] [HasTateTwist Λ] {X Y : Scheme.{u}}

/-- The trace of a class `c ∈ H^{2d}_c(X, Λ)`, as a morphism `Λ_Y(d) ⟶ Λ_Y`:

`Λ_Y(d) ≅ Λ_Y ⊗ᴸ Λ_Y(d) ⟶ (Ra_! Λ_X)[2d] ⊗ᴸ Λ_Y(d) ≅ (Ra_! Λ_X ⊗ᴸ Λ_Y(d))[2d]
  ⟶ (Ra_!(Λ_X ⊗ᴸ La^* Λ_Y(d)))[2d] ≅ (Ra_!(Λ_X(d)))[2d] ⟶ Λ_Y`,

through the projection map of `Ra_!`, `La^* Λ_Y(d) ≅ Λ_X(d)` and the normalized smooth
trace. -/
noncomputable def traceMapTwisting (a : X ⟶ Y) [HasCompactification a] (d : ℕ)
    (γ : (twistShift Λ X d).obj (constantComplex Λ X) ≅
      dualizingComplex (ModuleCat.{u + 1} Λ) a) :
    DerivedCategory.cohomologyClasses
        ((R(a)_![ModuleCat.{u + 1} Λ]).obj (constantComplex Λ X)) (2 * d : ℤ) →ₗ[Λ]
      (tateObject Λ Y d ⟶ 𝟙_ _) where
  toFun c := (derivedTensorLeftUnitor _ _ _).inv ≫
    ((derivedTensor _ Y).flip.obj (tateObject Λ Y d)).map c ≫
      (((derivedTensor _ Y).flip.obj (tateObject Λ Y d)).commShiftIso (2 * d : ℤ)).hom.app _ ≫
        (((projectionMap _ a).app (constantComplex Λ X)).app (tateObject Λ Y d) ≫
          (R(a)_![ModuleCat.{u + 1} Λ]).map (((derivedTensor _ X).obj _).map
            (leftDerivedUpperStarTateObjectIso a d).hom))⟦(2 * d : ℤ)⟧' ≫
          shiftedSmoothTrace Λ a d γ
  map_add' c c' := by
    simp only [Functor.map_add, Preadditive.add_comp, Preadditive.comp_add]
  map_smul' r c := by
    simp only [Functor.map_smul, Linear.smul_comp, Linear.comp_smul, RingHom.id_apply]

/-- Blueprint `sk-def-trace-cup`: Trace and trace–cup pairing.

The *trace* `tr^{(-d)}_X : H^{2d}_c(X, Λ) ⟶ Λ(-d)`: a class `c : Λ_Y ⟶ (Ra_! Λ_X)[2d]` is
tensored with `Λ_Y(d)`, pushed through the projection map of `Ra_!` into
`(Ra_!(Λ_X(d)))[2d]`, sent to `Λ_Y` by the normalized smooth trace (the counit of
`Ra_! ⊣ Ra^!` read through the orientation `γ`), and the resulting `Λ_Y(d) ⟶ Λ_Y` is
untwisted into a class `Λ_Y ⟶ Λ_Y(-d)` (`AlgebraicGeometry.Etale.untwistTateObject`).

For `X` proper over `Y = Spec k` the source is `H^{2d}(X, Λ)`, and this is the trace of the
blueprint; it is defined for any `a` admitting a compactification. -/
noncomputable def traceMap (a : X ⟶ Y) [HasCompactification a] (d : ℕ)
    (γ : (twistShift Λ X d).obj (constantComplex Λ X) ≅
      dualizingComplex (ModuleCat.{u + 1} Λ) a) :
    DerivedCategory.cohomologyClasses
        ((R(a)_![ModuleCat.{u + 1} Λ]).obj (constantComplex Λ X)) (2 * d : ℤ) →ₗ[Λ]
      (𝟙_ _ ⟶ tateObject Λ Y (-d)) :=
  untwistTateObject Λ Y d ∘ₗ traceMapTwisting Λ a d γ

variable {k : Type u} [Field k]

/-- Blueprint `sk-cor-trace`: The trace isomorphism.

The *twisted trace* `tr^{(-d)}_X(d) : H^{2d}_c(X, Λ(d)) ⟶ Λ`: a class
`Λ_s ⟶ (Ra_!(Λ_X(d)))[2d]` composed with the normalized smooth trace, read in `Λ` through
`AlgebraicGeometry.Etale.coefficientRingEquiv`. -/
noncomputable def twistedTraceMap (a : X ⟶ Spec (CommRingCat.of k)) [HasCompactification a]
    (d : ℕ) (γ : (twistShift Λ X d).obj (constantComplex Λ X) ≅
      dualizingComplex (ModuleCat.{u + 1} Λ) a) :
    DerivedCategory.cohomologyClasses ((R(a)_![ModuleCat.{u + 1} Λ]).obj
        ((tateTwist Λ X d).obj (constantComplex Λ X))) (2 * d : ℤ) →ₗ[Λ] Λ :=
  coefficientLinearMap Λ k ∘ₗ Linear.rightComp Λ _ (shiftedSmoothTrace Λ a d γ)

/-- Blueprint `sk-def-trace-cup`: Trace and trace–cup pairing.

The *trace–cup pairing* of a proper `X`,

`⟨x, y⟩_i = tr^{(-d)}_X(x ⌣ y) : H^i(X, Λ) × H^j(X, Λ) ⟶ Λ(-d)`, `i + j = 2d`.

The classes `x ∈ H^i(X, Λ)`, `y ∈ H^j(X, Λ)` (classes `Λ_s ⟶ (Ra_* Λ_X)[i]`) are read on `X`
through `AlgebraicGeometry.Etale.lowerStarClassEquiv`, multiplied by
`AlgebraicGeometry.Etale.cupProduct`, and the product, read back on `s` and in `H^{2d}_c`
through `Ra_* ≅ Ra_!`, is sent to `Λ(-d)` by `AlgebraicGeometry.Etale.traceMap`. -/
noncomputable def traceCupPairing (a : X ⟶ Spec (CommRingCat.of k)) [IsProper a]
    [HasCompactification a] (d : ℕ)
    (γ : (twistShift Λ X d).obj (constantComplex Λ X) ≅
      dualizingComplex (ModuleCat.{u + 1} Λ) a) (i j : ℤ) (hij : i + j = 2 * d) :
    DerivedCategory.cohomologyClasses
        ((R((a)_*[ModuleCat.{u + 1} Λ])).obj (constantComplex Λ X)) i →ₗ[Λ]
      DerivedCategory.cohomologyClasses
          ((R((a)_*[ModuleCat.{u + 1} Λ])).obj (constantComplex Λ X)) j →ₗ[Λ]
        (𝟙_ _ ⟶ tateObject Λ (Spec (CommRingCat.of k)) (-d)) :=
  ((cupProduct Λ X i j).compl₁₂ (lowerStarClassEquiv Λ a _ i).symm.toLinearMap
      (lowerStarClassEquiv Λ a _ j).symm.toLinearMap).compr₂
    (traceMap Λ a d γ ∘ₗ lowerStarClassToLowerShriek Λ a _ _ ∘ₗ
      (lowerStarClassEquiv Λ a _ _).toLinearMap ∘ₗ
        Linear.rightComp Λ _ (eqToHom (by rw [hij])))

end Trace

section Statements

variable (Λ : Type (u + 1)) [CommRing Λ] [HasTateTwist Λ]
  {k₀ : Type u} [Field k₀] [Finite k₀] {d : ℕ} (S : PoincareDualitySetting k₀ d)
  (k : Type u) [Field k] [IsAlgClosed k] [Algebra k₀ k]

/-- Blueprint `sk-cor-trace`: The trace isomorphism.

For `X₀` in addition proper, the trace `tr^{(-d)}_X : H^{2d}(X, Λ) ⟶ Λ(-d)` is an isomorphism.
-/
theorem bijective_traceMap [Finite Λ] [HasInvertibleExponent Λ (Spec (CommRingCat.of k))]
    [IsProper (S.structureMorphism k)] [HasCompactification (S.structureMorphism k)]
    (γ : (twistShift Λ (S.geometricFiber k) d).obj (constantComplex Λ (S.geometricFiber k)) ≅
      dualizingComplex (ModuleCat.{u + 1} Λ) (S.structureMorphism k)) :
    Function.Bijective (traceMap Λ (S.structureMorphism k) d γ) :=
  sorry

/-- Blueprint `sk-cor-trace`: The trace isomorphism.

**The trace is the duality at `i = 0`.** For `X₀` proper and `K = Λ_X`, the degreewise
Poincaré pairing `⟨1, y⟩_0` of the unit class `1 ∈ H^0_c(X, Λ)` (the unit `Λ_s ⟶ Ra_* Λ_X`,
read in `H^0_c` through `Ra_* ≅ Ra_!`) with `y ∈ H^{2d}(X, Λ_X^∨(d))` is the twisted trace
`tr^{(-d)}_X(d)` of `y`, read in `H^{2d}_c(X, Λ(d))` through `Λ_X^∨ ≅ Λ_X` (the evaluation
`Λ_X ⊗ᴸ Λ_X^∨ ⟶ Λ_X`) and `Ra_* ≅ Ra_!`. -/
theorem twistedTraceMap_eq_degreewisePoincarePairing [Finite Λ]
    [HasInvertibleExponent Λ (Spec (CommRingCat.of k))]
    [IsProper (S.structureMorphism k)] [HasCompactification (S.structureMorphism k)]
    (γ : (twistShift Λ (S.geometricFiber k) d).obj (constantComplex Λ (S.geometricFiber k)) ≅
      dualizingComplex (ModuleCat.{u + 1} Λ) (S.structureMorphism k))
    (y : DerivedCategory.cohomologyClasses
      ((R((S.structureMorphism k)_*[ModuleCat.{u + 1} Λ])).obj
        ((tateTwist Λ (S.geometricFiber k) d).obj
          ((DerivedCategory.coefficientDual (ModuleCat.{u + 1} Λ) (S.geometricFiber k)).obj
            (op (constantComplex Λ (S.geometricFiber k)))))) (2 * d : ℤ)) :
    twistedTraceMap Λ (S.structureMorphism k) d γ
        (lowerStarClassToLowerShriek Λ (S.structureMorphism k) _ _
          (y ≫ ((R((S.structureMorphism k)_*[ModuleCat.{u + 1} Λ])).map
            (((derivedTensor _ _).flip.obj (tateObject Λ (S.geometricFiber k) d)).map
              ((derivedTensorLeftUnitor _ _ _).inv ≫
                coefficientEvaluation (constantComplex Λ (S.geometricFiber k)))))⟦(2 * d : ℤ)⟧')) =
      degreewisePoincarePairing Λ (S.structureMorphism k) d γ
        (constantComplex Λ (S.geometricFiber k)) 0 (2 * d) (zero_add _)
        (lowerStarClassToLowerShriek Λ (S.structureMorphism k) _ 0
          (lowerStarClassEquiv Λ (S.structureMorphism k) _ 0
            ((shiftFunctorZero _ ℤ).inv.app _))) y :=
  sorry

end Statements

section FundamentalClass

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] [HasKummerClass Λ]
  [HasKummerClass.IsNormalized Λ]
  {k₀ : Type u} [Field k₀] [Finite k₀] {d : ℕ} (S : PoincareDualitySetting k₀ d)
  (k : Type u) [Field k] [IsAlgClosed k] [Algebra k₀ k]

/-- Blueprint `sk-cor-trace`: The trace isomorphism.

**Normalisation by the fundamental class.** For `X₀` proper and a `k`-point
`x : Spec k ⟶ X`, a regular closed immersion of codimension `d`, the twisted trace
`tr^{(-d)}_X(d)` sends the class of `x` to `1`. The class of `x` is the image in
`H^{2d}(X, Λ(d))` of the fundamental class `[x ⊂ X] ∈ H^{2d}_x(X, Λ(d))` of `sk-thm-regular`
(`AlgebraicGeometry.Etale.fundamentalClass`), obtained by forgetting supports through the
counit of `Rx_! ⊣ Rx^!`, read in `H^{2d}_c(X, Λ(d))` through `Ra_* ≅ Ra_!`. The orientation
`γ` is the normalized one: this is where the blueprint's normalization of the orientation
enters, and the statement fails for an arbitrary `γ`. -/
theorem twistedTraceMap_fundamentalClass
    [HasInvertibleExponent Λ (Spec (CommRingCat.of k))]
    [HasInvertibleExponent Λ (S.geometricFiber k)]
    [IsProper (S.structureMorphism k)] [HasCompactification (S.structureMorphism k)]
    [Smooth (S.structureMorphism k)]
    (γ : (twistShift Λ (S.geometricFiber k) d).obj (constantComplex Λ (S.geometricFiber k)) ≅
      dualizingComplex (ModuleCat.{u + 1} Λ) (S.structureMorphism k))
    (x : Spec (CommRingCat.of k) ⟶ S.geometricFiber k) [IsRegularImmersion d x]
    [HasCompactification x]
    (hx : ∀ z : Spec (CommRingCat.of k),
      IsRegularLocalRing ((Spec (CommRingCat.of k)).presheaf.stalk z)) :
    twistedTraceMap Λ (S.structureMorphism k) d γ
        (lowerStarClassToLowerShriek Λ (S.structureMorphism k) _ _
          (lowerStarClassEquiv Λ (S.structureMorphism k) _ _
            (fundamentalClass Λ d x (S.structureMorphism k) hx ≫
              (rightDerivedUpperShriekAdjunction _ x).counit.app _ ≫
                ((derivedTensorLeftUnitor _ _ _).inv)⟦(2 * d : ℤ)⟧'))) = 1 :=
  sorry

end FundamentalClass

end Etale

end AlgebraicGeometry
