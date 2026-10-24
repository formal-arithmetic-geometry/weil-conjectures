/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.CoefficientMorphismBasic
public import WeilConjectures.TraceFormula.FibreModel
public import WeilConjectures.TraceFormula.RelativeFrobeniusIterate

/-!

# The trace formula along a morphism with proper fibres

Let `f : X ⟶ Y` be the base change of a morphism of models over a finite field, commuting with
the model Frobenii. The pushforward `ψ' = Rf_! ψ ∘ θ_f` of a Frobenius coefficient morphism `ψ`
(`ProEtale.CondensedRing.lowerShriekFrobeniusCoefficient`) has the same global operator
(`ProEtale.CondensedRing.frobeniusCompactOperator_lowerShriekFrobeniusCoefficient`), and its stalk
map at a fixed point `y` is the global operator of the restriction of `ψ` to the fibre
(`ProEtale.CondensedRing.stalk_lowerShriekFrobeniusCoefficient_iterate`). Hence the trace formula
on `Y` and on the fibres gives the trace formula on `X` (blueprint
`thm-trf-coefficient-morphism-trace-formula`, Step 4, with `lem-trf-weil-shriek-operator-fibres`).
The trace formula on the fibres, which are proper in the application, is taken as a hypothesis
for all proper models.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

attribute [local instance] boundedConstructibleBraiding

variable {ℓ : ℕ} [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]
  {X Y : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]

/-- **The trace formula along a morphism with proper fibres** (blueprint
`thm-trf-coefficient-morphism-trace-formula`, Step 4, with
`lem-trf-weil-shriek-operator-fibres`): let `f : X ⟶ Y` be the base change of a morphism
`f₀ : X₀ ⟶ Y₀` of models over the finite field `k₀`, commuting with the model Frobenii, whose
fibres over the rational points of `Y` fixed by `Φ_Y` are proper. If the trace formula in degree
one holds on `Y` and for all model Frobenii of proper schemes, it holds on `X`. -/
theorem traceFormulaHolds_of_isProper_pullback [IsAlgClosed k] {k₀ : Type u} [Field k₀]
    [Finite k₀] [Algebra k₀ k] {X₀ Y₀ : Scheme.{u}} {fX₀ : X₀ ⟶ Spec (.of k₀)}
    {fY₀ : Y₀ ⟶ Spec (.of k₀)} [LocallyOfFiniteType fX₀] [LocallyOfFiniteType fY₀]
    {pX : X.left ⟶ X₀} {pY : Y.left ⟶ Y₀} {ΦX : X ⟶ X} {ΦY : Y ⟶ Y}
    (hX : IsModelFrobenius ΦX fX₀ pX) (hY : IsModelFrobenius ΦY fY₀ pY) [IsProper ΦX.left]
    [IsProper ΦY.left] {f : X ⟶ Y} (hf : ΦX ≫ f = f ≫ ΦY) {f₀ : X₀ ⟶ Y₀}
    (hfp : f.left ≫ pY = pX ≫ f₀) (h₀ : f₀ ≫ fY₀ = fX₀)
    (hfib : ∀ y : RationalPoint Y, y ≫ ΦY = y → IsProper (pullback f y).hom)
    (hproper : ∀ (Z : Over (Spec (.of k))) [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom]
      [IsSeparated Z.hom] [IsProper Z.hom] (ΦZ : Z ⟶ Z) [IsProper ΦZ.left] (k' : Type u)
      [Field k'] [Finite k'] [Algebra k' k] (Z₀ : Scheme.{u}) (g₀ : Z₀ ⟶ Spec (.of k'))
      [LocallyOfFiniteType g₀] (pZ : Z.left ⟶ Z₀), IsModelFrobenius ΦZ g₀ pZ →
        TraceFormulaHolds ℓ ΦZ)
    (hYtf : TraceFormulaHolds ℓ ΦY) : TraceFormulaHolds ℓ ΦX :=
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
