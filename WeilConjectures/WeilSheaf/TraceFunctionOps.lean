/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.Fourier
public import WeilConjectures.WeilSheaf.Stalk

/-!
# Trace functions of Weil complexes under the operations

The trace function `t_K` of a Weil complex (`AlgebraicGeometry.WeilComplex.traceFunction`) is
compatible with the elementary operations: a shift `[a]` multiplies it by `(-1)ᵃ`, a pullback
`φ^*` composes it with `φ` on rational points, it is invariant under the Galois action on the
coefficient field of the rational points.

## Main statements

- `AlgebraicGeometry.WeilComplex.traceFunction_shift`: `t_{K[a]} = (-1)ᵃ t_K`.
- `AlgebraicGeometry.WeilComplex.traceFunction_upperStar`: `t_{φ^* K}(x) = t_K(φ(x))`.
- `AlgebraicGeometry.WeilComplex.traceFunction_fieldPointsCongr`: `t_K(σ(x)) = t_K(x)` for a
  `k₀`-automorphism `σ` of the coefficient field.

## Blueprint

These are the properties of the trace function (blueprint `def-fd-trace-function`,
`def-weil-local-frobenius-trace`) used in the proof of the Fourier trace formula
(sketch blueprint `sk-thm-fourier-trace-formula`).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
variable {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [Y.Over (Spec (CommRingCat.of k₀))]

omit [Finite k₀] in
/-- The image `φ(x) = x ≫ φ` of a rational point under a morphism of `k₀`-schemes. -/
noncomputable def Scheme.Hom.mapFieldPoints (φ : X ⟶ Y) [φ.IsOver (Spec (CommRingCat.of k₀))]
    (K : Type u) [Field K] [Algebra k₀ K]
    (x : (X ↘ Spec (CommRingCat.of k₀)).fieldPoints K) :
    (Y ↘ Spec (CommRingCat.of k₀)).fieldPoints K :=
  ⟨x.1 ≫ φ, by rw [Category.assoc, CategoryTheory.comp_over, x.2]⟩

omit [Finite k₀] in
@[simp]
lemma Scheme.Hom.mapFieldPoints_coe (φ : X ⟶ Y) [φ.IsOver (Spec (CommRingCat.of k₀))]
    (K : Type u) [Field K] [Algebra k₀ K]
    (x : (X ↘ Spec (CommRingCat.of k₀)).fieldPoints K) :
    (φ.mapFieldPoints K x).1 = x.1 ≫ φ :=
  rfl

namespace WeilComplex

/-- A shift `[a]` multiplies the trace function by `(-1)ᵃ`. -/
theorem traceFunction_shift (K : WeilComplex k₀ l X) (a : ℤ) (n : ℕ)
    (x : (X ↘ Spec (CommRingCat.of k₀)).fieldPoints (FiniteField.galoisExtension k₀ n)) :
    ((shiftFunctor (WeilComplex k₀ l X) a).obj K).traceFunction n x =
      (a.negOnePow : ℤ) • K.traceFunction n x :=
  sorry

/-- The trace function of a pullback is the composite with the morphism on rational points:
`t_{φ^* K}(x) = t_K(φ(x))`. -/
theorem traceFunction_upperStar (φ : X ⟶ Y) [φ.IsOver (Spec (CommRingCat.of k₀))]
    (K : WeilComplex k₀ l Y) (n : ℕ)
    (x : (X ↘ Spec (CommRingCat.of k₀)).fieldPoints (FiniteField.galoisExtension k₀ n)) :
    ((upperStar φ).obj K).traceFunction n x = K.traceFunction n (φ.mapFieldPoints _ x) :=
  sorry

/-- The trace function is invariant under `k₀`-automorphisms of the coefficient field of the
rational points: `t_K(σ(x)) = t_K(x)`, the local Frobenius operators at the geometric points
over `x` and `σ(x)` being conjugate. -/
theorem traceFunction_fieldPointsCongr (K : WeilComplex k₀ l X) (n : ℕ)
    (σ : FiniteField.galoisExtension k₀ n ≃ₐ[k₀] FiniteField.galoisExtension k₀ n)
    (x : (X ↘ Spec (CommRingCat.of k₀)).fieldPoints (FiniteField.galoisExtension k₀ n)) :
    K.traceFunction n ((X ↘ Spec (CommRingCat.of k₀)).fieldPointsCongr σ x) =
      K.traceFunction n x :=
  sorry

end WeilComplex

end AlgebraicGeometry
