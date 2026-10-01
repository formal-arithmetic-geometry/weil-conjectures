/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.Category
public import WeilConjectures.ZetaLinearAlgebra.FrobeniusModule
public import WeilConjectures.ZetaSeries

/-!
# Stalks, trace functions and weights of Weil sheaves

The geometric stalk of a Weil sheaf at a closed point with its local Frobenius, the trace
function, and the weight conditions phrased on them: punctual purity, upper weight bounds and
reality. The stalk, the support, the trace function and the reality condition are still
placeholders with `sorry` bodies; see `WeilConjectures.WeilSheaf.Defs`.

## Main declarations

- `AlgebraicGeometry.WeilSheaf.stalk`: the geometric stalk with its local Frobenius.
- `AlgebraicGeometry.WeilSheaf.IsPunctuallyPureOfWeight`,
  `AlgebraicGeometry.WeilSheaf.HasWeightsAtMost` and `AlgebraicGeometry.WeilSheaf.IsReal`: the
  weight conditions and the reality condition.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]

namespace WeilSheaf

-- TODO(unify): sk-d-real-weil
/-- The support of a Weil sheaf: the set of points with nonzero stalk. -/
def support (F : WeilSheaf k₀ l X) : Set X := sorry

-- TODO(unify): sk-d-real-weil
/-- The geometric stalk of `F` at a closed point `x`, with its local geometric Frobenius
`Fₓ`, which acts on the stalk at a geometric point above `x`. -/
noncomputable def stalk (F : WeilSheaf k₀ l X) (x : X) :
    FrobeniusModule.{u + 1, 0} (PadicAlgCl l) := sorry

-- TODO(unify): sk-def-trace
/-- The trace function `t_{F,n}` of a Weil sheaf: the trace of the Frobenius relative to
`𝔽_{qⁿ}` on the stalk at an `𝔽_{qⁿ}`-rational point. -/
noncomputable def traceFunction (F : WeilSheaf k₀ l X) (n : ℕ)
    (x : (X ↘ Spec (CommRingCat.of k₀)).fieldPoints (FiniteField.galoisExtension k₀ n)) :
    PadicAlgCl l := sorry

/-- `F` is punctually `ι`-pure of weight `w`: at every closed point `x`, every eigenvalue `α`
of the local Frobenius `Fₓ` satisfies `|ι α| = q_x ^ (w / 2)`, with `q_x` the residue
cardinality at `x`. -/
def IsPunctuallyPureOfWeight (ι : PadicAlgCl l →+* ℂ) (F : WeilSheaf k₀ l X) (w : ℝ) : Prop :=
  ∀ x : X, IsClosed ({x} : Set X) →
    (F.stalk x).IsPureOfWeight ι ((X ↘ Spec (CommRingCat.of k₀)).residueCard x) w

/-- `F` has weights at most `w`: at every closed point `x`, every eigenvalue `α` of the local
Frobenius `Fₓ` satisfies `|ι α| ≤ q_x ^ (w / 2)`. -/
def HasWeightsAtMost (ι : PadicAlgCl l →+* ℂ) (F : WeilSheaf k₀ l X) (w : ℝ) : Prop :=
  ∀ x : X, IsClosed ({x} : Set X) →
    (F.stalk x).HasWeightsAtMost ι ((X ↘ Spec (CommRingCat.of k₀)).residueCard x) w

/-- A punctually pure sheaf has weights at most its weight. -/
theorem IsPunctuallyPureOfWeight.hasWeightsAtMost {ι : PadicAlgCl l →+* ℂ}
    {F : WeilSheaf k₀ l X} {w : ℝ} (h : F.IsPunctuallyPureOfWeight ι w) :
    F.HasWeightsAtMost ι w :=
  fun x hx ↦ (h x hx).hasWeightsAtMost

-- TODO(unify): sk-d-real-weights
/-- `F` is `ι`-*real* if the realization under `ι` of the local Frobenius characteristic
polynomial `P_x(F, T) = det(1 - T Fₓ | F_x̄)` has real coefficients at every closed point `x`;
equivalently, if every complex local eigenvalue multiset is stable under complex conjugation.
Placeholder; see `WeilConjectures.WeilSheaf.Defs`. -/
def IsReal (ι : PadicAlgCl l →+* ℂ) (F : WeilSheaf k₀ l X) : Prop := sorry

end WeilSheaf

end AlgebraicGeometry
