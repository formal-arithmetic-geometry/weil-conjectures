module

public import Sheaf.Geometry.Manifold.BundleSobolevSpace
public import Mathlib.MeasureTheory.Function.LpSpace.Basic

/-! # Integer Euclidean weak Sobolev membership and norm

Source: Demailly, Differential and pseudodifferential operators on manifolds, §2, p.3,
integer-order description after (2.1); Demailly, Complex Analytic and Differential Geometry,
VI §2, p.289 (blueprint: def-sfb-euclidean-weak-sobolev).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open MeasureTheory
open scoped ContDiff

namespace BundleSobolev

/-- Global integer weak Sobolev membership of a vector-valued representative. The underlying
L² space is Mathlib's `Lp`; membership is expressed before taking its a.e. quotient, so all
representatives are covered. Weak derivatives use the already defined scalar test identity.
Source: Demailly, Differential and pseudodifferential operators, §2, p.3, after (2.1)
(blueprint: def-sfb-euclidean-weak-sobolev). -/
def EuclideanMem {m r : ℕ} (s : ℕ) (f : Model m → Model r) : Prop :=
  MemLp f 2 volume ∧ ∀ α : Fin m → ℕ, (∑ i, α i) ≤ s → ∀ k : Fin r,
    ∃ d : Model m → ℝ, MemLp d 2 volume ∧
      IsWeakDerivative ⊤ α (fun y ↦ f y k) d

/-- The exact unweighted integer weak Sobolev norm, summing once over each multi-index
of total order at most `s`, and over the Euclidean components. Chosen scalar weak derivatives
are unique a.e. on members of the space. Outside that space this is only a total extension.
Source: Demailly, Differential and pseudodifferential operators, §2, p.3, after (2.1)
(blueprint: def-sfb-euclidean-weak-sobolev). -/
def euclideanNorm {m r : ℕ} (s : ℕ) (f : Model m → Model r) : ℝ :=
  Real.sqrt (∑ α : Fin m → Fin (s + 1),
    if (∑ i, (α i : ℕ)) ≤ s then
      ∑ k : Fin r, ∫ y, ‖weakDerivative (fun i ↦ (α i : ℕ)) (fun x ↦ f x k) y‖ ^ 2
    else 0)

end BundleSobolev
