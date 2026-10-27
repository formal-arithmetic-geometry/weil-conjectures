module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Complex.Basic

/-! # Coordinate multi-index partial derivatives

Source: Demailly, Differential and pseudodifferential operators on manifolds, §1 (1.1),
coordinate derivative convention, and Complex Analytic and Differential Geometry, VI §2.
(blueprint: def-sfb-euclidean-multi-index-partial-derivative)

This module owns the existing coordinate derivative construction, extracted without a
change to its signature or body from the Plancherel weak-derivative theorem module.
-/

@[expose] public section

set_option autoImplicit false

namespace EuclideanSpace

/-- The real multi-index partial derivative, in increasing coordinate order, with each
coordinate repeated with its prescribed multiplicity. At the zero multi-index this is `f`.
This is the coordinate multi-index notation used in smooth amplitude seminorms.
Source: Demailly, VI §2, weak derivatives preceding Sobolev lemma (2.1), printed p.289.
(blueprint: def-sfb-euclidean-multi-index-partial-derivative) -/
noncomputable def multiIndexPartialDeriv {m : ℕ} (α : Fin m → ℕ)
    (f : EuclideanSpace ℝ (Fin m) → ℂ) : EuclideanSpace ℝ (Fin m) → ℂ :=
  (List.ofFn (fun j : Fin m ↦ List.replicate (α j) j)).flatten.foldr
    (fun j g ↦ fun x ↦ fderiv ℝ g x (EuclideanSpace.single j 1)) f

end EuclideanSpace

