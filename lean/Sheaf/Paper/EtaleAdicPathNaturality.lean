/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T2
-/
module

public import Sheaf.Paper.EtaleAdicPathData

/-!
# Compatibility of normalized etale adic paths

Source: Weil II (1.1.1), (1.1.6); Stacks 0BND (2).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
open FiniteEtale

variable {Y : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
  {y z : Spec (.of Ω) ⟶ Y}
variable (l : ℕ) [Fact l.Prime]
  [IsNoetherian Y] [Y.IsSeparated] [∀ x : Y, Invertible (l : Y.residueField x)]
  (Q : Type (u + 1)) [Field Q] [Algebra ℚ_[l] Q] [IsAlgClosure ℚ_[l] Q]

/-- Normalized path transport is natural for every algebraic-coefficient morphism.
Source: Weil II (1.1.1) b)-d), (1.1.6); Stacks 0BND (2)
(blueprint: new-t2-etale-adic-path-naturality).
Proof: at a finite level, represent each stalk element by a finite-cover germ.
A sheaf morphism maps its section on that same cover, so the two composites agree
by the germ formula. Equality after every limit projection gives integral
naturality. Rational morphisms are represented by integral maps divided by a
power of the uniformizer; linearity gives naturality after this division.
At algebraic coefficients choose a common finite coefficient extension for the
morphism, apply rational naturality there, and extend scalars. The balanced tensor
comparison for the common extension commutes with paths on pure tensors, by the
finite-level scalar comparison followed by limit projections. Thus the equation
descends through the coefficient localization to the recorded object fibres.
This also covers the zero morphism and rank-zero objects. -/
theorem etaleAlgebraicPath_naturality
    {F H : LisseAlgebraicSheaf l Y Q} (f : F ⟶ H) (τ : fiber y ≅ fiber z) :
    (etaleAlgebraicPathIso l Q F τ).hom ≫ etaleAlgebraicFiberMap l Q z f =
      etaleAlgebraicFiberMap l Q y f ≫ (etaleAlgebraicPathIso l Q H τ).hom := by sorry

end AlgebraicGeometry.Scheme
