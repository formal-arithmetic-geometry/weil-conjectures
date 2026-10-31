/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.PurityDiagonalSectionPastingData

/-! # The global equation of diagonal section pasting

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/
sk-prop-sp-composition/thm-pur-composition-coherence.proof.md, Step 1.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace WeilConjectures.PurityFiniteSetting.DiagonalPasting

/-- The global diagonal-pasting equation, independently of open locality and charts.
Source: composition coherence Step 1, diagonal section pasting proof Steps 1--5
(blueprint: lem-pur-diagonal-global-equation).

Proof: form Q = X times_Z Y and W = X times_Z X. The two Cartesian squares
exhibit a and b as the base changes of f and g, and ba is the first projection
of W. Smooth exceptional tensor pasting at the coefficient unit gives
D l^*(sigma_(f,g)) = sigma_(a,b) (A tensor a^*B), where A, B and D are the
specified smooth dualizing base-change maps. Pull this equality along the
composite diagonal t. Double diagonal section identifications give alpha_f
as gamma_f followed by inverse t^*A, f^*alpha_g as gamma_g followed by inverse
s^*B, and alpha_(fg) as inverse t^*D, with the canonical section comparators.
Precompose with gamma_f tensor gamma_g and cancel the invertible t^*D.
Naturality of the tensor pullback comparison and its compatibility with the
pullback compositor identify the remaining middle arrow with kappa. Applying
the comparison inverse image gives SameProEtaleMap. No open or affine chart
assertion is used. The same pullback and inverse identities hold for empty
schemes and relative dimension zero; no orientation is introduced. -/
theorem diagonalSectionPastingEquation (P : PurityFiniteSetting.{u}) {X Y Z : Scheme.{u}}
    (d e : ℕ) (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    [SmoothOfRelativeDimension d f] [SmoothOfRelativeDimension e g]
    (aZ : Z ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aZ] [QuasiCompact aZ] :
    letI := P.comparedExponent (𝟙 (Spec (.of P.field.k)))
    Equation P.Coefficient P d e f g aZ := by sorry

end WeilConjectures.PurityFiniteSetting.DiagonalPasting
