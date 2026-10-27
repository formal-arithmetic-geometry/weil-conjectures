/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E9
-/
module

public import Sheaf.Paper.PurityDiagonalSectionPastingData

/-! # The affine chart equation of diagonal section pasting

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/
sk-prop-sp-composition/thm-pur-composition-coherence.proof.md, Step 1.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace WeilConjectures.PurityFiniteSetting.DiagonalPasting

/-- The ordered affine difference-coordinate equation on a single chart triple.
This assertion has neither the global equation nor an open naturality clause.
Source: composition coherence Step 1, diagonal section pasting proof Steps 8--12
(blueprint: lem-pur-diagonal-affine-chart-equation).

Proof: affineGeometry constructs the Cartesian block square for q, and nu
is its inverse beta restriction followed by zero-section pullback of sigma.
Affine difference tower factorization supplies the translated etale maps G,
H, J and F = H followed by J, with the Cartesian square defining R. Apply
etale Cartesian tower tensor comparison to q, P_e, G and H. Its final
identity compares sigma_(a,b) followed by E_F with pullback of sigma_(q,P_e),
whose two inputs are H-pullback of inverse beta_(q,G) followed by E_H, and
a-pullback of E_G. Pull this identity along t and precompose with gamma_f
tensor gamma_g. Difference coordinate section identifications identify the
first input with the specified c1 of ChartEquation, the second with c2, and
the output with c3. The identities Ft = z_(d+e) and Gs = z_e, together with
the derived pullback compositor, turn the middle arrow into nu. Naturality
of the tensor pullback comparison gives exactly the two composites in
ChartEquation. The comparisons E agree with etaleSection by the uniqueness
of their counit normalization. The translated coordinate and concatenation
formulas work with empty affine schemes and either empty coordinate block.
No global equality, localization argument, or Tate trivialization is used. -/
theorem diagonalSectionPastingChart (P : PurityFiniteSetting.{u}) {X Y Z : Scheme.{u}}
    (d e : ℕ) (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsAffine X] [IsAffine Y] [IsAffine Z]
    [IsNoetherian X] [IsNoetherian Y] [IsNoetherian Z]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    [SmoothOfRelativeDimension d f] [SmoothOfRelativeDimension e g]
    (aZ : Z ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aZ] [QuasiCompact aZ]
    (x : X ⟶ A d Y) (y : Y ⟶ A e Z) [Etale x] [Etale y]
    (hx : x ≫ pr d Y = f) (hy : y ≫ pr e Z = g) :
    letI := P.comparedExponent (𝟙 (Spec (.of P.field.k)))
    ChartEquation P.Coefficient P d e f g aZ x y hx hy := by sorry

end WeilConjectures.PurityFiniteSetting.DiagonalPasting
