/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E9
-/
module

public import Sheaf.Paper.PurityDiagonalSectionPastingData

/-! # Open restrictions of diagonal section pasting

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/
sk-prop-sp-composition/thm-pur-composition-coherence.proof.md, Step 1.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace WeilConjectures.PurityFiniteSetting.DiagonalPasting

/-- The seven open naturality squares, independently of global or affine equations.
Source: composition coherence Step 1, diagonal section pasting proof Steps 6--7
(blueprint: lem-pur-diagonal-open-restriction).

Proof: factor each compatible open restriction into target-open base change
and the residual source-open immersion openFactor. The first comparison is
beta and the second is the unique counit-normalized etale restriction E.
The sigma cocycle and normalized source-etale compatibility prove naturality
of sigma for that factorization. Horizontal beta pasting and compatibility
of E with beta prove naturality of each alpha by restricting its defining
self-product square and diagonal. Apply the same beta/E calculation to the
squares defining gamma_f and gamma_g: openPair and openMiddle respect their
projections, graph and diagonal by openPairProperties and openMiddleProperties.
This gives the last two squares of OpenEquation. Tensor these squares and
use the canonical tensor pullback comparison; naturality of sigma_(a,b)
and equality transport ba = p_(fg) then give the kappa square. These are
exactly the seven squares in OpenEquation, in its order. All composites and
inverses use finite expression locality for beta, sigma and E. A source-open
square is only required to commute, never to be Cartesian. Empty opens and
zero relative dimensions are included by the same identities. -/
theorem diagonalSectionPastingOpen (P : PurityFiniteSetting.{u})
    {X Y Z X' Y' Z' : Scheme.{u}}
    (d e : ℕ) (f : X ⟶ Y) (g : Y ⟶ Z) (f' : X' ⟶ Y') (g' : Y' ⟶ Z')
    (u' : X' ⟶ X) (v : Y' ⟶ Y) (w : Z' ⟶ Z)
    [IsNoetherian X] [IsNoetherian Y] [IsNoetherian Z]
    [IsNoetherian X'] [IsNoetherian Y'] [IsNoetherian Z']
    [IsOpenImmersion u'] [IsOpenImmersion v] [IsOpenImmersion w]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    [SmoothOfRelativeDimension d f] [SmoothOfRelativeDimension e g]
    [IsSeparated f'] [LocallyOfFiniteType f'] [QuasiCompact f']
    [IsSeparated g'] [LocallyOfFiniteType g'] [QuasiCompact g']
    [SmoothOfRelativeDimension d f'] [SmoothOfRelativeDimension e g']
    (hf : u' ≫ f = f' ≫ v) (hg : v ≫ g = g' ≫ w)
    (aZ : Z ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aZ] [QuasiCompact aZ] :
    letI := P.comparedExponent (𝟙 (Spec (.of P.field.k)))
    OpenEquation P.Coefficient P d e f g f' g' u' v w hf hg aZ := by sorry

end WeilConjectures.PurityFiniteSetting.DiagonalPasting
