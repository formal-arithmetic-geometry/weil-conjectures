/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G1
-/
module

public import Sheaf.AlgebraicGeometry.FormalKernelGradedPieces
import Sheaf.AlgebraicGeometry.Modules.IdealTimesQuasiCoherentAffineSections

/-! # Bilinear multiplication on associated graded ideal sheaves

Source: Stacks Project, Lemma 087Z, the algebra in its statement; Schemes Lemmas
01I8 and 01IC for affine tensor products and quotients.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry

/-- Multiplication descends to successive ideal-power quotients and commutes with
restriction. No associativity, commutativity or unit law is asserted here.
Source: Stacks Project, Lemma 087Z and Schemes Lemmas 01I8, 01IC.
(blueprint: lem-weil-pbc-formal-associated-graded-multiplication).

Proof: On an affine open U, identify the power inclusions with I(U)^r and the
quotient projection with I(U)^r / I(U)^(r+1). For degree zero use the identity
inclusion of the structure sheaf. Multiply representatives. The product lies in
I(U)^(m+n); changing either representative changes it by I(U)^(m+n+1), so the
operation is well defined and bilinear. This construction commutes with restriction
between affine opens, since inclusions, projections and ring multiplication do.
For an arbitrary open, lift the two quotient sections on an affine cover. On an
affine refinement of any overlap the results agree by independence of lifts. Glue
using the sheaf condition. The same argument proves bilinearity and restriction
compatibility. For actual sections of the power ideals, their product belongs
locally to the range of the (m+n)-th power inclusion. This inclusion is monic;
hence the local lifts agree and glue to c, and the local definition of the quotient
operation gives the displayed identity. The argument includes empty opens,
the zero and unit ideals, and zero degrees. -/
theorem formalAssociatedGraded_multiplication_exists {X : Scheme.{u}}
    (I : X.IdealSheafData) :
    ∃ mu : ∀ (m n : ℕ) (U : X.Opens),
      (formalAssociatedGradedPiece I m).val.obj (op U) →ₗ[Γ(X, U)]
        (formalAssociatedGradedPiece I n).val.obj (op U) →ₗ[Γ(X, U)]
          (formalAssociatedGradedPiece I (m + n)).val.obj (op U),
      (∀ (m n : ℕ) (U V : X.Opens) (h : V ≤ U)
        (a : (formalAssociatedGradedPiece I m).val.obj (op U))
        (b : (formalAssociatedGradedPiece I n).val.obj (op U)),
        (formalAssociatedGradedPiece I (m + n)).val.map (homOfLE h).op (mu m n U a b) =
          mu m n V ((formalAssociatedGradedPiece I m).val.map (homOfLE h).op a)
            ((formalAssociatedGradedPiece I n).val.map (homOfLE h).op b)) ∧
      (∀ (m n : ℕ) (U : X.Opens)
        (a : (Scheme.idealSheafPower I.toModulesι m).1.val.obj (op U))
        (b : (Scheme.idealSheafPower I.toModulesι n).1.val.obj (op U)),
        ∃ c : (Scheme.idealSheafPower I.toModulesι (m + n)).1.val.obj (op U),
          (Scheme.idealSheafPower I.toModulesι (m + n)).2.val.app (op U) c =
            (@id Γ(X, U) ((Scheme.idealSheafPower I.toModulesι m).2.val.app (op U) a)) *
              (@id Γ(X, U) ((Scheme.idealSheafPower I.toModulesι n).2.val.app (op U) b)) ∧
          mu m n U ((formalAssociatedGradedπ I m).val.app (op U) a)
            ((formalAssociatedGradedπ I n).val.app (op U) b) =
              (formalAssociatedGradedπ I (m + n)).val.app (op U) c) := by sorry

end AlgebraicGeometry
