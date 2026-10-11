/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P1
-/
import Sheaf.AlgebraicGeometry.NagataAffineFpDescent

/-!
# Affine finite-presentation descent

Source: the Weil conjectures blueprint, `sec-nagata-compactification`,
`sk-prop-nagata-sketch-approximation`, node order 352
(blueprint: lemma-nagata-affine-fp-descends).
-/

universe v

namespace AlgebraicGeometry

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

/-- For the chosen finite-stage descent data, the stage algebra is finitely presented over
its stage ring and the comparison map to the presented colimit algebra is an isomorphism.
First, the finite quotient presentation of `E.stageAlgebra` gives finite presentation over
`F.obj E.stage`. Second, tensoring with the colimit carries each transported relation to the
corresponding relation in `relations`, identifying the tensor quotient with `E.algebra`'s
presentation. Third, under that identification `E.beta` is the identity on polynomial
generators, so the generator-preserving map in the reverse direction is a two-sided inverse
(blueprint: lemma-nagata-affine-fp-descends). -/
theorem nagata_affine_fp_descends {I : Type v} [Preorder I]
    [IsDirected I (· ≤ ·)] (F : I ⥤ CommRingCat.{v}) (lambda0 : I)
    (n m : ℕ) (relations : Fin m → MvPolynomial (Fin n) (↑(colimit F)))
    (E : NagataAffineFpDescent F lambda0 n m relations) :
    Algebra.FinitePresentation (F.obj E.stage) E.stageAlgebra ∧
      ∃ e : (↑(colimit F) ⊗[F.obj E.stage] E.stageAlgebra) ≃ₐ[↑(colimit F)] E.algebra,
        e.toAlgHom = E.beta := by
  sorry

end AlgebraicGeometry
