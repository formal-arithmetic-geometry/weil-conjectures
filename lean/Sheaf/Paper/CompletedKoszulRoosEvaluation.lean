/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A2
-/
module

public import Sheaf.Paper.IntrinsicCompletionCompleted
public import Sheaf.Paper.SequentialDerivedInverseLimitCompleted
import Sheaf.RingTheory.NoetherianKoszulAugmentationProZero
import Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients
import Sheaf.Paper.CompletedConstantSheafReduction

/-! # Evaluation-compatible Koszul reconstruction in the completed coefficient universe

Source: blueprint order 1248, and order 1249, proof steps 2--3; Stacks 099M and 091Z.
(blueprint: lem-weil-pbc-completed-koszul-roos-evaluation).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe t
open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

variable (T : Scheme.{t}) {A : Type (t + 1)} [CommRing A]
variable (d : ProEtaleAdicCoefficientDatum A)

/-- The explicit Koszul fibre is any Roos limit of the strict quotient tower, compatibly
with its unit and every finite evaluation, before assuming the input complete.

Source: blueprint order 1248, and order 1249, proof steps 2--3; Stacks 099M and 091Z.
(blueprint: lem-weil-pbc-completed-koszul-roos-evaluation).

Proof: compute the Koszul and quotient towers on M.complex. The Noetherian Koszul
augmentation to A/I^(m+1) has pro-zero cone, even though its degree-zero Koszul
homology is A/(f_i^(m+1)). Exact constant sheafification, flat scalar extension to
A_T and derived tensor by M.complex preserve the zero cone transition maps. The
strict-tower derived-limit theorem inverts that augmentation. Exact countable products
identify the derived limit of the Koszul tensor tower with the explicit Koszul fibre.
The augmentation preserves degree-zero units. Compare
this computation with the given Roos triangle by a morphism of distinguished triangles
which is the identity on the two product vertices; its remaining component is invertible.
Its product square gives the asserted evaluation identities. The universal K-flat scalar
comparison and the normalized extension/restriction adjunction identify the evaluation
of the quotient unit with the displayed derived adjunction unit. Transport from the
representative through M.realization. This also treats the empty generator family and
zero quotient rings; no completeness assumption is needed for the comparison itself. -/
theorem completedKoszulRoosEvaluation {K : adicDatumDerived T d}
    (M : AdicDatumModel T d K) (r : ℕ) (f : Fin r → A)
    (hf : Ideal.span (Set.range f) = d.ideal)
    (L : CompletedSequentialDerivedLimit T d (adicDatumModelTower T d M)) :
    ∃ e : completedIntrinsicCompletion T d r f M.complex ≅ L.obj,
      ∀ n : ℕ,
        completedIntrinsicCompletionMap T d r f M.complex M.realization ≫
            e.hom ≫ L.p ≫
            Pi.π (fun a : ℕ ↦ (adicDatumModelTower T d M).obj (op a)) n ≫
            (adicDatumModelRestriction T d M n).hom ≫
            (adicDatumRestriction T (adicDatumProjection T d n)).map
              (adicDatumModelReductionIso T d M n).inv =
          (adicDatumAdjunction T (adicDatumProjection T d n)).unit.app K := by
  sorry

end AlgebraicGeometry.Scheme
