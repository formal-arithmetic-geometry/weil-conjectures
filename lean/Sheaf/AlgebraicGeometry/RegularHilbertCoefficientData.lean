/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q80
-/
module

public import Sheaf.AlgebraicGeometry.RegularHilbertCoefficientDatum
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

import Sheaf.AlgebraicGeometry.NonreducedRegularHilbertCoefficients

/-!
# Existence of regular Hilbert--Samuel coefficient data

Source: ILO VIII 2.3.11--2.3.13; Bierstone--Milman, Invent. Math. 128 (1997),
Theorem 9.6, (7.1)--(7.2), (9.7)--(9.14)
(blueprint: lem-trf-regular-hilbert-coefficient-data).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.HilbertCoefficient

/-- After one common étale shrinking, regular coefficients give division-adapted
formal generators and smooth coefficient loci with the block Jacobian conditions.
The diagram is chosen first; the normalization is available for each finite Q.
No algebraization of an arbitrary formal standard basis is asserted.

Source: ILO VIII 2.3.11--2.3.13; Bierstone--Milman, Invent. Math. 128 (1997),
Theorem 9.6, (7.1)--(7.2), (9.7)--(9.14)
(blueprint: lem-trf-regular-hilbert-coefficient-data).

Proof: Apply `exists_nonreduced_regularHilbertCoefficientDatum` to the same closed
immersion and structure morphism. It supplies the vertices before the choice of Q,
with `orderedVertices` and regular coefficient data for every allowed Q. Retain the
vertices and the data, forgetting the additional positive-degree and zero-ideal
conclusions. The stronger theorem uses the actual defining ideal, so it applies
in particular to reduced X and retains every field of the required datum.
-/
theorem exists_regularHilbertCoefficientDatum
    (k : Type u) [Field k] [CharZero k] (X M : Scheme.{u})
    [M.Over (Spec (CommRingCat.of k))]
    (i : X ⟶ M) [IsClosedImmersion i] [IsReduced X]
    [Smooth (M ↘ Spec (CommRingCat.of k))]
    [LocallyOfFiniteType (M ↘ Spec (CommRingCat.of k))]
    [QuasiCompact (M ↘ Spec (CommRingCat.of k))] (a : X) :
    ∃ (m n s : ℕ) (α : Fin s → Fin n →₀ ℕ), orderedVertices α ∧
      ∀ Q : ℕ, (∀ l : Fin s, (α l).degree - 1 ≤ Q) →
        Nonempty (RegularHilbertCoefficientDatum
          (M ↘ Spec (CommRingCat.of k)) i a m n s α Q) := by
  obtain ⟨m, n, s, α, hα, _, hdata⟩ :=
    exists_nonreduced_regularHilbertCoefficientDatum k X M
      (M ↘ Spec (CommRingCat.of k)) i a
  refine ⟨m, n, s, α, hα, ?_⟩
  intro Q hQ
  obtain ⟨D, _⟩ := hdata Q hQ
  exact ⟨D⟩

end AlgebraicGeometry.HilbertCoefficient
