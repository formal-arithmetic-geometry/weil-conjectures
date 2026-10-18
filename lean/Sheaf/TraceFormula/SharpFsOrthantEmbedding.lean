/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.LogRegularPair

/-!
# Lattice-intersection embedding of a sharp fs monoid

Source: ILO, Exposé VIII 3.1.17 and Remark 3.1.29, printed pp. 101 and 103
(blueprint: lem-trf-sharp-fs-orthant-embedding).
-/

set_option autoImplicit false

@[expose] public section

open Set

universe u

namespace AlgebraicGeometry

/-- A finitely generated integral saturated sharp commutative monoid embeds in an
integer lattice so that its image is exactly the lattice points in a nonnegative
orthant.  The multiplicative presentation of monoids in Lean is identified with
the additive notation of the source by the Grothendieck group construction and
`Additive` type synonym. Source: ILO, Exposé VIII 3.1.17 and Remark 3.1.29,
printed pp. 101 and 103 (blueprint: lem-trf-sharp-fs-orthant-embedding).

Proof plan: apply the sharp rational-cone lattice-intersection statement and the
integral dual-cone description to obtain finitely many integral linear forms;
their product map is injective because the forms span the rational dual, and its
nonnegative locus is precisely the original monoid. The empty family handles the
trivial monoid, so rank zero is included.
-/
theorem exists_sharp_fs_orthant_embedding (P : Type u) [CommMonoid P]
    (hP : IsFineSaturatedMonoid P)
    (hsharp : ∀ a b : P, a * b = 1 → a = 1 ∧ b = 1) :
    ∃ (r : ℕ)
      (embedding : Additive (Algebra.GrothendieckGroup P) →+ (Fin r → ℤ)),
      Function.Injective embedding ∧
        (embedding '' Set.range (fun p : P => (Algebra.GrothendieckGroup.of p))) =
          Set.range embedding ∩ Set.Ici (0 : Fin r → ℤ) := by
  sorry

end AlgebraicGeometry
