/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G1
-/
import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Defs
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Algebra.Ring.Subring.Defs
import Mathlib.Algebra.CharP.Defs

/-!
# Existence of a coefficient subring

Source: Stacks Project, Algebra, Theorem 032A(1) and Definition 0326
(blueprint: lem-weil-pbc-cohen-coefficient-ring-exists).
-/

universe u

namespace IsLocalRing

/-- A complete local ring contains a coefficient subring, in the sense of Stacks Project,
Algebra, Definition 0326; existence is Theorem 032A(1).
(blueprint: lem-weil-pbc-cohen-coefficient-ring-exists)

Proof: (1) For n ≥ 2 the kernel of R/m^n → R/m^(n-1) is square-zero. In residue
characteristic zero the quotients are Q-algebras; in characteristic p > 0, R/m^n is a
Z/p^n-algebra. (2) In characteristic zero, lift the identity of the residue field successively
through these square-zero kernels using formal smoothness over Q
(lem-weil-pbc-char-zero-field-extension-formally-smooth and def-weil-pbc-formally-smooth-adic).
(3) Pass to the inverse limit using def-weil-pbc-adic-completion and
def-weil-pbc-adically-complete-ring. The resulting section has image a field with zero
intersection with m, and its reduction is an isomorphism.
(4) In positive characteristic choose a Cohen ring with the prescribed residue field
(lem-weil-pbc-cohen-rings-exist). Lift its maps modulo p^n successively using
lem-weil-pbc-cohen-ring-mod-pn-formally-smooth. (5) Completeness of R gives a map from
this Cohen ring to R, whose inverse image of m is its ideal (p).
(6) By lem-weil-pbc-dvr-unit-times-uniformizer-power, its kernel is either zero or (p^N)
for N ≥ 1. (7) Its image is local with maximal ideal its intersection with m, equal to
(p), and the induced residue map is bijective. If the kernel is zero, completeness transfers
from the Cohen ring; otherwise powers of (p) eventually vanish, so the inverse system of
quotients stabilizes. This verifies all three coefficient-ring conditions. -/
theorem exists_coefficient_subring (R : Type u) [CommRing R] [IsLocalRing R]
    [IsAdicComplete (maximalIdeal R) R] (p : ℕ) [CharP (ResidueField R) p] :
    ∃ (Λ : Subring R) (hΛ : IsLocalRing Λ),
      letI : IsLocalRing Λ := hΛ
      maximalIdeal Λ = (maximalIdeal R).comap Λ.subtype ∧
      IsAdicComplete ((maximalIdeal R).comap Λ.subtype) Λ ∧
      Function.Bijective
        (Ideal.quotientMap (I := (maximalIdeal R).comap Λ.subtype)
          (maximalIdeal R) Λ.subtype le_rfl) ∧
      (maximalIdeal R).comap Λ.subtype = Ideal.span {(p : Λ)} := by
  sorry

end IsLocalRing
