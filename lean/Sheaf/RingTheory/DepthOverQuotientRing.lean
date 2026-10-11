/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
import Sheaf.RingTheory.Depth
import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
import Mathlib.RingTheory.LocalRing.RingHom.Basic
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.RingTheory.Finiteness.Basic

/-!
# Depth over a quotient ring

Source: Stacks Project, Algebra, Lemma Tag 0AUK (lemma-depth-goes-down-finite),
applied to the finite ring map `R → R ⧸ I`
(blueprint: lem-weil-pbc-depth-over-quotient-ring).
-/

universe u v

namespace IsLocalRing

/-- Let `R` be a Noetherian local ring, `I ≤ maximalIdeal R` an ideal and `M` a finite
`R`-module with `I M = 0` (`Module.IsTorsionBySet R M I`). Then `R ⧸ I` is local (as
`I ≠ ⊤`), `M` is a finite `R ⧸ I`-module by Mathlib's `Module.IsTorsionBySet.module`,
`(r mod I) • m = r • m`, and the depth of `M` over `R ⧸ I` equals its depth over `R`;
in particular (for `M = R ⧸ I`) the depth of the local ring `R ⧸ I` equals the depth of
`R ⧸ I` as an `R`-module (blueprint: lem-weil-pbc-depth-over-quotient-ring).

Proof (Stacks Tag 0AUK for the finite ring map `R → R ⧸ I`, whose only maximal ideal is
`m ⧸ I`): the maximal ideal of `R ⧸ I` is the image of `m`, so `(m ⧸ I) M = m M` and the
clause `I M = M` of the depth definition holds over one ring iff over the other. For
`f₁, …, f_r ∈ m` with images `f̄ᵢ ∈ m ⧸ I`, multiplication by `fᵢ` and by `f̄ᵢ` on each
`M ⧸ (f₁, …, f_{i-1}) M` is the same map, so `f₁, …, f_r` is `M`-regular over `R` iff
`f̄₁, …, f̄_r` is `M`-regular over `R ⧸ I`; every sequence in `m ⧸ I` lifts to `m`. Hence
the sets of lengths of regular sequences agree and the two depths are equal. -/
theorem depth_over_quotient_ring
    (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (I : Ideal R) (hI : I ≤ maximalIdeal R)
    (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M]
    (hIM : Module.IsTorsionBySet R M (I : Set R)) :
    letI : Nontrivial (R ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr
      (ne_top_of_le_ne_top (maximalIdeal.isMaximal R).ne_top hI)
    letI : IsLocalRing (R ⧸ I) :=
      IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
    letI : Module (R ⧸ I) M := hIM.module
    haveI : Module.Finite (R ⧸ I) M := Module.Finite.of_restrictScalars_finite R (R ⧸ I) M
    depth (R := R ⧸ I) M = depth (R := R) M ∧
      depth (R := R ⧸ I) (R ⧸ I) = depth (R := R) (R ⧸ I) := by
  sorry

end IsLocalRing
