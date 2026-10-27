/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q14
-/
module

public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.Algebraic.Defs
public import Mathlib.RingTheory.AlgebraicIndependent.Basic
public import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
import Sheaf.RingTheory.AffineDimensionInequality

/-!
# Closed residue algebraicity over a local ring of dimension at most one

Source: Stacks Project, Varieties, Tag 0AB6, `lemma-quasi-finite-in-codim-1`,
proof of condition (2), reduced-component and vertical/horizontal paragraphs
(blueprint: lem-sfb-local-dimension-one-closed-residue-algebraicity).

Residue extensions use the canonical `Ideal.ResidueField.map`. At the maximal ideal,
its source is canonically the field `B / maximalIdeal B`: the quotient-to-residue-field
algebra map is bijective by `Ideal.bijective_algebraMap_quotient_residueField`.
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace Ideal

/-- Closed residue transcendence degree is zero under generic algebraicity.
Source: Stacks Project, Varieties, Tag 0AB6, proof of condition (2)
(blueprint: lem-sfb-local-dimension-one-closed-residue-algebraicity).

Proof plan:
1. For the chosen prime `P` over the maximal ideal, use
   `lem-weil-pbc-prime-contains-minimal-prime` (`Ideal.exists_minimalPrimes_le`)
   to choose a minimal prime `Q` below `P`. Put `q = Q.comap (algebraMap B C)`,
   `R = B / q`, `D = C / Q`, `n = maximalIdeal B / q`, and `p = P / Q`.
   Quotient prime correspondence and images of generators show that `R` is a
   Noetherian local domain, `D` is a finite type domain over `R`, and `R → D`
   is injective. The residue fields at `p` and `P` agree over `R / n = B / m`.
   The generic fraction-field extension is algebraic by the hypothesis on `Q`.
2. If `q = m`, then `R` is a field. A nonzero element `d` of `D` satisfies a
   nonzero polynomial over `R`. Remove powers of the variable from that polynomial
   to obtain a relation with nonzero constant coefficient. Solving the relation
   gives `d⁻¹` in `D`. Thus `D` is a field, `p = 0`, and its algebraic residue
   extension has transcendence degree zero (`def-kun-transcendence-degree`).
3. Otherwise the strict prime chain `q < m` and `ringKrullDim B ≤ 1` imply that
   `q` is minimal, `dim R = 1`, and `height n = 1`. Since `p` contracts to the
   nonzero ideal `n`, it is nonzero, so `height p ≥ 1`.
4. Clear denominators in generic algebraic relations to see `trdeg R D = 0`.
   Apply `lem-trf-affine-dimension-inequality`
   (`Ideal.height_add_trdeg_residueField_le`) to `R → D`, `n`, and `p`.
   It gives `height p + trdeg κ(n) κ(p) ≤ 1`; together with `height p ≥ 1`
   this forces the residue transcendence degree to vanish. Transport along the
   quotient residue-field identifications from step 1. If the closed fibre is
   empty there is no prime `P` to consider. No reducedness assumption is used.
-/
theorem trdeg_residueField_eq_zero_of_local_dim_le_one
    {B : Type u} {C : Type v} [CommRing B] [CommRing C]
    [IsNoetherianRing B] [IsLocalRing B] [Algebra B C] [Algebra.FiniteType B C]
    (hdim : ringKrullDim B ≤ 1)
    (hgeneric : ∀ (Q : Ideal C) [Q.IsPrime], Q ∈ minimalPrimes C →
      @Algebra.IsAlgebraic (Q.comap (algebraMap B C)).ResidueField Q.ResidueField _ _
        (Ideal.ResidueField.map (Q.comap (algebraMap B C)) Q (algebraMap B C) rfl).toAlgebra)
    (P : Ideal C) [P.IsPrime]
    (hP : IsLocalRing.maximalIdeal B = P.comap (algebraMap B C)) :
    @Algebra.trdeg (IsLocalRing.maximalIdeal B).ResidueField P.ResidueField _ _
      (Ideal.ResidueField.map (IsLocalRing.maximalIdeal B) P (algebraMap B C) hP).toAlgebra =
        0 := by
  sorry

end Ideal
