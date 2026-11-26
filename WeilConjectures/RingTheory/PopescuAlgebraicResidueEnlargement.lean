/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.PopescuAdmissibleSubalgebra
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.Algebraic.Defs

import WeilConjectures.RingTheory.PopescuSeparableResidueRealization
import Mathlib.FieldTheory.Separable
import Mathlib.Algebra.CharP.Algebra


/-!
# Geometric residue-power capture in an Artinian local algebra

In the algebraic case of the Popescu enlargement, a `p`-power of a residue class is captured by an
admissible Artinian local subalgebra with finite separable residue extension.

## Implementation details

The separable part `F₀(α^Q) / F₀` lifts to a finite étale `A₀`-algebra `D`, which is Artinian
local; henselian étale retraction gives a map `D → B` compatible with the residue embedding,
which is flat by the closed-fibre criterion and hence injective. Its image is the admissible
subalgebra.

## References

* [Stacks, Tag 07FH]
* [Stacks, Tag 07FI] (algebraic case)
-/

@[expose] public section
set_option autoImplicit false
universe u v
namespace Algebra

private theorem exists_separable_power
    {F : Type*} {K : Type*} [Field F] [Field K] [Algebra F K]
    (p : ℕ) [CharP F p] (hp : 0 < p) (α : K) (hα : IsAlgebraic F α) :
    ∃ Q : ℕ, 1 ≤ Q ∧ IsSeparable F (α ^ Q) := by
  obtain ⟨n, g, hg, heq⟩ :=
    Polynomial.exists_separable_of_irreducible p (minpoly.irreducible hα.isIntegral) hp.ne'
  refine ⟨p ^ n, one_le_pow₀ hp, ?_⟩
  apply hg.of_dvd
  apply minpoly.dvd
  have h := congrArg (Polynomial.aeval α) heq
  simpa only [Polynomial.expand_aeval, minpoly.aeval] using h

/-- The algebraic branch of geometric enlargement, before lifting an inverse: if the unit `x` has
residue algebraic over the residue field of `A₀`, then some power `x^Q` with `Q ≥ 1` has the same
residue as an element of an admissible subalgebra `A ⊇ A₀` whose residue field is formally étale
over that of `A₀`. -/
theorem exists_popescu_algebraic_residue_enlargement
    (k : Type u) (B : Type v) [Field k] [CommRing B] [Algebra k B]
    [IsArtinianRing B] [IsLocalRing B]
    (p : ℕ) [CharP k p] (hp : 0 < p)
    (A₀ : Subalgebra k B) [IsLocalRing A₀]
    (hA₀ : A₀.IsPopescuAdmissible (IsLocalRing.maximalIdeal B))
    (x : B) (hx : IsUnit x)
    [IsLocalHom A₀.val]
    [Algebra (IsLocalRing.ResidueField A₀) (IsLocalRing.ResidueField B)]
    [IsScalarTower k (IsLocalRing.ResidueField A₀) (IsLocalRing.ResidueField B)]
    (hmap : ∀ a₀ : A₀, algebraMap (IsLocalRing.ResidueField A₀)
      (IsLocalRing.ResidueField B) (IsLocalRing.residue A₀ a₀) =
        IsLocalRing.residue B (a₀ : B))
    (hα : IsAlgebraic (IsLocalRing.ResidueField A₀) (IsLocalRing.residue B x)) :
    ∃ (A : Subalgebra k B) (_ : IsLocalRing A), ∃ hle : A₀ ≤ A,
      A.IsPopescuAdmissible (IsLocalRing.maximalIdeal B) ∧
      ∃ (Q : ℕ) (_ : 1 ≤ Q) (a : A),
        IsLocalRing.residue B (a : B) = IsLocalRing.residue B (x ^ Q) ∧
        ∃ (alg : Algebra (IsLocalRing.ResidueField A₀) (IsLocalRing.ResidueField A)),
          letI := alg
          IsScalarTower k (IsLocalRing.ResidueField A₀) (IsLocalRing.ResidueField A) ∧
          (∀ a₀ : A₀, algebraMap (IsLocalRing.ResidueField A₀)
            (IsLocalRing.ResidueField A) (IsLocalRing.residue A₀ a₀) =
              IsLocalRing.residue A (Subalgebra.inclusion hle a₀)) ∧
          Algebra.FormallyEtale (IsLocalRing.ResidueField A₀)
            (IsLocalRing.ResidueField A) := by
  have _ := hx
  have : CharP (IsLocalRing.ResidueField A₀) p :=
    charP_of_injective_algebraMap (algebraMap k (IsLocalRing.ResidueField A₀)).injective p
  obtain ⟨Q, hQ, hsep⟩ := exists_separable_power p hp (IsLocalRing.residue B x) hα
  obtain ⟨A, hlocal, hle, hA, a, ha, alg, htower, hres, hetale⟩ :=
    exists_popescu_separable_residue_realization k B A₀ hA₀ hmap
      (IsLocalRing.residue B x ^ Q) hsep
  refine ⟨A, hlocal, hle, hA, Q, hQ, a, ?_, alg, htower, hres, hetale⟩
  simpa only [map_pow] using ha

end Algebra
