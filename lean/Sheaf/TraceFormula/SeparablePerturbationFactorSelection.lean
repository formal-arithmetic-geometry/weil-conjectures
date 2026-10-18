/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q142
-/
module

public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.FieldTheory.RatFunc.AsPolynomial
public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.AlgebraicIndependent.Basic
public import Sheaf.FieldTheory.AbhyankarInequality

import Mathlib.FieldTheory.AlgebraicClosure
import Sheaf.TraceFormula.ResidualCurveValueGroup

/-!
# Separable perturbation and factor selection

Source: Temkin, *Stable modification of relative curves*, Proposition 4.3.1,
proof p. 28, the separable perturbation paragraph
(blueprint: lem-trf-separable-perturbation-factor-selection).

The restricted valuation ring is `O.comap (algebraMap K (RatFunc K))`.
Its canonical residue-field embedding is the published `O.comapResidueFieldMap`.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

namespace ValuationSubring

/-- A normalized irreducible polynomial with transcendental residue can be replaced
by a normalized monic separable irreducible polynomial with transcendental residue.
Every monic separable irreducible polynomial over the separably closed base has degree one.
Source: Temkin, *Stable modification of relative curves*, Proposition 4.3.1, proof p. 28,
the separable perturbation paragraph
(blueprint: lem-trf-separable-perturbation-factor-selection).

Proof, following the node's eight steps:
1. Put `L = K(t)`, `R = O ∩ K`, `k = κ(R)`, and `l = κ(O)`. The canonical map
   `k → l` is injective, since restriction preserves the intersection of maximal ideals.
   The indeterminate is a transcendence basis of `L/K`, so `trdeg_K L = 1`.
   The given transcendental residue implies `trdeg_k l ≥ 1`. Apply
   `lem-trf-abhyankar-inequality`; its nonnegative rational-rank summand gives
   `trdeg_k l ≤ 1`, hence equality.
2. Apply `lem-trf-residual-curve-value-group` to normalize every nonzero element
   of `L` by a scalar in `Kˣ`. In particular choose `c` with `x = t/c ∈ Oˣ`.
   The same assertion will normalize every `t-a`, which is nonzero by transcendence.
3. If `R = K`, all nonzero constants are units in `O`, and `t = cx` is a unit.
   If its residue were algebraic over `K`, the residue of `f(t)/π` would be too:
   `def-weil-relative-algebraic-closure` says algebraic elements form a subfield.
   Thus `g = X`, `π' = 1` works. Henceforth assume `R ≠ K`.
4. If `f` is separable, take `g = f`, `π' = π`. Otherwise
   `lem-trf-irreducible-separable-derivative` gives `f' = 0`.
   Its positive degree cannot be one, since a monic linear polynomial has derivative one.
5. Choose `b ∈ K ∖ R`. Then `δ = b⁻¹` is a nonzero element of `m_R ⊆ m_O`.
   Put `ε = πδ/c` and `h = f + εX`. Since `deg f ≥ 2`, this is monic of the
   same degree and has constant nonzero derivative `ε`, hence is separable by Bezout.
   Also `h(t)/π = f(t)/π + δx`, so it is a unit with the same transcendental residue.
   This choice does not require `t ∈ O`.
6. Apply `lem-trf-separable-polynomial-linear-factorization` to write
   `h = ∏ (X-a_i)`, with a nonempty finite factor list. Normalize each `t-a_i`
   by `c_i ∈ Kˣ`, obtaining units `v_i`. With `C = ∏ c_i`, evaluation gives
   `h(t)/π = (C/π) ∏ v_i`. Both sides and all the `v_i` are units, so
   `C/π ∈ K ∩ Oˣ = Rˣ`. Reduction expresses the given residue as a product
   of the residues of `v_i` times an element of `kˣ`.
7. If every residue of `v_i` were algebraic over `k`, their product would be too,
   again using `def-weil-relative-algebraic-closure`, a contradiction. Choose a
   transcendental factor; `g = X-a_i`, `π' = c_i` works. A linear polynomial is
   monic and irreducible by degrees, and separable because its derivative is one.
8. For any monic separable irreducible polynomial `q`, separable splitting gives
   a nonempty product of linear factors. Two or more factors contradict irreducibility,
   so there is exactly one and `q.degree = 1`. This also handles step 4's output. -/
theorem exists_separable_irreducible_transcendental_residue
    {K : Type u} [Field K] [IsSepClosed K]
    (O : ValuationSubring (RatFunc K)) (f : Polynomial K)
    (hf_monic : f.Monic) (hf_irreducible : Irreducible f)
    (π : Kˣ) (v : Oˣ)
    (hv : ((v : O) : RatFunc K) =
      Polynomial.eval₂ (algebraMap K (RatFunc K)) RatFunc.X f /
        algebraMap K (RatFunc K) (π : K))
    (htrans : @Transcendental
      (IsLocalRing.ResidueField (O.comap (algebraMap K (RatFunc K))))
      (IsLocalRing.ResidueField O) _ _
      (O.comapResidueFieldMap (algebraMap K (RatFunc K))).toAlgebra
      (IsLocalRing.residue O (v : O))) :
    (∃ (g : Polynomial K) (π' : Kˣ) (w : Oˣ),
      g.Monic ∧ g.Separable ∧ Irreducible g ∧
      ((w : O) : RatFunc K) =
        Polynomial.eval₂ (algebraMap K (RatFunc K)) RatFunc.X g /
          algebraMap K (RatFunc K) (π' : K) ∧
      @Transcendental
        (IsLocalRing.ResidueField (O.comap (algebraMap K (RatFunc K))))
        (IsLocalRing.ResidueField O) _ _
        (O.comapResidueFieldMap (algebraMap K (RatFunc K))).toAlgebra
        (IsLocalRing.residue O (w : O))) ∧
    (∀ g : Polynomial K, g.Monic → g.Separable → Irreducible g → g.degree = 1) := by
  sorry

end ValuationSubring
