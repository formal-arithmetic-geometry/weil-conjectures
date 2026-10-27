/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q93
-/
module

public import Mathlib.RingTheory.MvPowerSeries.Restricted
public import Mathlib.RingTheory.MvPowerSeries.Derivative
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.LinearAlgebra.TensorProduct.Defs
import WeilConjectures.AlgebraicGeometry.ClosedImmersionConormalFlatBaseChange
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.Flat.Localization
import WeilConjectures.Mathlib.RingTheory.RegularLocalRing.Defs

/-!
# Injectivity of the continuous conormal map on affinoid residue fibres

Source: Temkin, Desingularization of quasi-excellent schemes in characteristic zero,
Proposition 3.3.2, printed pp. 20--21; Conrad, Irreducible components of rigid spaces,
section 3.3, printed pp. 509--512
(blueprint: lem-per-affinoid-residual-conormal-injective).

The map is specified by its value on every representative. The derivative is Mathlib's
termwise derivative, regarded as a restricted series by equality of underlying series.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u v

open MvPowerSeries

namespace RestrictedSeries

/-- The residue-fibre continuous conormal map of a geometrically regular affinoid quotient
exists, has the prescribed termwise derivative formula, and is injective.
Source: Temkin, Proposition 3.3.2, printed pp. 20--21; Conrad, section 3.3,
printed pp. 509--512 (blueprint: lem-per-affinoid-residual-conormal-injective).

Proof:
1. Integer norms are at most one, so termwise partial differentiation preserves coefficient
   decay. Leibniz follows from the finite Cauchy coefficient formulas. If `h` belongs to
   `n * I`, its derivative belongs to `n`, since `I ≤ n`. The same formula proves scalar
   compatibility modulo `n`, giving the displayed linear map on `I / n I`.
2. Apply lem-per-tate-maximal-residue-evaluation: the quotient field `L = A / n` is a finite
   complete isometric extension of `K`, including for inseparable extensions. With coordinate
   images `a`, evaluation of `B = L⟨x⟩` at `a` restricts to the quotient map on `A`.
   Its kernel `q` contracts to `n` and contains the extended equation ideal.
3. By lem-per-tate-finite-scalar-extension, `A → B` is flat. By
   lem-per-tate-rational-local-coordinates, `R = B_q` is regular local with maximal ideal
   `m`, residue `L`, and derivative-coordinate isomorphism `m / m² ≃ L^r`.
   The geometric regularity hypothesis makes `B / I B` regular Noetherian. Using
   lem-weil-pbc-localization-at-prime-of-quotient and def-weil-regular-scheme,
   its localization `R / J`, for `J = I R`, is regular local.
4. Apply lem-weil-pbc-closed-immersion-conormal-flat-base-change to `A → B` and `B → R`;
   the latter is flat by lem-weil-pbc-localization-flat. Tensor the resulting conormal
   isomorphisms with `L`. Balancing pure tensors (def-weil-pbc-module-tensor-product)
   identifies the result with `α : I / n I ≃ J / m J`, sending `[g]` to `[g / 1]`.
   The quotient identifications use `I² ≤ n I` and `J² ≤ m J` and preserve the original
   quotient-field action.
5. By lem-weil-pbc-regular-local-quotient-independent-generators, choose generators of `J`
   independent in `m / m²`. A relation in the kernel of `β : J / m J → m / m²`
   has all its coefficients in `m`, so represents zero. Thus `β` is injective,
   also when the generator family is empty.
6. Derivatives commute with coefficient extension; evaluation on `A` is reduction modulo
   `n`. Consequently the displayed map is `θ ∘ β ∘ α`, hence injective. For `r = 0`,
   `R = L` and `J = 0`; for `s = 0`, `I = 0`; for the zero quotient, no maximal
   ideal contains `I = A`.

The extended ideal is written as the span of the actual coefficient-extended series,
using equality in the ambient formal-series ring. Isometry preserves coefficient decay,
so for each original equation this set contains exactly its coefficient extension.
The derivative formula likewise uniquely specifies the map, since quotient classes
have representatives and the restricted-series inclusion is injective. -/
theorem affinoid_residual_conormal_injective
    (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (r s : ℕ)
    (f : Fin s → ↥(IsRestricted.subring (R := K) (1 : Fin r → ℝ)))
    (I : Ideal ↥(IsRestricted.subring (R := K) (1 : Fin r → ℝ)))
    (hI : I = Ideal.span (Set.range f))
    (hgeom : ∀ (L : Type (max u v)) [NormedField L] [IsUltrametricDist L]
      [CompleteSpace L] (φ : K →+* L), Isometry φ →
      IsRegularRing
        (↥(IsRestricted.subring (R := L) (1 : Fin r → ℝ)) ⧸
          Ideal.span {g : ↥(IsRestricted.subring (R := L) (1 : Fin r → ℝ)) |
            ∃ j : Fin s,
            g.val = MvPowerSeries.map φ (f j).val}))
    (n : Ideal ↥(IsRestricted.subring (R := K) (1 : Fin r → ℝ)))
    [n.IsMaximal] (hIn : I ≤ n) :
    ∃ d : (I ⧸ (n • ⊤ : Submodule
        ↥(IsRestricted.subring (R := K) (1 : Fin r → ℝ)) I)) →ₗ[
        ↥(IsRestricted.subring (R := K) (1 : Fin r → ℝ)) ⧸ n]
        (Fin r → ↥(IsRestricted.subring (R := K) (1 : Fin r → ℝ)) ⧸ n),
      (∀ (g : I) (i : Fin r),
        ∃ dg : ↥(IsRestricted.subring (R := K) (1 : Fin r → ℝ)),
          dg.val = MvPowerSeries.pderiv K i g.val.val ∧
          d (Submodule.Quotient.mk g) i = Ideal.Quotient.mk n dg) ∧
      Function.Injective d := by
  sorry

end RestrictedSeries
